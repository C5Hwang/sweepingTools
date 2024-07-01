//
// Created by CSHwang on 2024/1/29.
//

#include <cctype>
#include <cstdio>
#include <climits>
#include <cstdlib>
#include <cstring>
#include <cinttypes>

#include <cassert>
#include <vector>

#include "btorfunc.h"
#include "btorsim/btorsimhelpers.h"
#include "btor2parser/btor2parser.h"

/*------------------------------------------------------------------------*/

static FILE *model_file;
static FILE *expand_file;
static const char *model_path;
static const char *expand_path;

int32_t verbosity;
static const char *usage =
    "usage: btorexpand [ <option> ... ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -h                      print this command line option summary\n"
    "  -v                      increase verbosity level (multiple times if necessary)\n"
    "  -e <n>                  expand <n> layers (default 20)\n"
    "\n"
    "  --model <btor>          load model from <btor> in 'BTOR' format\n"
    "  --output <expand>       write result to <expand>\n"
    "\n"
    "and '<btor>' is sequential model in 'BTOR' format\n"
    "and '<expand>' is combinational model with <n>-layer in 'BTOR' format.\n";

static Btor2Parser *model;
static int expand_layers = 20;

static std::vector<Btor2Line *> inputs;
static std::vector<Btor2Line *> states;
static std::vector<Btor2Line *> bads;
static std::vector<Btor2Line *> constraints;
static std::vector<Btor2Line *> justices;

static int64_t num_format_lines;
static std::vector<Btor2Line *> inits;
static std::vector<Btor2Line *> nexts;

static std::vector<int64_t> reached_bads;

static int64_t num_unreached_bads;

/*------------------------------------------------------------------------*/

static int32_t parse_int(const char *str, int32_t *res_ptr) {
  const char *p = str;
  if (!*p) return 0;
  if (*p == '0' && p[1]) return 0;
  int32_t res = 0;
  while (*p) {
    const int32_t ch = *p++;
    if (!isdigit(ch)) return 0;
    if (INT_MAX / 10 < res) return 0;
    res *= 10;
    const int32_t digit = ch - '0';
    if (INT_MAX - digit < res) return 0;
    res += digit;
  }
  *res_ptr = res;
  return 1;
}

static void parse_model_line(Btor2Line *l) {
  switch (l->tag) {
    case BTOR2_TAG_bad: {
      int64_t i = (int64_t) bads.size();
      msg(2, "bad %" PRId64 " at line %" PRId64, i, l->lineno);
      bads.push_back(l);
      reached_bads.push_back(-1);
      num_unreached_bads++;
    }
      break;

    case BTOR2_TAG_constraint: {
      int64_t i = (int64_t) constraints.size();
      msg(2, "constraint %" PRId64 " at line %" PRId64, i, l->lineno);
      constraints.push_back(l);
    }
      break;

    case BTOR2_TAG_init:inits[l->args[0]] = l;
      break;

    case BTOR2_TAG_input: {
      int64_t i = (int64_t) inputs.size();
      if (l->symbol)
        msg(2,
            "input %" PRId64 " '%s' at line %" PRId64,
            i,
            l->symbol,
            l->lineno);
      else
        msg(2, "input %" PRId64 " at line %" PRId64, i, l->lineno);
      inputs.push_back(l);
    }
      break;

    case BTOR2_TAG_next:nexts[l->args[0]] = l;
      break;

    case BTOR2_TAG_sort: {
      switch (l->sort.tag) {
        case BTOR2_TAG_SORT_bitvec:
          msg(2,
              "sort bitvec %u at line %" PRId64,
              l->sort.bitvec.width,
              l->lineno);
          break;
        case BTOR2_TAG_SORT_array:
          msg(2,
              "sort array %u %u at line %" PRId64,
              l->sort.array.index,
              l->sort.array.element,
              l->lineno);
          break;
        default:
          die("parse error in '%s' at line %" PRId64 ": unsupported sort '%s'",
              model_path,
              l->lineno,
              l->sort.name);
          break;
      }
    }
      break;

    case BTOR2_TAG_state: {
      int64_t i = (int64_t) states.size();
      if (l->symbol) {
        msg(2,
            "state %" PRId64 " '%s' at line %" PRId64,
            i,
            l->symbol,
            l->lineno);
      } else {
        msg(2, "state %" PRId64 " at line %" PRId64, i, l->lineno);
      }
      states.push_back(l);
    }
      break;

    case BTOR2_TAG_add:
    case BTOR2_TAG_and:
    case BTOR2_TAG_concat:
    case BTOR2_TAG_const:
    case BTOR2_TAG_constd:
    case BTOR2_TAG_consth:
    case BTOR2_TAG_dec:
    case BTOR2_TAG_eq:
    case BTOR2_TAG_implies:
    case BTOR2_TAG_inc:
    case BTOR2_TAG_ite:
    case BTOR2_TAG_mul:
    case BTOR2_TAG_nand:
    case BTOR2_TAG_neg:
    case BTOR2_TAG_neq:
    case BTOR2_TAG_nor:
    case BTOR2_TAG_not:
    case BTOR2_TAG_one:
    case BTOR2_TAG_ones:
    case BTOR2_TAG_or:
    case BTOR2_TAG_output:
    case BTOR2_TAG_redand:
    case BTOR2_TAG_redor:
    case BTOR2_TAG_redxor:
    case BTOR2_TAG_sdiv:
    case BTOR2_TAG_sext:
    case BTOR2_TAG_sgt:
    case BTOR2_TAG_sgte:
    case BTOR2_TAG_slice:
    case BTOR2_TAG_sll:
    case BTOR2_TAG_slt:
    case BTOR2_TAG_slte:
    case BTOR2_TAG_sra:
    case BTOR2_TAG_srem:
    case BTOR2_TAG_srl:
    case BTOR2_TAG_sub:
    case BTOR2_TAG_udiv:
    case BTOR2_TAG_uext:
    case BTOR2_TAG_ugt:
    case BTOR2_TAG_ugte:
    case BTOR2_TAG_ult:
    case BTOR2_TAG_ulte:
    case BTOR2_TAG_urem:
    case BTOR2_TAG_xnor:
    case BTOR2_TAG_xor:
    case BTOR2_TAG_zero:
    case BTOR2_TAG_read:
    case BTOR2_TAG_write:break;

    case BTOR2_TAG_fair:
    case BTOR2_TAG_justice:
    case BTOR2_TAG_rol:
    case BTOR2_TAG_ror:
    case BTOR2_TAG_saddo:
    case BTOR2_TAG_sdivo:
    case BTOR2_TAG_smod:
    case BTOR2_TAG_smulo:
    case BTOR2_TAG_ssubo:
    case BTOR2_TAG_uaddo:
    case BTOR2_TAG_umulo:
    case BTOR2_TAG_usubo:
    default:
      die("parse error in '%s' at line %" PRId64 ": unsupported '%" PRId64
          " %s%s'",
          model_path,
          l->lineno,
          l->id,
          l->name,
          l->nargs ? " ..." : "");
      break;
  }
}

static void parse_model() {
  assert (model_file);
  model = btor2parser_new();
  if (!btor2parser_read_lines(model, model_file))
    die("parse error in '%s' at %s", model_path, btor2parser_error(model));
  num_format_lines = btor2parser_max_id(model);
  inits.resize(num_format_lines, nullptr);
  nexts.resize(num_format_lines, nullptr);
  Btor2LineIterator it = btor2parser_iter_init(model);
  Btor2Line *line;
  while ((line = btor2parser_iter_next(&it))) parse_model_line(line);

  for (size_t i = 0; i < states.size(); i++) {
    Btor2Line *state = states[i];
    if (!nexts[state->id]) {
      msg(1, "state %d without next function", state->id);
    }
  }
}

/*------------------------------------------------------------------------*/

static int64_t get_lineno(int64_t idx) {
  int64_t f = idx < 0 ? -1 : 1;
  return f * btor2parser_get_line_by_id(model, idx)->lineno;
}

static void parse_line(Btor2Line *line, int64_t &line_id, int time, bool first_timestamp, bool show_property) {
  auto default_setting = [&]() {
    ++line_id;
    fprintf(expand_file, "%" PRId64 " %s", line_id, line->name);
    if (line->sort.id) {
      int64_t sort_lid = get_lineno(line->sort.id);
      fprintf(expand_file, " %" PRId64 "", sort_lid);
    }
    if (line->constant) fprintf(expand_file, " %s", line->constant);
    for (uint32_t i = 0, n = line->nargs; i < n; ++i)
      fprintf(expand_file, " %" PRId64 "", get_lineno(line->args[i]));
    if (line->tag == BTOR2_TAG_sext || line->tag == BTOR2_TAG_uext)
      fprintf(expand_file, " %" PRId64, line->args[1]);
//    fprintf(expand_file, " id_%" PRId64 ".time_%d", line->id, time); // debug
    fprintf(expand_file, "\n");

    line->lineno = line_id;
  };
  auto add_state = [&](Btor2Line *state, int64_t val_id) {
    int64_t sort_lid = get_lineno(state->sort.id),
        zero_lid = btor2parser_get_line_by_id(model, state->sort.id)->init;

    auto print_symbol = [&]() {
      if (state->symbol)
        fprintf(expand_file, " %s.state.id_%" PRId64 ".time_%d\n", state->symbol, state->id, time);
      else
        fprintf(expand_file, " state.id_%" PRId64 ".time_%d\n", state->id, time);
    };

    if (val_id != 0) {
      ++line_id;
      fprintf(expand_file, "%" PRId64 " add %" PRId64 "", line_id, sort_lid);
      fprintf(expand_file, " %" PRId64 " %" PRId64 "", zero_lid, val_id);
      print_symbol();
      state->lineno = line_id;
    } else {
      ++line_id;
      fprintf(expand_file, "%" PRId64 " input %" PRId64 "", line_id, sort_lid);
      print_symbol();
      state->lineno = line_id;
    }
  };

  switch (line->tag) {
    case BTOR2_TAG_sort: {
      if (first_timestamp) {
        ++line_id;
        fprintf(expand_file, "%" PRId64 " sort", line_id);
        if (line->sort.tag == BTOR2_TAG_SORT_array) {
          int64_t index_lid = get_lineno(line->sort.array.index),
              element_lid = get_lineno(line->sort.array.element);
          fprintf(expand_file, " array %" PRId64 " %" PRId64 "\n", index_lid, element_lid);
        } else
          fprintf(expand_file, " bitvec %" PRIu32 "\n", line->sort.bitvec.width);

        line->lineno = line_id;
        line->init = ++line_id;
        fprintf(expand_file, "%" PRId64 " zero %" PRId64 "\n", line->init, line->lineno);
      }
    }
      break;

    case BTOR2_TAG_state: {
      if (first_timestamp) {
        if (line->init > 0) add_state(line, get_lineno(line->init));
        else add_state(line, 0);
      } else if (line->next > 0) add_state(line, line->init);
      else add_state(line, 0);
    }
      break;

    case BTOR2_TAG_input: {
      ++line_id;
      int64_t sort_lid = get_lineno(line->sort.id);
      fprintf(expand_file, "%" PRId64 " input %" PRId64 "", line_id, sort_lid);
      if (line->symbol)
        fprintf(expand_file, " %s.input.id_%" PRId64 ".time_%d\n", line->symbol, line->id, time);
      else
        fprintf(expand_file, " input.id_%" PRId64 ".time_%d\n", line->id, time);

      line->lineno = line_id;
    }
      break;

    case BTOR2_TAG_slice: {
      ++line_id;
      int64_t sort_lid = get_lineno(line->sort.id);
      fprintf(expand_file, "%" PRId64 " slice %" PRId64 "", line_id, sort_lid);
      fprintf(expand_file, " %" PRId64 " %" PRId64 " %" PRId64 "\n",
              get_lineno(line->args[0]), line->args[1], line->args[2]);
      line->lineno = line_id;
    }
      break;

//    case BTOR2_TAG_sext:
//    case BTOR2_TAG_uext: {
//      fprintf(stderr, "expand error in '%s' at line %" PRId64 ": unsupported '%s'\n",
//              model_path, line->lineno, line->name);
//      exit(1);
//    }
//      break;

    case BTOR2_TAG_init: {
//      if (first_timestamp) default_setting();
//      else {
//        int64_t state_id = line->args[0];
//        Btor2Line *state = btor2parser_get_line_by_id(model, state_id);
//        if (state->next == 0) default_setting();
//      }

//      int64_t state_id = line->args[0];
//      Btor2Line *state = btor2parser_get_line_by_id(model, state_id);
//      if (first_timestamp || state->next == 0) add_state(state, line->args[1]);
    }
      break;
    case BTOR2_TAG_next:break;

    case BTOR2_TAG_bad:
    case BTOR2_TAG_justice:
    case BTOR2_TAG_constraint: {
      if (show_property) default_setting();
    }
      break;

    case BTOR2_TAG_const:
    case BTOR2_TAG_constd:
    case BTOR2_TAG_consth:
    case BTOR2_TAG_one:
    case BTOR2_TAG_ones:
    case BTOR2_TAG_zero: {
      if (first_timestamp) default_setting();
    }
      break;

    default:default_setting();
      break;
  }
}

int main(int argc, char const *argv[]) {
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "-h")) {
      fputs(usage, stdout);
      exit(1);
    } else if (!strcmp(argv[i], "-v")) {
      ++verbosity;
    } else if (!strcmp(argv[i], "-e")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'btorexpand' error: argument to '-e' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &expand_layers)) {
        fprintf(stderr, "*** 'btorexpand' error: invalid number in '-e %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "--model")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'btorexpand' error: argument to '--model' missing\n");
        exit(1);
      }
      model_path = argv[i];
    } else if (!strcmp(argv[i], "--output")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'btorexpand' error: argument to '--output' missing\n");
        exit(1);
      }
      expand_path = argv[i];
    } else {
      fprintf(stderr, "*** 'btorexpand' error: invalid command line option '%s'", argv[i]);
      exit(1);
    }
  }
  open("btorexpand", model_path, model_file, "<stdin>", stdin, 1);
  open("btorexpand", expand_path, expand_file, "<stdout>", stdout, 0);

  parse_model();

//  auto print_info = [](Btor2Line *line) {
//    fprintf(stderr, "------------------\n");
//    fprintf(stderr, "id: %" PRId64 "\n", line->id);
//    fprintf(stderr, "lineno: %" PRId64 "\n", line->lineno);
//    fprintf(stderr, "name: %s\n", line->name);
//    fprintf(stderr, "sort.id: %" PRId64 "\n", line->sort.id);
//    fprintf(stderr, "sort.name: %s\n", line->sort.name);
//    fprintf(stderr, "init: %" PRId64 "\n", line->init);
//    fprintf(stderr, "next: %" PRId64 "\n", line->next);
//    fprintf(stderr, "constant: %s\n", line->constant);
//    fprintf(stderr, "symbol: %s\n", line->symbol);
//    fprintf(stderr, "nargs: %" PRIu32 "\n", line->nargs);
//    fprintf(stderr, "args: \n");
//    for (uint32_t j = 0; j < line->nargs; ++j) {
//      fprintf(stderr, "  [%" PRIu32 "] %" PRId64 "\n", j, line->args[j]);
//    }
//  };
//  for (int64_t i = 1, n = btor2parser_max_id(model); i <= n; ++i) {
//    Btor2Line *tmp = btor2parser_get_line_by_id(model, i);
//    print_info(tmp);
//  }

  int64_t number_of_lines = btor2parser_max_id(model), line_id = 0;
  for (int timestamp = 0; timestamp <= expand_layers; ++timestamp) {
    fprintf(expand_file, ";\n; timestamp %d\n;\n", timestamp);
    for (int64_t i = 1; i <= number_of_lines; ++i)
      parse_line(btor2parser_get_line_by_id(model, i), line_id,
                 timestamp, timestamp == 0, 1);

    for (int64_t i = 1; i <= number_of_lines; ++i) {
      Btor2Line *line = btor2parser_get_line_by_id(model, i);
      if (line->tag == BTOR2_TAG_state && line->next != 0) line->init = get_lineno(line->next);
    }
  }
  btor2parser_delete(model);

  return 0;
}