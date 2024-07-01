//
// Created by CSHwang on 2024/2/3.
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
static FILE *output_file;
static const char *model_path;
static const char *output_path;

int32_t verbosity;
static const char *usage =
    "usage: btoreliminate [ <option> ... ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -h                      print this command line option summary\n"
    "  --model <model>         load model from <model> in 'BTOR' format\n"
    "  --output <output>       write eliminated model to <output>\n";

static Btor2Parser *model;

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

static void eliminate_constraint() {
  int64_t number_of_lines = btor2parser_max_id(model);
  std::vector<bool> eliminate(number_of_lines + 1, 0);

  int64_t eliminated_cons = 0, total_cons = 0;
  int64_t eliminated_state = 0, eliminated_node = 0, total_state = 0;
  for (int64_t i = 1; i <= number_of_lines; ++i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    if (line->tag == BTOR2_TAG_constraint) ++total_cons;
    if (line->symbol && line->tag != BTOR2_TAG_input) ++total_state;
    if (classification(line) == BTOR2_TAG_state) eliminate[i] = 1;
  }
  transition(model, eliminate);
  for (int64_t i = 1; i <= number_of_lines; ++i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    if (line->tag != BTOR2_TAG_constraint)
      eliminate[i] = 0;
  }
  for (int64_t i = number_of_lines; i > 0; --i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    Btor2Tag type = classification(line);
    if (type == BTOR2_TAG_constraint || type == BTOR2_TAG_eq) {
      for (int64_t j = 0; j < line->nargs; ++j) {
        int64_t args_id = labs(line->args[j]);
        eliminate[args_id] = eliminate[i] || eliminate[args_id];
      }
    }
  }
  for (int64_t i = 1; i <= number_of_lines; ++i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    if (classification(line) != BTOR2_TAG_state)
      eliminate[i] = 0;
  }

  transition(model, eliminate);
  for (int64_t i = 1; i <= number_of_lines; ++i)
    if (eliminate[i]) {
      Btor2Line *line = btor2parser_get_line_by_id(model, i);
      line->lineno = -1;

      ++eliminated_node;
      if (line->tag == BTOR2_TAG_constraint) ++eliminated_cons;
      if (line->symbol && line->tag != BTOR2_TAG_input) ++eliminated_state;
    }
  printf("eliminated state: %" PRId64 "/%" PRId64 "\n", eliminated_state, total_state);
  printf("eliminated node: %" PRId64 "/%" PRId64 "\n", eliminated_node, number_of_lines);
  printf("eliminated constraints: %" PRId64 "/%" PRId64 "\n", eliminated_cons, total_cons);
}

int main(int argc, char const *argv[]) {
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "-h")) {
      fputs(usage, stdout);
      exit(1);
    } else if (!strcmp(argv[i], "--model")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'btoreliminate' error: argument to '--model' missing\n");
        exit(1);
      }
      model_path = argv[i];
    } else if (!strcmp(argv[i], "--output")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'btoreliminate' error: argument to '--output' missing\n");
        exit(1);
      }
      output_path = argv[i];
    } else {
      fprintf(stderr, "*** 'btoreliminate' error: invalid command line option '%s'", argv[i]);
      exit(1);
    }
  }
  open("btoreliminate", model_path, model_file, "<stdin>", stdin, 1);
  open("btoreliminate", output_path, output_file, "<stdout>", stdout, 0);

  parse_model();
  eliminate_constraint();

  int64_t number_of_lines = btor2parser_max_id(model);
  for (int i = 1; i <= number_of_lines; ++i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    if (line->lineno != -1) print_line("btoreliminate", output_file, line);
  }
  btor2parser_delete(model);

  return 0;
}