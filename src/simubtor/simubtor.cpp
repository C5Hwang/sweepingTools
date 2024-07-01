//
// Created by CSHwang on 2024/2/4.
//

#include <cstdio>
#include <climits>
#include <cstdlib>
#include <cstring>
#include <cinttypes>

#include <map>
#include <set>
#include <vector>
#include <cassert>
#include <algorithm>

#include "btorfunc.h"
#include "btorsim/btorsimstate.h"
#include "btorsim/btorsimhelpers.h"
#include "btor2parser/btor2parser.h"

/*------------------------------------------------------------------------*/

static FILE *log_file;
static FILE *model_file;
static FILE *output_file;
static const char *log_path;
static const char *model_path;
static const char *output_path;

int32_t verbosity;
static const char *usage =
    "usage: simubtor [ <option> ... ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -s <s>                  random seed (default 0)\n"
    "  -h <s>                  random hash seed (default 0)\n"
    "  -c <c>                  set check capacity (default 4)\n"
    "  -r <n>                  generate <n> random transitions (default 10000)\n"
    "\n"
    "  --help                  print this command line option summary\n"
    "  --states                print state's bitvec to log\n"
    "  --hash                  print state's hash value to log\n"
    "  --check-all             check all node's equivalence(default 'state only')\n"
    "\n"
    "  --model <model>         load model from <model> in 'BTOR' format\n"
    "  --output <output>       write result to <output>\n"
    "  --log <log>             write log to <log>\n";

static Btor2Parser *model;

static std::vector<Btor2Line *> inputs;
static std::vector<Btor2Line *> states;
static std::vector<Btor2Line *> bads;
static std::vector<Btor2Line *> constraints;

static int64_t num_format_lines;
static std::vector<Btor2Line *> inits;
static std::vector<Btor2Line *> nexts;

static std::vector<int64_t> reached_bads;

static int64_t constraints_violated = -1;
static int64_t num_unreached_bads;

static bool all_hash = false;
static bool print_hash = false;
static bool print_states = false;
static std::vector<BtorSimState> current_state;

static BtorSimRNG rng, base_rng;
static std::vector<BtorSimBitVector *> fixed_input;
static std::vector<std::pair<uint64_t, uint64_t>> hash_value;
static std::vector<std::pair<Btor2Line *, std::pair<int, int>>> parse_states;

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

static void update_current_state(int64_t id, BtorSimBitVector *bv) {
  assert (0 <= id), assert (id < num_format_lines);
  msg(5, "updating state %" PRId64, id);
  current_state[id].update(bv);
}

static void update_current_state(int64_t id, BtorSimArrayModel *am) {
  assert (0 <= id), assert (id < num_format_lines);
  msg(5, "updating state %" PRId64, id);
  current_state[id].update(am);
}

static void update_current_state(int64_t id, BtorSimState &s) {
  assert (0 <= id), assert (id < num_format_lines);
  msg(5, "updating state %" PRId64, id);
  current_state[id].update(s);
}

static void delete_current_state(int64_t id) {
  assert (0 <= id), assert (id < num_format_lines);
  if (current_state[id].type) current_state[id].remove();
}

static BtorSimState simulate(int64_t id) {
  int32_t sign = id < 0 ? -1 : 1;
  if (sign < 0) id = -id;
  assert (0 <= id), assert (id < num_format_lines);
  BtorSimState res = current_state[id];
  if (!res.is_set()) {
    Btor2Line *l = btor2parser_get_line_by_id(model, id);
    if (!l) die("internal error: unexpected empty ID %" PRId64, id);
    BtorSimState args[3];
    for (uint32_t i = 0; i < l->nargs; i++) args[i] = simulate(l->args[i]);
    switch (l->tag) {
      case BTOR2_TAG_add:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_add(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_and:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_and(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_concat:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_concat(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_const:assert (l->nargs == 0);
        assert (res.type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_char_to_bv(l->constant);
        break;
      case BTOR2_TAG_constd:assert (l->nargs == 0);
        assert (res.type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_constd(l->constant, l->sort.bitvec.width);
        break;
      case BTOR2_TAG_consth:assert (l->nargs == 0);
        assert (res.type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_consth(l->constant, l->sort.bitvec.width);
        break;
      case BTOR2_TAG_dec:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_dec(args[0].bv_state);
        break;
      case BTOR2_TAG_eq:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        if (args[0].type == BtorSimState::Type::ARRAY) {
          assert (args[1].type == BtorSimState::Type::ARRAY);
          res.bv_state =
              btorsim_am_eq(args[0].array_state, args[1].array_state);
        } else {
          assert (args[0].type == BtorSimState::Type::BITVEC);
          assert (args[1].type == BtorSimState::Type::BITVEC);
          res.bv_state = btorsim_bv_eq(args[0].bv_state, args[1].bv_state);
        }
        break;
      case BTOR2_TAG_implies:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_implies(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_inc:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_inc(args[0].bv_state);
        break;
      case BTOR2_TAG_ite:assert (l->nargs == 3);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        if (res.type == BtorSimState::Type::ARRAY) {
          assert (args[1].type == BtorSimState::Type::ARRAY);
          assert (args[2].type == BtorSimState::Type::ARRAY);
          res.array_state = btorsim_am_ite(
              args[0].bv_state, args[1].array_state, args[2].array_state);
        } else {
          assert (args[1].type == BtorSimState::Type::BITVEC);
          assert (args[2].type == BtorSimState::Type::BITVEC);
          res.bv_state = btorsim_bv_ite(
              args[0].bv_state, args[1].bv_state, args[2].bv_state);
        }
        break;
      case BTOR2_TAG_mul:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_mul(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_nand:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_nand(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_neg:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_neg(args[0].bv_state);
        break;
      case BTOR2_TAG_neq:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        if (args[0].type == BtorSimState::Type::ARRAY) {
          assert (args[1].type == BtorSimState::Type::ARRAY);
          res.bv_state =
              btorsim_am_neq(args[0].array_state, args[1].array_state);
        } else {
          assert (args[0].type == BtorSimState::Type::BITVEC);
          assert (args[1].type == BtorSimState::Type::BITVEC);
          res.bv_state = btorsim_bv_neq(args[0].bv_state, args[1].bv_state);
        }
        break;
      case BTOR2_TAG_nor:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_nor(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_not:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_not(args[0].bv_state);
        break;
      case BTOR2_TAG_one:assert (res.type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_one(l->sort.bitvec.width);
        break;
      case BTOR2_TAG_ones:assert (res.type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_ones(l->sort.bitvec.width);
        break;
      case BTOR2_TAG_or:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_or(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_redand:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_redand(args[0].bv_state);
        break;
      case BTOR2_TAG_redor:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_redor(args[0].bv_state);
        break;
      case BTOR2_TAG_redxor:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_redxor(args[0].bv_state);
        break;
      case BTOR2_TAG_slice:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        res.bv_state =
            btorsim_bv_slice(args[0].bv_state, l->args[1], l->args[2]);
        break;
      case BTOR2_TAG_sub:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_sub(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_uext:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        {
          uint32_t width = args[0].bv_state->width;
          assert (width <= l->sort.bitvec.width);
          uint32_t padding = l->sort.bitvec.width - width;
          if (padding)
            res.bv_state = btorsim_bv_uext(args[0].bv_state, padding);
          else
            res.bv_state = btorsim_bv_copy(args[0].bv_state);
        }
        break;
      case BTOR2_TAG_udiv:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_udiv(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_sdiv:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_sdiv(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_sext:assert (l->nargs == 1);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        {
          uint32_t width = args[0].bv_state->width;
          assert (width <= l->sort.bitvec.width);
          uint32_t padding = l->sort.bitvec.width - width;
          if (padding)
            res.bv_state = btorsim_bv_sext(args[0].bv_state, padding);
          else
            res.bv_state = btorsim_bv_copy(args[0].bv_state);
        }
        break;
      case BTOR2_TAG_sll:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_sll(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_srl:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_srl(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_sra:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_sra(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_srem:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_srem(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_ugt:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_ult(args[1].bv_state, args[0].bv_state);
        break;
      case BTOR2_TAG_ugte:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_ulte(args[1].bv_state, args[0].bv_state);
        break;
      case BTOR2_TAG_ult:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC),
            assert (args[0].type == BtorSimState::Type::BITVEC),
            assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_ult(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_ulte:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_ulte(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_urem:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_urem(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_sgt:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_slt(args[1].bv_state, args[0].bv_state);
        break;
      case BTOR2_TAG_sgte:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_slte(args[1].bv_state, args[0].bv_state);
        break;
      case BTOR2_TAG_slt:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_slt(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_slte:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_slte(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_iff:
      case BTOR2_TAG_xnor:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_xnor(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_xor:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::BITVEC);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_xor(args[0].bv_state, args[1].bv_state);
        break;
      case BTOR2_TAG_zero:assert (res.type == BtorSimState::Type::BITVEC);
        res.bv_state = btorsim_bv_zero (l->sort.bitvec.width);
        break;
      case BTOR2_TAG_read:assert (l->nargs == 2);
        assert (res.type == BtorSimState::Type::BITVEC);
        assert (args[0].type == BtorSimState::Type::ARRAY);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        res.bv_state = args[0].array_state->read(args[1].bv_state);
        {
          Btor2Line *mem = btor2parser_get_line_by_id(model, l->args[0]);
          msg(4,
              "read %s[%s] -> %s",
              mem->symbol ? mem->symbol : std::to_string(mem->id).c_str(),
              btorsim_bv_to_string(args[1].bv_state).c_str(),
              btorsim_bv_to_string(res.bv_state).c_str());
        }
        break;
      case BTOR2_TAG_write:assert (l->nargs == 3);
        assert (res.type == BtorSimState::Type::ARRAY);
        assert (args[0].type == BtorSimState::Type::ARRAY);
        assert (args[1].type == BtorSimState::Type::BITVEC);
        assert (args[2].type == BtorSimState::Type::BITVEC);
        res.array_state =
            args[0].array_state->write(args[1].bv_state, args[2].bv_state);
        {
          Btor2Line *mem = btor2parser_get_line_by_id(model, l->args[0]);
          msg(4,
              "write %s[%s] <- %s",
              mem->symbol ? mem->symbol : std::to_string(mem->id).c_str(),
              btorsim_bv_to_string(args[1].bv_state).c_str(),
              btorsim_bv_to_string(args[2].bv_state).c_str());
        }
        break;
      default:
        die("can not randomly simulate operator '%s' at line %" PRId64,
            l->name,
            l->lineno);
        break;
    }
    for (uint32_t i = 0; i < l->nargs; i++) args[i].remove();
    update_current_state(id, res);
  }
  if (res.type == BtorSimState::Type::ARRAY) {
    res.array_state = res.array_state->copy();
  } else {
    assert (res.type == BtorSimState::Type::BITVEC);
    if (sign < 0)
      res.bv_state = btorsim_bv_not(res.bv_state);
    else
      res.bv_state = btorsim_bv_copy(res.bv_state);
  }
  return res;
}

/*------------------------------------------------------------------------*/

static void setup_states() {
  current_state.resize(num_format_lines);
  hash_value.resize(num_format_lines, std::make_pair(0ull, 0ull));
  for (int i = 0; i < num_format_lines; i++) {
    Btor2Line *l = btor2parser_get_line_by_id(model, i);
    if (l) {
      Btor2Sort *sort = get_sort(l, model);
      switch (sort->tag) {
        case BTOR2_TAG_SORT_bitvec:current_state[i].type = BtorSimState::Type::BITVEC;
          break;
        case BTOR2_TAG_SORT_array:current_state[i].type = BtorSimState::Type::ARRAY;
          break;
        default:die("Unknown sort");
      }
    }
  }
  for (auto state : states) {
    assert (current_state[state->id].type != BtorSimState::Type::INVALID);
  }
}

static void print_all_hash(int64_t step) {
  for (int64_t i = 1; i <= num_format_lines; ++i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    BtorSimBitVector *bv = current_state[i].bv_state;
    if (!bv) continue;

    fprintf(log_file, "%" PRId64 "", i);
    if (line->symbol) fprintf(log_file, " %s", line->symbol);
    fprintf(log_file, " %lX,%lX\n", hash_value[i].first, hash_value[i].second);
  }
}

static void print_state_or_input(int64_t id, int64_t pos, int64_t step, bool is_input) {
  auto print_bv = [](const BtorSimBitVector *bv) {
    assert (bv);
    for (int i = bv->width - 1; i >= 0; --i)
      fprintf(log_file, "%d", btorsim_bv_get_bit(bv, i));
  };

  Btor2Line *l = btor2parser_get_line_by_id(model, id);
  switch (current_state[id].type) {
    case BtorSimState::Type::BITVEC:fprintf(log_file, "%" PRId64 " ", pos);
      print_bv(current_state[id].bv_state);
      if (l->symbol)
        fprintf(log_file, " %s%s%" PRId64, l->symbol, is_input ? "@" : "#", step);
      fputc('\n', log_file);
      break;
    case BtorSimState::Type::ARRAY:
      for (auto e : current_state[id].array_state->data) {
        fprintf(log_file, "%" PRId64 " [%s]", pos, e.first.c_str());
        print_bv(e.second);
        if (l->symbol)
          fprintf(log_file, " %s%s%" PRId64, l->symbol, is_input ? "@" : "#", step);
        fputc('\n', log_file);
      }
      break;
    default:die("uninitialized current_state %" PRId64, id);
  }
}

static void report() {
  if (num_unreached_bads < (int64_t) bads.size()) {
    fprintf(log_file, "[simubtor] reached bad state properties {");
    for (size_t i = 0; i < bads.size(); i++) {
      int64_t r = reached_bads[i];
      if (r >= 0) fprintf(log_file, " b%lu@%" PRId64, i, r);
    }
    fprintf(log_file, " }\n");
  } else if (!bads.empty())
    fprintf(log_file, "[simubtor] no bad state property reached\n");
}

static void initialize_states(int32_t randomly) {
  for (size_t i = 0; i < states.size(); i++) {
    Btor2Line *state = states[i];
    assert (0 <= state->id), assert (state->id < num_format_lines);
    Btor2Line *init = inits[state->id];
    switch (current_state[state->id].type) {
      case BtorSimState::Type::BITVEC: {
        assert (state->sort.tag == BTOR2_TAG_SORT_bitvec);
        if (init) {
          assert (init->nargs == 2);
          assert (init->args[0] == state->id);
          BtorSimState update = simulate(init->args[1]);
          assert (update.type == BtorSimState::Type::BITVEC);
          update_current_state(state->id, update);
        } else {
          BtorSimBitVector *bv;
          if (randomly)
            bv = btorsim_bv_new_random(&rng, state->sort.bitvec.width);
          else
            bv = btorsim_bv_new(state->sort.bitvec.width);
          update_current_state(state->id, bv);
        }
      }
        break;
      case BtorSimState::Type::ARRAY:assert (state->sort.tag == BTOR2_TAG_SORT_array);
        if (init) {
          assert (init->nargs == 2);
          assert (init->args[0] == state->id);
          BtorSimState update = simulate(init->args[1]);
          switch (update.type) {
            case BtorSimState::Type::ARRAY:update_current_state(state->id, update);
              break;
            case BtorSimState::Type::BITVEC: {
              Btor2Line *li =
                  btor2parser_get_line_by_id(model, state->sort.array.index);
              Btor2Line *le = btor2parser_get_line_by_id(
                  model, state->sort.array.element);
              assert (li->sort.tag == BTOR2_TAG_SORT_bitvec);
              assert (le->sort.tag == BTOR2_TAG_SORT_bitvec);
              BtorSimArrayModel *am = new BtorSimArrayModel(
                  li->sort.bitvec.width, le->sort.bitvec.width);
              am->const_init = update.bv_state;
              update_current_state(state->id, am);
            }
              break;
            default:die("bad result simulating %" PRId64, init->args[1]);
          }
        } else {
          Btor2Line *li =
              btor2parser_get_line_by_id(model, state->sort.array.index);
          Btor2Line *le =
              btor2parser_get_line_by_id(model, state->sort.array.element);
          assert (li->sort.tag == BTOR2_TAG_SORT_bitvec);
          assert (le->sort.tag == BTOR2_TAG_SORT_bitvec);
          BtorSimArrayModel *am = new BtorSimArrayModel(
              li->sort.bitvec.width, le->sort.bitvec.width);
          if (randomly) {
            am->random_seed = btorsim_rng_rand(&rng);
          }
          update_current_state(state->id, am);
        }
        break;
      default:die("uninitialized current_state %" PRId64, state->id);
    }
  }
}

static void initialize_inputs(int64_t k, int32_t randomize) {
  for (size_t i = 0; i < inputs.size(); i++) {
    Btor2Line *input = inputs[i];
    if (input->sort.tag == BTOR2_TAG_SORT_bitvec) {
      uint32_t width = input->sort.bitvec.width;
      BtorSimBitVector *update;
      if (!input->next) {
        if (randomize)
          update = btorsim_bv_new_random(&rng, width);
        else
          update = btorsim_bv_new(width);
      } else {
        update = btorsim_bv_copy(fixed_input[input->next]);
      }
      update_current_state(input->id, update);
    } else {
      assert (input->sort.tag == BTOR2_TAG_SORT_array);
      Btor2Line *li =
          btor2parser_get_line_by_id(model, input->sort.array.index);
      Btor2Line *le =
          btor2parser_get_line_by_id(model, input->sort.array.element);
      assert (li->sort.tag == BTOR2_TAG_SORT_bitvec);
      assert (le->sort.tag == BTOR2_TAG_SORT_bitvec);
      BtorSimArrayModel *am = new BtorSimArrayModel(li->sort.bitvec.width,
                                                    le->sort.bitvec.width);
      if (randomize) {
        am->random_seed = btorsim_rng_rand(&rng);
      }
      update_current_state(input->id, am);
    }
  }
}

static bool simulate_step(int64_t k) {
  msg(1, "simulating step %" PRId64, k);
  for (int64_t i = 0; i < num_format_lines; i++) {
    Btor2Line *l = btor2parser_get_line_by_id(model, i);
    if (!l) continue;
    if (l->tag == BTOR2_TAG_sort || l->tag == BTOR2_TAG_init
        || l->tag == BTOR2_TAG_next || l->tag == BTOR2_TAG_bad
        || l->tag == BTOR2_TAG_constraint || l->tag == BTOR2_TAG_fair
        || l->tag == BTOR2_TAG_justice || l->tag == BTOR2_TAG_output)
      continue;

    BtorSimState s = simulate(i);
    s.remove();
  }

  if (!k) return 0;
  for (size_t i = 0; i < constraints.size(); i++) {
    Btor2Line *constraint = constraints[i];
    BtorSimState s = current_state[constraint->args[0]];
    assert (s.type == BtorSimState::Type::BITVEC);
    if (!btorsim_bv_is_zero(s.bv_state)) continue;
    return 0;
  }

  for (size_t i = 0; i < bads.size(); i++) {
    int64_t r = reached_bads[i];
    if (r >= 0) continue;
    Btor2Line *bad = bads[i];
    BtorSimState s = current_state[bad->args[0]];
    assert (s.type == BtorSimState::Type::BITVEC);
    if (btorsim_bv_is_zero(s.bv_state)) continue;
    int64_t bound = reached_bads[i];
    if (bound >= 0) continue;
    reached_bads[i] = k;
    assert (num_unreached_bads > 0);
    if (!--num_unreached_bads)
      msg(1,
          "all %" PRId64 " bad state properties reached",
          (int64_t) bads.size());
  }
  return 1;
}

static void random_simulation(int64_t k) {
  auto run_step = [](int64_t k, int32_t randomize) {
    initialize_states(randomize);
    initialize_inputs(k, randomize);
    return simulate_step(k);
  };
  auto reset_state = []() {
    for (int64_t i = 1; i <= num_format_lines; i++) {
      Btor2Line *l = btor2parser_get_line_by_id(model, i);
      if (!l) continue;
      if (l->tag == BTOR2_TAG_sort || l->tag == BTOR2_TAG_init
          || l->tag == BTOR2_TAG_next || l->tag == BTOR2_TAG_bad
          || l->tag == BTOR2_TAG_constraint || l->tag == BTOR2_TAG_fair
          || l->tag == BTOR2_TAG_justice || l->tag == BTOR2_TAG_output)
        continue;
//      current_state[i].remove();
      current_state[i].bv_state = nullptr;
    }
  };

  int64_t succ = 0;
  run_step(0, 1);
  std::vector<short> cons(num_format_lines + 1, 0);
  for (int64_t i = num_format_lines; i > 0; --i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    if (!line) continue;

    if (line->tag == BTOR2_TAG_constraint)
      cons[line->args[0]] = 1;
    else if (line->tag == BTOR2_TAG_and) {
      if (cons[i] <= 0) continue;
      for (int64_t j = 0; j < line->nargs; ++j) {
        int id = labs(line->args[j]);
        if (line->args[j] < 0) cons[id] = -1;
        else cons[id] = 1;
      }
    } else if (line->tag == BTOR2_TAG_or) {
      if (cons[i] >= 0) continue;
      for (int64_t j = 0; j < line->nargs; ++j) {
        int id = labs(line->args[j]);
        if (line->args[j] < 0) cons[id] = 1;
        else cons[id] = -1;
      }
    } else if (line->tag == BTOR2_TAG_eq) {
      if (cons[i] <= 0) continue;
      int p = line->args[0], q = line->args[1];
      Btor2Line *model_p = btor2parser_get_line_by_id(model, p),
          *model_q = btor2parser_get_line_by_id(model, q);

      if (model_q->tag == BTOR2_TAG_input) {
        std::swap(p, q);
        std::swap(model_p, model_q);
      }
      if (model_p->tag != BTOR2_TAG_input || model_q->tag == BTOR2_TAG_input) continue;

      if (p < 0) p = -p, q = -q;
      model_p->next = fixed_input.size();

      BtorSimBitVector *bv = btorsim_bv_copy(current_state[model_q->id].bv_state);
      fixed_input.push_back(bv);
      if (q < 0) {
        for (uint32_t j = bv->width - 1; j >= 0; --j)
          bv->bits[j] ^= 1;
      }

      fprintf(log_file, "[simubtor] parse constraints: %s must equal to ", model_p->symbol);
      for (int j = bv->width - 1; j >= 0; --j)
        fprintf(log_file, "%d", btorsim_bv_get_bit(bv, j));
      fprintf(log_file, "\n");
    }
  }
  reset_state();

  for (int64_t step = 1; step <= k; ++step) {
    if (!num_unreached_bads) break;
    uint32_t base1 = btorsim_rng_rand(&base_rng), base2 = btorsim_rng_rand(&base_rng);
    if (run_step(step, 1)) {
      ++succ;
      fprintf(log_file, "[simubtor] constraints satisfied at time %" PRId64 "\n", step);
      for (size_t i = 1; i <= num_format_lines; ++i) {
        if (current_state[i].type != BtorSimState::BITVEC) continue;
        BtorSimBitVector *bv = current_state[i].bv_state;
        if (!bv) continue;

        uint64_t val1 = 0, val2 = 0;
        for (int j = (int) bv->width - 1; j >= 0; --j) {
          val1 = val1 * base1 + (btorsim_bv_get_bit(bv, j) + 1);
          val2 = val2 * base2 + (btorsim_bv_get_bit(bv, j) + 1);
        }
        val1 *= base1;
        val2 *= base2;
        hash_value[i].first ^= val1;
        hash_value[i].second ^= val2;
      }

      fprintf(log_file, "@%" PRId64 "\n", succ);
      for (size_t i = 0, n = inputs.size(); i < n; ++i) {
        Btor2Line *input = inputs[i];
        print_state_or_input(input->id, i, succ, 1);
      }
      if (print_states) {
        fprintf(log_file, "#%" PRId64 "\n", succ);
        for (size_t i = 0, n = parse_states.size(); i < n; ++i) {
          Btor2Line *state = parse_states[i].first;
          print_state_or_input(state->id, i, succ, 0);
        }
      }
    } else
      fprintf(log_file, "[simubtor] constraints violated at time %" PRId64 "\n", step);
    if (step < k) reset_state();
  }

  if (print_hash) {
    fprintf(log_file, "$hash value\n");
    print_all_hash(succ);
  }
  report();
  fprintf(log_file, "[simubtor] successful simulation: %" PRId64 "/%" PRId64 "\n", succ, k);
}

int main(int argc, char const *argv[]) {
  static int32_t step = 10000, s = -1, hash_seed = -1, capacity = 4;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "--help")) {
      fputs(usage, stdout);
      exit(1);
    } else if (!strcmp(argv[i], "-s")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simubtor' error: argument to '-s' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &s)) {
        fprintf(stderr, "*** 'simubtor' error: invalid number in '-s %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "-r")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simubtor' error: argument to '-r' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &step)) {
        fprintf(stderr, "*** 'simubtor' error: invalid number in '-r %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "-c")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simubtor' error: argument to '-c' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &capacity)) {
        fprintf(stderr, "*** 'simubtor' error: invalid number in '-c %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "-h")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simubtor' error: argument to '-h' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &hash_seed)) {
        fprintf(stderr, "*** 'simubtor' error: invalid number in '-h %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "--log")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'simubtor' error: argument to '--log' missing\n");
        exit(1);
      }
      log_path = argv[i];
    } else if (!strcmp(argv[i], "--model")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'simubtor' error: argument to '--model' missing\n");
        exit(1);
      }
      model_path = argv[i];
    } else if (!strcmp(argv[i], "--output")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'simubtor' error: argument to '--output' missing\n");
        exit(1);
      }
      output_path = argv[i];
    } else if (!strcmp(argv[i], "--states"))
      print_states = true;
    else if (!strcmp(argv[i], "--hash"))
      print_hash = true;
    else if (!strcmp(argv[i], "--check-all"))
      all_hash = true;
    else {
      fprintf(stderr, "*** 'simubtor' error: invalid command line option '%s'", argv[i]);
      exit(1);
    }
  }
  open("simubtor", model_path, model_file, "<stdin>", stdin, 1);
  open("simubtor", output_path, output_file, "<stdout>", stdout, 0);
  open("simubtor", log_path, log_file, "<stderr>", stderr, 0);

  parse_model();
  fixed_input.resize(1);

  int64_t number_of_lines = btor2parser_max_id(model);
  for (int i = 1; i <= number_of_lines; ++i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    if (!line || !line->symbol) continue;

    auto parse_symbol = [](char *symbol) -> std::pair<Btor2Tag, std::pair<int, int>> {
      std::vector<char *> pos;
      for (char *p = symbol; *p; ++p)
        if (*p == '.') pos.push_back(p);
      assert(pos.size() >= 2);
      *pos.back() = '\0';

      int id, time;
      char *p2 = pos.back(), *p1 = *std::next(pos.rbegin());
      parse_int(p2 + 6, &time);
      parse_int(p1 + 4, &id);

      *p2 = '.';
      if (*(p1 - 1) == 't')
        return std::make_pair(BTOR2_TAG_input, std::make_pair(id, time));
      else
        return std::make_pair(BTOR2_TAG_state, std::make_pair(id, time));
    };
    auto [tag, info] = parse_symbol(line->symbol);
    if (tag == BTOR2_TAG_state)
      parse_states.emplace_back(line, info);
  }

  if (s < 0) s = 0;
  if (hash_seed < 0) hash_seed = 0;
  setup_states();
  btorsim_rng_init(&rng, (uint32_t) s);
  btorsim_rng_init(&base_rng, (uint32_t) hash_seed);
  random_simulation(step);

  std::vector<std::tuple<uint64_t, uint64_t, uint32_t, int>> hash_set;
  if (all_hash) {
    for (size_t i = 1; i <= number_of_lines; ++i) {
      if (current_state[i].type != BtorSimState::BITVEC) continue;
      if (!current_state[i].bv_state) continue;
      Btor2Line *line = btor2parser_get_line_by_id(model, i);
      hash_set.emplace_back(hash_value[i].first, hash_value[i].second,
                            line->sort.bitvec.width, i);
    }
  } else {
    for (size_t i = 0, n = parse_states.size(); i < n; ++i) {
      Btor2Line *line = parse_states[i].first;
      hash_set.emplace_back(hash_value[line->id].first, hash_value[line->id].second,
                            line->sort.bitvec.width, parse_states[i].second.first);
    }
  }
  std::sort(hash_set.begin(), hash_set.end());

  int group = 0;
  std::set<std::pair<int, int>> candidate;
  for (size_t i = 0, n = hash_set.size(); i < n;) {
    size_t j;
    std::set<int> set_id;
    for (j = i; j + 1 < n && std::get<0>(hash_set[i]) == std::get<0>(hash_set[j + 1])
        && std::get<1>(hash_set[i]) == std::get<1>(hash_set[j + 1])
        && std::get<2>(hash_set[i]) == std::get<2>(hash_set[j + 1]); ++j);

    for (size_t k = i; k <= j; ++k) set_id.insert(std::get<3>(hash_set[k]));
    if (1 < set_id.size() && set_id.size() <= capacity) {
      for (auto x : set_id)
        for (auto y : set_id)
          if (x != y) candidate.insert(std::make_pair(std::min(x, y), std::max(x, y)));
      ++group;
    }
    i = j + 1;
  }
  for (auto x : candidate)
    fprintf(output_file, "%d %d\n", x.first, x.second);
  printf("candidate: %d\ngroup: %d\n", candidate.size(), group);

  btor2parser_delete(model);

  return 0;
}