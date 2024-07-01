//
// Created by CSHwang on 2024/4/8.
//

#include <cctype>
#include <cstdio>
#include <climits>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <cinttypes>

#include <cassert>
#include <vector>

extern "C" {
#include "aiger.h"
}
#include "btorfunc.h"

/*------------------------------------------------------------------------*/

aiger *model;

static FILE *model_file;
static FILE *output_file;
static const char *list_path;
static const char *model_path;
static const char *output_path;

int32_t verbosity;
static const char *usage =
    "usage: aigmerge [ <option> ... ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -h                      print this command line option summary\n"
    "  --model <model>         load model from <model> in 'BTOR' format\n"
    "  --list <list>           load merged list from <list>\n"
    "  --output <output>       write eliminated model to <output>\n";

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

/*------------------------------------------------------------------------*/

std::vector<bool> fixed;

struct UnionSet {
  std::vector<int> fa;
  UnionSet() = default;
  explicit UnionSet(int n) { fa.resize(n, -1); }

  void resize(int n) { fa.resize(n, -1); }
  int findset(int x) {
    if (fa[x] == -1) return x;
    return (fa[x] = findset(fa[x]));
  }
  void merge(int x, int y) {
    int fx = findset(x), fy = findset(y);
    if (fx == fy) return;

    if (fx > fy) std::swap(fx, fy);
    fa[fy] = fx;
  }

  ~UnionSet() = default;
} union_set;

static uint convert(uint x) {
  uint fa = union_set.findset(x >> 1);
  return (fa << 1) | (x & 1);
}

int main(int argc, char const *argv[]) {
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "-h")) {
      fputs(usage, stdout);
      exit(1);
    } else if (!strcmp(argv[i], "--model")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'aigmerge' error: argument to '--model' missing\n");
        exit(1);
      }
      model_path = argv[i];
    } else if (!strcmp(argv[i], "--list")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'aigmerge' error: argument to '--list' missing\n");
        exit(1);
      }
      list_path = argv[i];
    } else if (!strcmp(argv[i], "--output")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'aigmerge' error: argument to '--output' missing\n");
        exit(1);
      }
      output_path = argv[i];
    } else {
      fprintf(stderr, "*** 'aigmerge' error: invalid command line option '%s'", argv[i]);
      exit(1);
    }
  }
  if (!list_path) {
    fprintf(stderr, "*** 'aigmerge' error: argument to '--list' is not allowed to be empty\n");
    exit(1);
  }
  open("aigmerge", model_path, model_file, "<stdin>", stdin, 1);
  open("aigmerge", output_path, output_file, "<stdout>", stdout, 0);

  model = aiger_init();
  const char *error = aiger_read_from_file(model, model_file);
  if (error) {
    fprintf(stderr, "*** 'aigmerge' error: %s %s\n", model_path, error);
    exit(1);
  }

  if (model->num_latches) {
    fprintf(stderr, "*** 'aigmerge' error: can not handle latches\n");
    exit(1);
  }
  if (model->num_outputs) {
    fprintf(stderr, "*** 'aigmerge' error: can not handle outputs\n");
    exit(1);
  }
  if (model->num_justice) fprintf(stderr, "[aigmerge] ignoring justice properties\n");
  if (model->num_fairness) fprintf(stderr, "[aigmerge] ignoring fairness constraints\n");

  aiger_reencode(model);

  std::ifstream fin;
  fin.open(list_path, std::ios::in);
  if (!fin.is_open()) {
    fprintf(stderr, "*** 'aigmerge' error: failed to open BTOR model file '%s' for reading\n",
            list_path);
    exit(1);
  }
  union_set.resize(model->maxvar + 1);
  fixed.resize(model->maxvar + 1, false);
  for (int x, y; fin >> x >> y;) union_set.merge(x, y);
  fin.close();

  for (int i = 0; i < model->num_constraints; ++i)
    fixed[aiger_lit2var(model->constraints[i].lit)] = true;
  for (int i = (int) model->num_ands - 1; i >= 0; --i) {
    uint lhs = model->ands[i].lhs, rhs0 = model->ands[i].rhs0, rhs1 = model->ands[i].rhs1;
    if (fixed[aiger_lit2var(lhs)]) {
      fixed[aiger_lit2var(rhs0)] = true;
      fixed[aiger_lit2var(rhs1)] = true;
    }
  }

  aiger *new_model = aiger_init();
  for (int i = 0; i < model->num_ands; ++i) {
    aiger_and a = model->ands[i];
    uint rhs0 = a.rhs0, rhs1 = a.rhs1;
    if (!fixed[aiger_lit2var(a.lhs)]) rhs0 = convert(rhs0), rhs1 = convert(rhs1);
    
    if (rhs0 < rhs1) std::swap(rhs0, rhs1);
    aiger_add_and(new_model, a.lhs, rhs0, rhs1);
  }
  for (int i = 0; i < model->num_bad; ++i)
    aiger_add_bad(new_model, convert(model->bad[i].lit), model->bad[i].name);
  for (int i = 0; i < model->num_inputs; ++i)
    aiger_add_input(new_model, model->inputs[i].lit, model->inputs[i].name);
  for (int i = 0; i < model->num_constraints; ++i)
    aiger_add_constraint(new_model, model->constraints[i].lit, model->constraints[i].name);

  aiger_reencode(new_model);
  aiger_write_to_file(new_model, aiger_binary_mode, output_file);

  return 0;
}
