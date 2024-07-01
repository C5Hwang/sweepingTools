//
// Created by CSHwang on 2024/4/7.
//

#include <cctype>
#include <cstdio>
#include <climits>
#include <cstdlib>
#include <cstring>
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
static const char *model_path;
static const char *output_path;

int32_t verbosity;
static const char *usage =
    "usage: aigextract [ <option> ... ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -h                      print this command line option summary\n"
    "  --node [ <n> ... ]      set key node(end with '0')\n"
    "  --model <model>         load model from <model> in 'BTOR' format\n"
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

int main(int argc, char const *argv[]) {
  std::vector<int64_t> knode;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "-h")) {
      fputs(usage, stdout);
      exit(1);
    } else if (!strcmp(argv[i], "--node")) {
      int32_t node = -1;
      while (node != 0) {
        if (++i == argc) {
          fprintf(stderr, "*** 'aigextract' error: argument to '--node' missing\n");
          exit(1);
        }
        parse_int(argv[i], &node);
        if (node != 0) knode.emplace_back(node);
      }
    } else if (!strcmp(argv[i], "--model")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'aigextract' error: argument to '--model' missing\n");
        exit(1);
      }
      model_path = argv[i];
    } else if (!strcmp(argv[i], "--output")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'aigextract' error: argument to '--output' missing\n");
        exit(1);
      }
      output_path = argv[i];
    } else {
      fprintf(stderr, "*** 'aigextract' error: invalid command line option '%s'", argv[i]);
      exit(1);
    }
  }
  open("aigextract", model_path, model_file, "<stdin>", stdin, 1);
  open("aigextract", output_path, output_file, "<stdout>", stdout, 0);

  model = aiger_init();
  const char *error = aiger_read_from_file(model, model_file);
  if (error) {
    fprintf(stderr, "*** 'aigextract' error: %s %s\n", model_path, error);
    exit(1);
  }

  if (model->num_latches) {
    fprintf(stderr, "*** 'aigextract' error: can not handle latches\n");
    exit(1);
  }
  if (model->num_outputs) {
    fprintf(stderr, "*** 'aigextract' error: can not handle outputs\n");
    exit(1);
  }
  if (model->num_justice) fprintf(stderr, "[aigextract] ignoring justice properties\n");
  if (model->num_fairness) fprintf(stderr, "[aigextract] ignoring fairness constraints\n");

  aiger_reencode(model);

  std::vector<uint> bads;
  std::vector<aiger_and> ands;
  for (int i = 1; i < knode.size(); ++i) {
    uint u = knode[0] << 1, v = knode[i] << 1;
    if (u < v) std::swap(u, v);

    uint p1 = (++model->maxvar) << 1;
    ands.emplace_back((aiger_and) {p1, u ^ 1, v});
    uint p2 = (++model->maxvar) << 1;
    ands.emplace_back((aiger_and) {p2, u, v ^ 1});
    uint p3 = (++model->maxvar) << 1;
    ands.emplace_back((aiger_and) {p3, p2 ^ 1, p1 ^ 1});
    bads.emplace_back(p3 ^ 1);
  }

  aiger *new_model = aiger_init();
  for (int i = 0; i < model->num_ands; ++i) {
    aiger_and a = model->ands[i];
    aiger_add_and(new_model, a.lhs, a.rhs0, a.rhs1);
  }
  for (int i = 0; i < model->num_inputs; ++i)
    aiger_add_input(new_model, model->inputs[i].lit, model->inputs[i].name);
  for (int i = 0; i < model->num_constraints; ++i)
    aiger_add_constraint(new_model, model->constraints[i].lit, model->constraints[i].name);
  for (auto a : ands) aiger_add_and(new_model, a.lhs, a.rhs0, a.rhs1);
  for (auto bad : bads) aiger_add_bad(new_model, bad, NULL);

  aiger_reencode(new_model);
  aiger_write_to_file(new_model, aiger_binary_mode, output_file);

  return 0;
}
