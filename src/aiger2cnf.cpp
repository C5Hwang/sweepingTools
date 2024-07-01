//
// Created by CSHwang on 2024/3/1.
//

#include <cstdlib>
#include <cstring>

#include <vector>

extern "C" {
#include "aiger.h"
}
#include "btorfunc.h"

/*------------------------------------------------------------------------*/

aiger *model;
bool pg = true, print_map = false;

static FILE *model_file;
static FILE *output_file;
static const char *model_path;
static const char *output_path;

static const char *usage =
    "usage: aig2cnf [ <option> ... ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -h                      print this command line option summary\n"
    "  -m                      output mapping of aiger variables to cnf variables\n"
    "  -pg                     output simplified cnf\n"
    "  --model <model>         load model from <model> in 'AIGER' format\n"
    "  --output <output>       write result to <output>\n";

/*------------------------------------------------------------------------*/

int main(int argc, char const *argv[]) {
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "-h")) {
      fputs(usage, stdout);
      exit(1);
    } else if (!strcmp(argv[i], "-pg")) {
      pg = false;
    } else if (!strcmp(argv[i], "-m")) {
      print_map = true;
    } else if (!strcmp(argv[i], "--model")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'aiger2cnf' error: argument to '--model' missing\n");
        exit(1);
      }
      model_path = argv[i];
    } else if (!strcmp(argv[i], "--output")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'aiger2cnf' error: argument to '--output' missing\n");
        exit(1);
      }
      output_path = argv[i];
    } else {
      fprintf(stderr, "*** 'aiger2cnf' error: invalid command line option '%s'", argv[i]);
      exit(1);
    }
  }
  open("aiger2cnf", model_path, model_file, "<stdin>", stdin, 1);
  open("aiger2cnf", output_path, output_file, "<stdout>", stdout, 0);

  model = aiger_init();
  const char *error = aiger_read_from_file(model, model_file);
  if (error) {
    fprintf(stderr, "*** 'aiger2cnf' error: %s %s\n", model_path, error);
    exit(1);
  }

  if (model->num_latches) {
    fprintf(stderr, "*** 'aiger2cnf' error: can not handle latches\n");
    exit(1);
  }
  if (model->num_justice) fprintf(stderr, "[aiger2cnf] ignoring justice properties\n");
  if (model->num_fairness) fprintf(stderr, "[aiger2cnf] ignoring fairness constraints\n");

  aiger_reencode(model);

  std::vector<bool> refs(2 * (model->maxvar + 1), pg);
  std::vector<int> map(2 * (model->maxvar + 1), 0);

  for (uint i = 0; i < model->num_bad; ++i) refs[model->bad[i].lit] = 1;
  for (uint i = 0; i < model->num_outputs; ++i) refs[model->outputs[i].lit] = 1;
  for (uint i = 0; i < model->num_constraints; ++i) refs[model->constraints[i].lit] = 1;
  for (int i = (int) model->num_ands - 1; i >= 0; --i) {
    uint lhs = model->ands[i].lhs, rhs0 = model->ands[i].rhs0, rhs1 = model->ands[i].rhs1;
    if (refs[lhs]) refs[rhs0] = refs[rhs1] = 1;
    if (refs[lhs ^ 1]) refs[rhs0 ^ 1] = refs[rhs1 ^ 1] = 1;
  }

  int num_var = 0;
  std::vector<std::vector<int>> form;

  if (refs[0] || refs[1]) {
    map[0] = ++num_var;
    map[1] = -num_var;
    form.push_back({map[1]});
  }
  for (uint lit = 2; lit <= 2 * model->maxvar; lit += 2) {
    if (!refs[lit] && !refs[lit ^ 1]) continue;
    map[lit] = ++num_var;
    map[lit ^ 1] = -num_var;
    fprintf(output_file, "c %d -> %d\n", lit, num_var);
  }
  for (uint i = 0; i < model->num_ands; ++i) {
    uint lhs = model->ands[i].lhs, rhs0 = model->ands[i].rhs0, rhs1 = model->ands[i].rhs1;
    if (refs[lhs]) {
      form.push_back({map[lhs ^ 1], map[rhs0]});
      form.push_back({map[lhs ^ 1], map[rhs1]});
    }
    if (refs[lhs ^ 1]) {
      form.push_back({map[rhs0 ^ 1], map[rhs1 ^ 1], map[lhs]});
    }
  }

  for (uint i = 0; i < model->num_constraints; ++i) {
    uint lit = model->constraints[i].lit;
    form.push_back({map[lit]});
  }
  form.emplace_back(0);
  for (uint i = 0; i < model->num_bad; ++i) {
    uint lit = model->bad[i].lit;
    form.back().push_back(map[lit]);
  }
  for (uint i = 0; i < model->num_outputs; ++i) {
    uint lit = model->outputs[i].lit;
    form.back().push_back(map[lit]);
  }

  fprintf(output_file, "p cnf %d %zu\n", num_var, form.size());
  for (const auto &vt : form) {
    for (auto x : vt) fprintf(output_file, "%d ", x);
    fprintf(output_file, "0\n");
  }

  return 0;
}
