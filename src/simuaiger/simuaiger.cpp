//
// Created by CSHwang on 2024/3/26.
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
#include <functional>

extern "C" {
#include "aiger.h"
}
#include "btorfunc.h"
#include "twosat.h"
#include "btorsim/btorsimstate.h"

/*------------------------------------------------------------------------*/

aiger *model;

static FILE *log_file;
static FILE *model_file;
static FILE *output_file;
static const char *log_path;
static const char *model_path;
static const char *output_path;

int32_t verbosity;
static const char *usage =
    "usage: simuaiger [ <option> ... ]\n"
    "\n"
    "where <option> is one of the following\n"
    "\n"
    "  -s <s>                  random seed (default 0)\n"
    "  -h <s>                  random hash seed (default 0)\n"
    "  -c <c>                  set check capacity (default 4)\n"
    "  -r <n>                  generate <n> random transitions (default 10000)\n"
    "\n"
    "  --help                  print this command line option summary\n"
    "  --var                   print variables' value to log\n"
    "  --hash                  print variables' hash value to log\n"
    "\n"
    "  --model <model>         load model from <model> in 'BTOR' format\n"
    "  --output <output>       write result to <output>\n"
    "  --log <log>             write log to <log>\n";

static BtorSimRNG rng, hrng;
static bool print_var = false;
static bool print_hash = false;

static std::vector<short> cons;
static std::vector<uint64_t> hvalue;

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

static void preprocessing() {
  std::vector<short> tag(2 * (model->maxvar + 1), -1);
  std::vector<bool> isinput(2 * (model->maxvar + 1), 0);
  cons.resize(2 * (model->maxvar + 1), -1);

  auto tagged = [&](uint lit) {
    assert(tag[lit] != 0);
    tag[lit] = 1;
    tag[lit ^ 1] = 0;
  };
  auto assign = [&](uint lit, short x) {
    assert(cons[lit] == -1 || cons[lit] == x);
    if (cons[lit] == -1)
      fprintf(log_file, "[simuaiger] preprocessing: assign var (%u) to %d\n", lit, x);
    cons[lit] = x;
    cons[lit ^ 1] = x ^ 1;
  };

  for (int i = 0; i < model->num_inputs; ++i) {
    uint lit = model->inputs[i].lit;
    isinput[lit] = isinput[lit ^ 1] = 1;
  }
  for (int i = 0; i < model->num_constraints; ++i) tagged(model->constraints[i].lit);

  TwoSAT::initialize(2 * (model->maxvar + 1));
  for (int i = (int) model->num_ands - 1; i >= 0; --i) {
    uint lhs = model->ands[i].lhs, rhs0 = model->ands[i].rhs0, rhs1 = model->ands[i].rhs1;

    short nw = tag[lhs];
    if (nw == 1) {
      tagged(rhs0);
      tagged(rhs1);
    } else if (nw == 0 && isinput[rhs0] && isinput[rhs1]) TwoSAT::add_edge(log_file, rhs0, rhs1);
  }

  for (int i = 0; i < model->num_inputs; ++i) {
    uint lit = model->inputs[i].lit;
    if (tag[lit] != -1) {
      lit ^= tag[lit];
      TwoSAT::add_edge(log_file, lit, lit ^ 1);
    }
  }

  std::vector<uint> choose = TwoSAT::solve();
  for (auto x : choose) assign(x, 1);
}

static void random_simulation(int k) {
  std::vector<short> table(2 * (model->maxvar + 1));
  auto initialize = [&]() {
    for (int i = 0; i < table.size(); ++i) table[i] = -1;
    std::function<void(uint, short)> assign = [&](uint lit, short x) {
      if (table[lit] == x) return;

      assert(table[lit] == -1);
      table[lit] = x;
      table[lit ^ 1] = x ^ 1;

      lit ^= x ^ 1;
      for (auto nlit : TwoSAT::eg[lit]) assign(nlit, 1);
    };

    assign(0, 0);
    int free_variables = 0;
    for (int i = 0; i < model->num_inputs; ++i) {
      int lit = model->inputs[i].lit;
      if (cons[lit] != -1) assign(lit, cons[lit]);
      else {
        ++free_variables;
        assign(lit, btorsim_rng_rand(&rng) & 1);
      }
    }
    assert(free_variables > 32);
  };
  auto run_step = [&]() {
    for (int i = 0; i < model->num_ands; ++i) {
      uint lhs = model->ands[i].lhs, rhs0 = model->ands[i].rhs0, rhs1 = model->ands[i].rhs1;
      if (table[rhs0] == -1 || table[rhs1] == -1) continue;

      short res = table[rhs0] & table[rhs1];
      assert(table[lhs] == -1 || table[lhs] == res);
      table[lhs] = res;

      lhs ^= 1;
      res ^= 1;
      assert(table[lhs] == -1 || table[lhs] == res);
      table[lhs] = res;
    }

    for (int i = 0; i < model->num_constraints; ++i) {
      uint lit = model->constraints[i].lit;
      assert(table[lit] != -1);
      if (!table[lit]) return 0;
    }
    for (int i = 0; i < model->num_bad; ++i) {
      uint lit = model->bad[i].lit;
      assert(table[lit] != -1);
      if (table[lit]) {
        fprintf(log_file, "[simuaiger] reach bad property (%u)\n", lit);
        exit(0);
      }
    }
    return 1;
  };

  int succ = 0;
  for (int step = 1; step <= k; ++step) {
    initialize();
    if (run_step()) {
      uint64_t base = (uint64_t) btorsim_rng_rand(&hrng) << 32 | btorsim_rng_rand(&hrng);
      for (uint i = 1; i <= model->maxvar; ++i) {
        uint lit = i << 1;
        if (table[lit] == -1) continue;
        if (table[lit]) hvalue[i] ^= base;
      }

      ++succ;
      if (print_var) {
        fprintf(log_file, "@%d\n", succ);
        for (uint i = 0; i < model->num_inputs; ++i) {
          uint lit = model->inputs[i].lit;
          fprintf(log_file, "(%u) %d input@%d\n", lit, table[lit], succ);
        }
        fprintf(log_file, "@%d\n", succ);
        for (uint i = 1; i <= model->maxvar; ++i) {
          uint lit = i << 1;
          fprintf(log_file, "(%u) %d var@%d\n", lit, table[lit], succ);
        }
      }
    } else fprintf(log_file, "[simuaiger] constraints violated at time %d\n", step);
  }

  if (print_hash) {
    fprintf(log_file, "$hash value");
    for (uint i = 1; i <= model->maxvar; ++i) {
      uint lit = i << 1;
      fprintf(log_file, "%u (%u) %lX\n", i, lit, hvalue[i]);
    }
  }
  fprintf(log_file, "[simuaiger] successful simulation: %d/%d\n", succ, k);
}

int main(int argc, char const *argv[]) {
  static int step = 10000, seed = -1, hash_seed = -1, capacity = 4;
  for (int i = 1; i < argc; ++i) {
    if (!strcmp(argv[i], "--help")) {
      fputs(usage, stdout);
      exit(1);
    } else if (!strcmp(argv[i], "-s")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simuaiger' error: argument to '-s' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &seed)) {
        fprintf(stderr, "*** 'simuaiger' error: invalid number in '-s %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "-r")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simuaiger' error: argument to '-r' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &step)) {
        fprintf(stderr, "*** 'simuaiger' error: invalid number in '-r %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "-c")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simuaiger' error: argument to '-c' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &capacity)) {
        fprintf(stderr, "*** 'simuaiger' error: invalid number in '-c %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "-h")) {
      if (++i >= argc) {
        fprintf(stderr, "*** 'simuaiger' error: argument to '-h' missing\n");
        exit(1);
      }
      if (!parse_int(argv[i], &hash_seed)) {
        fprintf(stderr, "*** 'simuaiger' error: invalid number in '-h %s'", argv[i]);
        exit(1);
      }
    } else if (!strcmp(argv[i], "--log")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'simuaiger' error: argument to '--log' missing\n");
        exit(1);
      }
      log_path = argv[i];
    } else if (!strcmp(argv[i], "--model")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'simuaiger' error: argument to '--model' missing\n");
        exit(1);
      }
      model_path = argv[i];
    } else if (!strcmp(argv[i], "--output")) {
      if (++i == argc) {
        fprintf(stderr, "*** 'simuaiger' error: argument to '--output' missing\n");
        exit(1);
      }
      output_path = argv[i];
    } else if (!strcmp(argv[i], "--hash"))
      print_hash = true;
    else if (!strcmp(argv[i], "--var"))
      print_var = true;
    else {
      fprintf(stderr, "*** 'simuaiger' error: invalid command line option '%s'", argv[i]);
      exit(1);
    }
  }
  open("simuaiger", model_path, model_file, "<stdin>", stdin, 1);
  open("simuaiger", output_path, output_file, "<stdout>", stdout, 0);
  open("simuaiger", log_path, log_file, "<stderr>", stderr, 0);

  model = aiger_init();
  const char *error = aiger_read_from_file(model, model_file);
  if (error) {
    fprintf(stderr, "*** 'simuaiger' error: %s %s\n", model_path, error);
    exit(1);
  }

  if (model->num_latches) {
    fprintf(stderr, "*** 'simuaiger' error: can not handle latches\n");
    exit(1);
  }
  if (model->num_outputs) {
    fprintf(stderr, "*** 'simuaiger' error: can not handle outputs\n");
    exit(1);
  }
  if (model->num_justice) fprintf(stderr, "[simuaiger] ignoring justice properties\n");
  if (model->num_fairness) fprintf(stderr, "[simuaiger] ignoring fairness constraints\n");

  aiger_reencode(model);
  btorsim_rng_init(&rng, seed);
  btorsim_rng_init(&hrng, hash_seed);
  hvalue.resize(model->maxvar + 1, 0);

  preprocessing();
  random_simulation(step);

  std::vector<std::pair<uint64_t, uint>> hash_set;
  for (uint i = 1; i <= model->maxvar; ++i) hash_set.emplace_back(hvalue[i], i);
  std::sort(hash_set.begin(), hash_set.end());

  int group = 0;
  std::vector<std::pair<int, int>> candidate;
  for (size_t i = 0, n = hash_set.size(); i < n;) {
    size_t j;
    for (j = i; j + 1 < n && hash_set[i].first == hash_set[j].first; ++j);

    if (1 < j - i + 1 && j - i + 1 <= capacity) {
      for (size_t x = i; x <= j; ++x)
        for (size_t y = x + 1; y <= j; ++y)
          candidate.emplace_back(hash_set[x].second, hash_set[y].second);
      ++group;
    }
    i = j + 1;
  }
  for (auto x : candidate)
    fprintf(output_file, "%d %d\n", x.first, x.second);
  printf("candidate: %zu/%u (%0.3lf)\ngroup: %d\n",
         candidate.size(),
         model->maxvar,
         (double) candidate.size() / model->maxvar,
         group);

  return 0;
}
