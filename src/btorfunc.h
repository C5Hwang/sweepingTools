//
// Created by CSHwang on 2024/3/19.
//

#ifndef BTOR2TOOLS_SRC_BTORFUNC_H_
#define BTOR2TOOLS_SRC_BTORFUNC_H_

#include <string>
#include <cstdio>
#include <cstdlib>
#include <cinttypes>

#include <cassert>

#include "btor2parser/btor2parser.h"

/*------------------------------------------------------------------------*/

Btor2Tag classification(Btor2Line *line) {
  if (line->symbol) {
    std::string tmp(line->symbol);
    if (tmp.find("state.id") != std::string::npos)
      return BTOR2_TAG_state;
  }

  Btor2Tag type = BTOR2_TAG_not;
  switch (line->tag) {
    case BTOR2_TAG_sort:type = BTOR2_TAG_sort;
      break;

    case BTOR2_TAG_input:type = BTOR2_TAG_input;
      break;

    case BTOR2_TAG_state:type = BTOR2_TAG_state;
      break;

    case BTOR2_TAG_init:
    case BTOR2_TAG_next:type = BTOR2_TAG_next;
      break;

    case BTOR2_TAG_bad:
    case BTOR2_TAG_fair:
    case BTOR2_TAG_justice:
    case BTOR2_TAG_constraint:type = BTOR2_TAG_constraint;
      break;

    case BTOR2_TAG_const:
    case BTOR2_TAG_constd:
    case BTOR2_TAG_consth:
    case BTOR2_TAG_zero:
    case BTOR2_TAG_one:
    case BTOR2_TAG_ones:type = BTOR2_TAG_const;
      break;

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
    case BTOR2_TAG_add:
    case BTOR2_TAG_and:
    case BTOR2_TAG_concat:
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
    case BTOR2_TAG_read:
    case BTOR2_TAG_write:type = BTOR2_TAG_eq;
      break;

    default:type = BTOR2_TAG_not;
      break;
  }
  return type;
}

void transition(Btor2Parser *model, std::vector<bool> &vec) {
  int64_t number_of_lines = btor2parser_max_id(model);
  for (int64_t i = 1; i <= number_of_lines; ++i) {
    Btor2Line *line = btor2parser_get_line_by_id(model, i);
    if (!line) continue;

    Btor2Tag type = classification(line);
    if (type == BTOR2_TAG_constraint || type == BTOR2_TAG_eq
        || type == BTOR2_TAG_state) {
      for (int64_t j = 0; j < line->nargs; ++j) {
        int64_t args_id = labs(line->args[j]);
        vec[i] = vec[i] || vec[args_id];
      }
    }
  }
};

void open(const char *ername, const char *&path, FILE *&file, const char *default_path, FILE *default_file, bool op) {
  if (path) {
    if (!(file = fopen(path, op ? "r" : "w"))) {
      fprintf(stderr, "*** '%s' error: failed to open model file '%s' for %s\n",
              ername, path, op ? "reading" : "writing");
      exit(1);
    }
  } else {
    path = default_path;
    file = default_file;
  }
};

void print_line(const char *ername, FILE *output_file, Btor2Line *line) {
  fprintf(output_file, "%" PRId64 " %s", line->id, line->name);
  if (line->tag == BTOR2_TAG_sort) {
    fprintf(output_file, " %s", line->sort.name);
    switch (line->sort.tag) {
      case BTOR2_TAG_SORT_bitvec:fprintf(output_file, " %u", line->sort.bitvec.width);
        break;
      case BTOR2_TAG_SORT_array:
        fprintf(output_file,
                " %" PRId64 " %" PRId64,
                line->sort.array.index,
                line->sort.array.element);
        break;
      default:assert (0);
        fprintf(stderr, "*** %s: invalid sort encountered\n", ername);
        exit(1);
    }
  } else if (line->sort.id)
    fprintf(output_file, " %" PRId64, line->sort.id);
  for (uint32_t j = 0; j < line->nargs; j++) fprintf(output_file, " %" PRId64, line->args[j]);
  if (line->tag == BTOR2_TAG_slice) fprintf(output_file, " %" PRId64 " %" PRId64, line->args[1], line->args[2]);
  if (line->tag == BTOR2_TAG_sext || line->tag == BTOR2_TAG_uext)
    fprintf(output_file, " %" PRId64, line->args[1]);
  if (line->constant) fprintf(output_file, " %s", line->constant);
  if (line->symbol) fprintf(output_file, " %s", line->symbol);
  fputc('\n', output_file);
};

#endif //BTOR2TOOLS_SRC_BTORFUNC_H_
