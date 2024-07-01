//
// Created by CSHwang on 2024/3/27.
//

#ifndef BTOR2TOOLS_SRC_RANDOMAIGER_TWOSAT_H_
#define BTOR2TOOLS_SRC_RANDOMAIGER_TWOSAT_H_

#include <cstdio>
#include <climits>
#include <cstdlib>
#include <cstring>
#include <cinttypes>

#include <stack>
#include <vector>
#include <cassert>
#include <algorithm>

/*------------------------------------------------------------------------*/

enum TwoSatTag {
  NOTVISIT,
  INSTACK,
  FINISH
};

namespace TwoSAT {

struct UnionSet {
  std::vector<uint> fa;
  UnionSet() = default;
  explicit UnionSet(int n) {
    fa.resize(n);
    for (int i = 0; i < n; ++i) fa[i] = i;
  }

  void resize(int n) {
    fa.resize(n);
    for (int i = 0; i < n; ++i) fa[i] = i;
  }
  uint findset(uint x) { return fa[x] == x ? x : (fa[x] = findset(fa[x])); }
  void merge(uint x, uint y) {
    int fx = findset(x), fy = findset(y);
    fa[fy] = fx;
  }

  ~UnionSet() = default;
};

UnionSet set;
int timestamp, cnt;
std::stack<int> sta;
static std::vector<uint> node;
static std::vector<TwoSatTag> state;
static std::vector<std::vector<uint>> eg;
static std::vector<int> dfn, low, col, mapping;

void initialize(int n) {
  set.resize(n);
  mapping.resize(n, -1);
  eg.resize(n, std::vector<uint>(0));
}
void add_edge(FILE *log_file, uint x, uint y) {
  if ((x ^ y) == 1) {
    node.emplace_back(x);
    node.emplace_back(y);
    eg[x].push_back(y);
    set.merge(x, y);
  } else {
    node.emplace_back(x);
    node.emplace_back(x ^ 1);
    node.emplace_back(y);
    node.emplace_back(y ^ 1);

    eg[x].push_back(y ^ 1);
    eg[y].push_back(x ^ 1);
    set.merge(x, y ^ 1);
    set.merge(y, x ^ 1);

    fprintf(log_file, "[randomaiger] preprocessing: (%u & %u) must equal to 0\n", x, y);
  }
}
void tarjan(int x) {
  sta.push(x);
  state[x] = INSTACK;
  dfn[x] = low[x] = ++timestamp;

  for (auto y : eg[node[x]]) {
    y = mapping[y];
    if (state[y] == FINISH) continue;
    if (state[y] == NOTVISIT) {
      tarjan(y);
      low[x] = std::min(low[x], low[y]);
    } else low[x] = std::min(low[x], dfn[y]);
  }

  if (low[x] == dfn[x]) {
    ++cnt;

    int tmp;
    do {
      tmp = sta.top();
      sta.pop();
      state[tmp] = FINISH;
      col[tmp] = cnt;
    } while (tmp != x);
  }
}
std::vector<uint> solve() {
  std::sort(node.begin(), node.end());
  node.erase(std::unique(node.begin(), node.end()), node.end());
  for (int i = 0; i < node.size(); ++i) mapping[node[i]] = i;

  timestamp = cnt = 0;
  dfn.resize(node.size());
  low.resize(node.size());
  col.resize(node.size());
  state.resize(node.size(), NOTVISIT);

  for (int i = 0; i < node.size(); ++i) if (!state[i]) tarjan(i);

  // 2SAT: find a feasible solution
  std::vector<uint> choose;
  for (int i = 0; i < node.size(); i += 2) {
    int x = node[i], y = node[i ^ 1];
    assert(col[i] != col[i ^ 1]);
    if (col[i] > col[i ^ 1]) choose.emplace_back(y);
    else choose.emplace_back(x);
  }
  return choose;
}

};

#endif //BTOR2TOOLS_SRC_RANDOMAIGER_TWOSAT_H_
