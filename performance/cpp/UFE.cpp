#include<vector>
#include<utility>
#include<algorithm>
#include<iostream>
#include<string>
#include<chrono>

// The Isabelle code export for arrays uses an initial capacity of 16
#define INITIAL_CAPACITY 16

using namespace std;

class UFE {
  #ifdef CPP_FAST
  private:
    vector <int> walk_x;
    vector <int> walk_y;
  #endif
  public:
    vector<int> uf;
    vector<int> ufc;
    vector<int> au;
    vector< pair<int, int> > unions;

    UFE(int n) : uf(n, -1), ufc(n, -1), au(n, -1), unions() {
      this->unions.reserve(INITIAL_CAPACITY);
      #ifdef CPP_FAST
      this->walk_x.reserve(INITIAL_CAPACITY);
      this->walk_y.reserve(INITIAL_CAPACITY);
      #endif
    }

    int find(int x) {
      int parent = this->ufc[x];
      if (parent < 0) {
        return x;
      } else {
        int rep_x = find(parent);
        this->ufc[x] = rep_x;
        return rep_x;
      }
    }

    void link(int x, int rep_x, int y, int rep_y, int sz) {
      this->uf[rep_x] = rep_y;
      this->ufc[rep_x] = rep_y;
      this->uf[rep_y] = -sz;
      this->ufc[rep_y] = -sz;
      this->au[x] = this->unions.size();
      this->unions.emplace_back(x, y);
    }

    void union_(int x, int y) {
      int rep_x = find(x);
      int rep_y = find(y);
      if (rep_x == rep_y) return;
      int size_x = -this->ufc[rep_x];
      int size_y = -this->ufc[rep_y];
      if (size_x < size_y) {
        link(x, rep_x, y, rep_y, size_x + size_y);
      } else {
        link(y, rep_y, x, rep_x, size_x + size_y);
      }
    }

    int find_newest_on_path(int x, int y) {
      int m = -1;
      while (x != y) {
        m = max(m, this->au[y]);
        y = this->uf[y];
      }
      return m;
    }

    void awalk_from_rep(vector<int>& verts, int x) {
      while(x >= 0) {
        verts.push_back(x);
        x = this->uf[x];
      }
    }

    int lca_of(int x, int y) {
      #ifdef CPP_FAST
      this->walk_x.resize(0);
      this->walk_y.resize(0);
      #else
      vector<int> walk_x;
      walk_x.reserve(INITIAL_CAPACITY);
      vector<int> walk_y;
      walk_y.reserve(INITIAL_CAPACITY);
      #endif
      awalk_from_rep(walk_x, x);
      awalk_from_rep(walk_y, y);
      int lca = walk_x.back();
      while (!walk_x.empty() && !walk_y.empty() && walk_x.back() == walk_y.back()) {
        lca = walk_x.back();
        walk_x.resize(walk_x.size() - 1);
        walk_y.resize(walk_y.size() - 1);
      }
      return lca;
    }

    void explain_aux(vector< pair<int, int> >& proof, int x, int y) {
      vector< pair<int, int> > q;
      q.reserve(INITIAL_CAPACITY);
      q.emplace_back(x, y);
      while (!q.empty()) {
        int x = get<0>(q.back());
        int y = get<1>(q.back());
        q.pop_back();
        if (x == y) continue;
        int lca = lca_of(x, y);
        int newest_x = find_newest_on_path(lca, x);
        int newest_y = find_newest_on_path(lca, y);
        if (newest_x >= newest_y) {
          pair<int, int> ax_bx = this->unions[newest_x];
          proof.push_back(ax_bx);
          q.emplace_back(x, get<0>(ax_bx));
          q.emplace_back(get<1>(ax_bx), y);
        } else {
          pair<int, int> ay_by = this->unions[newest_y];
          proof.push_back(ay_by);
          q.emplace_back(x, get<1>(ay_by));
          q.emplace_back(get<0>(ay_by), y);
        }
      }
    }

    void explain(int x, int y) {
      vector < pair<int, int> > proof;
      proof.reserve(INITIAL_CAPACITY);
      int rep_x = find(x);
      int rep_y = find(y);
      if (rep_x != rep_y) return;
      explain_aux(proof, x, y);
    }
};
