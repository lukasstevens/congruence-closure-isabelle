#include<vector>
#include<utility>
#include<algorithm>
#include<iostream>
#include<string>
#include<chrono>

using namespace std;

class UFE {
  public:
    vector<int> uf;
    vector<int> ufc;
    vector<int> au;
    vector< pair<int, int> > unions;

    UFE(int n) : uf(n, -1), ufc(n, -1), au(n, -1), unions() {}

    int find(int x) {
      int parent = this->ufc.at(x);
      if (parent < 0) {
        return x;
      } else {
        int rep_x = find(parent);
        this->ufc.at(x) = rep_x;
        return rep_x;
      }
    }

    void link(int x, int rep_x, int y, int rep_y, int sz) {
      this->uf.at(rep_x) = rep_y;
      this->ufc.at(rep_x) = rep_y;
      this->uf.at(rep_y) = -sz;
      this->ufc.at(rep_y) = -sz;
      this->au.at(x) = this->unions.size();
      this->unions.emplace_back(x, y);
    }

    void union_(int x, int y) {
      int rep_x = find(x);
      int rep_y = find(y);
      if (rep_x == rep_y) return;
      int size_x = -this->ufc.at(rep_x);
      int size_y = -this->ufc.at(rep_y);
      if (size_x < size_y) {
        link(x, rep_x, y, rep_y, size_x + size_y);
      } else {
        link(y, rep_y, x, rep_x, size_x + size_y);
      }
    }

    int find_newest_on_path(int x, int y) {
      int m = -1;
      while (x != y) {
        m = max(m, this->au.at(y));
        y = this->uf.at(y);
      }
      return m;
    }

    void awalk_from_rep(vector<int>& verts, int x) {
      while(x >= 0) {
        verts.push_back(x);
        x = this->uf.at(x);
      }
      return reverse(verts.begin(), verts.end());
    }

    int lca_of(int x, int y) {
      vector<int> walk_x;
      vector<int> walk_y; 
      awalk_from_rep(walk_x, x);
      awalk_from_rep(walk_y, y);
      size_t i;
      for (i = 0; i < min(walk_x.size(), walk_y.size()); ++i) {
        if (walk_x.at(i) != walk_y.at(i)) {
          break;
        }
      }
      return walk_x.at(i - 1);
    }

    void explain_aux(vector< pair<int, int> >& proof, int x, int y) {
      vector< pair<int, int> > q;
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
          pair<int, int> ax_bx = this->unions.at(newest_x);
          proof.push_back(ax_bx);
          q.emplace_back(x, get<0>(ax_bx));
          q.emplace_back(get<1>(ax_bx), y);
        } else {
          pair<int, int> ay_by = this->unions.at(newest_y);
          proof.push_back(ay_by);
          q.emplace_back(x, get<1>(ay_by));
          q.emplace_back(get<0>(ay_by), y);
        }
      }
    }

    void explain(int x, int y) {
      vector < pair<int, int> > proof;
      explain_aux(proof, x, y);
    }
};
