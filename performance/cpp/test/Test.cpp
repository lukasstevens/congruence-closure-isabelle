#include <iostream>
#include "../UFE.cpp"

int main() {
  int n = 1 << 18;
  UFE ufe(n);

  for (int i = 0; i < n - 1; ++i) {
    ufe.union_(i, i + 1);
  }
  //for (int i = 0; i < n; ++i) {
  //  std::cout << ufe.uf[i] << " ";
  //}
  //std::cout << std::endl;
  //for (int i = 0; i < n; ++i) {
  //  std::cout << ufe.ufc[i] << " ";
  //}
  //std::cout << std::endl;

  for (int i = 0; i < 1000; ++i) {
    std::vector< std::pair<int, int> > proof;
    ufe.explain_aux(proof, 0, n - 1);
  }
  //for (int i = 0; i < proof.size(); ++i) {
  //  std::cout << "(" << get<0>(proof[i]) << ", " << get<1>(proof[i]) << ") ";
  //}
  //std::cout << proof.size() << std::endl;
}
