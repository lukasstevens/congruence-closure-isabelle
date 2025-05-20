#include "include/UFE_API.h"
#include "UFE.cpp"

void* UFE_New(int n) {
    try { return new UFE(n); }
    catch (...) { return nullptr; }
}

void UFE_Delete(void* thisC) {
    delete static_cast<UFE*>(thisC);
}

int UFE_find(void* thisC, int x) {
    UFE* ufe = static_cast<UFE*>(thisC);
    return ufe->find(x);
}

void UFE_union(void* thisC, int x, int y) {
    UFE* ufe = static_cast<UFE*>(thisC);
    return ufe->union_(x, y);
}

void UFE_explain(void* thisC, int x, int y) {
    UFE* ufe = static_cast<UFE*>(thisC);
    return ufe->explain(x, y);
}