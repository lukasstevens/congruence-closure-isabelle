#ifdef __cplusplus
extern "C" {
#endif

void* UFE_New(int n);
void UFE_Delete(void* thisC);

int UFE_find(void* thisC, int x);
void UFE_union(void* thisC, int x, int y);
void UFE_explain(void* thisC, int x, int y);

#ifdef __cplusplus
}
#endif