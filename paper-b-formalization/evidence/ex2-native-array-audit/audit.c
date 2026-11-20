#include <lean/lean.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void lean_initialize_runtime_module(void);
lean_object *initialize_paperB_PaperB_ForestOrderRank(uint8_t);
lean_object *lp_paperB_PaperB_ForestPreparedBuild_buildWordsFromOrder___redArg(lean_object*,lean_object*);

typedef struct {const char *file; int line; uint64_t events, cells;} CopySite;
static CopySite sites[128];
static size_t siteCount;
static int filming;
static uint64_t writes, pushes, copiedCells, growthCells;
static void observe(lean_object *a, const char *file, int line, int push) {
    if (!filming) return;
    size_t length = lean_array_size(a);
    if (push) {
        ++pushes;
        if (length == lean_array_capacity(a)) growthCells += length;
    } else ++writes;
    if (lean_is_exclusive(a) || length == 0) return;
    copiedCells += length;
    size_t i = 0;
    while (i < siteCount && (sites[i].line != line || strcmp(sites[i].file,file))) ++i;
    if (i == siteCount) {
        if (i == sizeof sites / sizeof *sites) abort();
        sites[i] = (CopySite){file,line,0,0};
        ++siteCount;
    }
    ++sites[i].events;
    sites[i].cells += length;
}
lean_object *audit_fset(lean_object *a, lean_object *i, lean_object *v, const char *f, int l) {
    observe(a,f,l,0); return lean_array_fset(a,i,v);
}
lean_object *audit_set(lean_object *a, lean_object *i, lean_object *v, const char *f, int l) {
    observe(a,f,l,0); return lean_array_set(a,i,v);
}
lean_object *audit_uset(lean_object *a, size_t i, lean_object *v, const char *f, int l) {
    observe(a,f,l,0); return lean_array_uset(a,i,v);
}
lean_object *audit_push(lean_object *a, lean_object *v, const char *f, int l) {
    observe(a,f,l,1); return lean_array_push(a,v);
}

static lean_object *arcs(lean_object *tail, size_t u, size_t v, size_t copies) {
    for (size_t j=0; j<copies; ++j) {
        lean_object *arc = lean_alloc_ctor(0,2,0);
        lean_ctor_set(arc,0,lean_box(v)); lean_ctor_set(arc,1,lean_box(u));
        lean_object *item = lean_alloc_ctor(1,2,0);
        lean_ctor_set(item,0,arc); lean_ctor_set(item,1,tail); tail=item;
    }
    return tail;
}
static void exercise(size_t k, int ladder, size_t multiplicity) {
    size_t n = 2*k + (ladder != 0), m = 0;
    lean_object *order = lean_mk_empty_array_with_capacity(lean_box(n));
    lean_object *adj = lean_mk_empty_array_with_capacity(lean_box(n));
    for (size_t u=0; u<n; ++u) {
        lean_object *xs=lean_box(0);
        if (ladder) {
            size_t v = u == 0 ? 1 : 3 + 2*((u-1)/2);
            if (v+1 < n) {
                xs=arcs(xs,u,v+1,multiplicity);
                xs=arcs(xs,u,v,multiplicity);
                m+=2*multiplicity;
            }
        } else if (u == 0) {
            for (size_t v=k; v>0; --v) xs=arcs(xs,u,v,multiplicity);
            m+=k*multiplicity;
        } else if (u<=k) {
            if (u<k) { xs=arcs(xs,u,k+u,multiplicity); m+=multiplicity; }
            if (1<u) { xs=arcs(xs,u,k+u-1,multiplicity); m+=multiplicity; }
        }
        order=lean_array_push(order,lean_box(u)); adj=lean_array_push(adj,xs);
    }
    lean_object *h=lean_alloc_ctor(0,4,0);
    lean_ctor_set(h,0,lean_box(n)); lean_ctor_set(h,1,lean_box(n));
    lean_ctor_set(h,2,lean_box(0)); lean_ctor_set(h,3,adj);
    writes=pushes=copiedCells=growthCells=0; siteCount=0; filming=1;
    lean_object *out=lp_paperB_PaperB_ForestPreparedBuild_buildWordsFromOrder___redArg(h,order);
    filming=0;
    if (lean_obj_tag(out)!=1) { fprintf(stderr,"expected packed output\n"); abort(); }
    size_t dict=lean_array_size(lean_ctor_get(lean_ctor_get(out,0),0));
    size_t expected=1+3*(k-1);
    if (dict!=expected) { fprintf(stderr,"expected %zu dictionary words, got %zu\n",expected,dict); abort(); }
    printf("%s n=%zu m=%zu dict=%zu writes=%" PRIu64 " pushes=%" PRIu64 " shared_cells=%" PRIu64 " growth_cells=%" PRIu64 "\n",
           ladder ? "ladder" : "adjacent-hubs",n,m,dict,writes,pushes,copiedCells,growthCells);
    for (size_t i=0; i<siteCount; ++i)
        printf("  %s:%d shared events=%" PRIu64 " cells=%" PRIu64 "\n",
               sites[i].file,sites[i].line,sites[i].events,sites[i].cells);
    lean_dec(out);
}
int main(void) {
    lean_initialize_runtime_module();
    lean_object *res=initialize_paperB_PaperB_ForestOrderRank(1);
    if (lean_io_result_is_error(res)) { lean_io_result_show_error(res); return 1; }
    lean_dec(res);
    lean_io_mark_end_initialization();
    for (size_t k=32; k<=8192; k*=4) {
        exercise(k,0,1);
        exercise(k,1,3);
    }
    return 0;
}
