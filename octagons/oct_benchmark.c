#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>
#include <sys/time.h>

extern long int lrand48(void);
extern void srand48(long int seedval);

#include "oct.h"
#include "oct_fun.h"
#include "oct_internal.h"

#include "../newpolka/pk.h"


ap_manager_t* mo; /* octagon */
ap_manager_t* mp; /* polyhedron */

oct_internal_t* pr;

typedef enum { none = 0, best = 1, exact = 2 } exactness;

exactness flag;
typedef enum  {
  expr_unary,
  expr_oct,
  expr_lin,
  expr_qlin,
  expr_interv,
} exprmode;

typedef enum {
  px = 0,
  mx = 1,
  pxpy = 2,
  pxmy = 3,
  mxpy = 4,
  mxmy = 5,
  
} oct_type;

typedef size_t var_t;

typedef struct {
  var_t x;
  var_t y;
  bound_t bound;
  oct_type type;
  
} oct_constraint;

oct_constraint* create_oct_constraint(var_t x, var_t y, bound_t d, oct_type type) {
  oct_constraint *o = (oct_constraint*) malloc(sizeof(oct_constraint));
  o->x = x; o->y=y; bound_set(o->bound, d); o->type = type;
  return o;
}

void init_random(void) {
  srand(0);
  rand();
  return;
}

void flip_constraint(oct_constraint* o) {

  bound_t tmp;
  switch(o->type) {
  case px:
    o->type = mx;
    bound_init(tmp);
    bound_neg(tmp, o->bound);
    bound_set(o->bound, tmp);
    bound_clear(tmp);
    return;
  case mx:
    o->type = px;
    bound_init(tmp);
    bound_neg(tmp, o->bound);
    bound_set(o->bound, tmp);
    bound_clear(tmp);
    return;
  case pxpy:
    o->type=mxmy;
    bound_init(tmp);
    bound_neg(tmp, o->bound);
    bound_set(o->bound, tmp);
    bound_clear(tmp);
    return;
  case pxmy:
    o->type=mxpy;
    bound_init(tmp);
    bound_neg(tmp, o->bound);
    bound_set(o->bound, tmp);
    bound_clear(tmp);
    return;
  case mxpy:
    o->type=pxmy;
    bound_init(tmp);
    bound_neg(tmp, o->bound);
    bound_set(o->bound, tmp);
    bound_clear(tmp);
    return;
  case mxmy:
    o->type = pxpy;
    bound_init(tmp);
    bound_neg(tmp, o->bound);
    bound_set(o->bound, tmp);
    bound_clear(tmp);
    return;
  }
}

oct_constraint* create_constraint(int numvars) {

  // init_random();
  unsigned int x = rand() % ((numvars-1)-0 + 1) + 0;
  unsigned int y = rand() % ((numvars-1) - 0 + 1) + 0;

  
  bound_t bound;
  bound_init(bound);

  num_t n;
  num_init(n);

  int max = 10;
  int min = -10;
  
  int b = min + rand() / (RAND_MAX / (max - min +1) + 1);

  num_set_double(n, (double) b);
  bound_set_num(bound,n);

  var_t type = (var_t) (rand() % (5 - 0 + 1) + 0);
  
  oct_constraint* o = (oct_constraint*) malloc(sizeof(oct_constraint));
  o->type=type;
  o->x = x;
  o->y = y;
  bound_init(o->bound);
  bound_set(o->bound, bound);
  
  if(bound_sgn(bound) < 0) {
    flip_constraint(o);
  }

  bound_clear(bound);
  num_clear(n);
  return o;
}

void add_constraint_dbm(oct_constraint* o, dbm* m, int size) {
  int i,j,i1,j1;
  double d;

  int x = o->x;
  int y = o->y;
  
  bound_t tmp;
  switch(o->type) {
  case px:
    i = 2*x;
    j = 2*x + 1;
    bound_init(tmp);
    bound_mul_2(tmp, o->bound);
    setdbm(m, matpos2(i,j), tmp);
    bound_clear(tmp);
    return;
    
  case mx:
    i = 2*x + 1;
    j = 2*x;
    bound_init(tmp);
    bound_mul_2(tmp, o->bound);
    setdbm(m, matpos2(i,j), tmp);
    bound_clear(tmp);
    return;

  case pxpy:
    i = 2*x;
    j = 2*y+1;
    setdbm(m, matpos2(i,j), o->bound);
    return;

  case pxmy:
    i = 2*x;
    j = 2*y;
    setdbm(m, matpos2(i,j), o->bound);
    return;

  case mxpy:
    i = 2*y;
    j = 2*x;
    setdbm(m, matpos2(i,j), o->bound);
    return;

  case mxmy:
    i = 2*x +1;
    j = 2*y;
    setdbm(m, matpos2(i,j), o->bound);
    return;
  default:
    i = 2*x;
    j = 2*y+1;
    setdbm(m, matpos2(i,j), o->bound);
    return;

  }
}


ap_lincons0_t generate_lincons_from_oct_constraint(oct_constraint* o) {
  size_t x = o->x;
  size_t y = o->y;
  bound_t tmp;
  bound_init(tmp);
  int i, j;
  switch(o->type) {
  case px:
    i = 2*x;
    j = 2*x + 1;
    bound_mul_2(tmp, o->bound);
    break;
    
  case mx:
    i = 2*x + 1;
    j = 2*x;
    bound_mul_2(tmp, o->bound);
    break;
  case pxpy:
    i = 2*x;
    j = 2*y+1;
    bound_set(tmp,o->bound);
    break;

  case pxmy:
    i = 2*x;
    j = 2*y;
    bound_set(tmp,o->bound);
    break;

  case mxpy:
    i = 2*y;
    j = 2*x;
    bound_set(tmp,o->bound);
    break;

  case mxmy:
    i = 2*x +1;
    j = 2*y;
    bound_set(tmp, o->bound);
    break;

  default:
    i = 2*x;
    j = 2*y+1;
    bound_set(tmp,o->bound);
    break;
  }
  return lincons_of_bound(pr, i,j,tmp);
  
}

oct_t* random_oct(int dim, int numc) 
{
  oct_t* o = oct_alloc_internal(pr,dim,0);
  bound_t* b;
  int i,j,x,y;
  num_t n;
  num_t n1;
  o->m = hmat_alloc_top(pr,dim);
  oct_constraint *newconstraint;
  for(int i=0; i<numc; i++) {
    newconstraint = create_constraint(dim);
    add_constraint_dbm(newconstraint, o->m, dim);
  }

  return o;
}


ap_linexpr0_t* random_linexpr(exprmode mode, int dim)
{
  ap_linexpr0_t* l = ap_linexpr0_alloc(AP_LINEXPR_DENSE,dim);
  int i,n1,n2,d;
  if (mode<=expr_oct) {
    if (lrand48()%10>2)
      ap_coeff_set_scalar_int(l->p.coeff+(lrand48()%dim),lrand48()%3-1);
    if (mode==expr_oct)
      if (lrand48()%10>2)
	ap_coeff_set_scalar_int(l->p.coeff+(lrand48()%dim),lrand48()%3-1);
  }
  else if (mode<=expr_qlin) {
    for (i=0;i<dim;i++)
      ap_coeff_set_scalar_frac(l->p.coeff+i,lrand48()%20-10,lrand48()%4+1);
  }
  else {
    for (i=0;i<dim;i++) {
      int n1 = lrand48()%20-10;
      int n2 = n1 + lrand48()%20;
      int d  = lrand48()%4+1;
      ap_coeff_set_interval_frac(l->p.coeff+i,n1,d,n2,d);
    }
  }
  if (mode<=expr_lin) {
    ap_coeff_set_scalar_frac(&l->cst,lrand48()%20-10,lrand48()%4+1);
  }
  else {
    int n1 = lrand48()%20-10;
    int n2 = n1 + lrand48()%20;
    int d  = lrand48()%4+1;
    ap_coeff_set_interval_frac(&l->cst,n1,d,n2,d);
  }
  return l;
}

/* chose one linexpr within an interval linexpr */
ap_linexpr0_t* random_from_linexpr(ap_linexpr0_t* a)
{
  size_t i;
  ap_linexpr0_t* l = ap_linexpr0_alloc(AP_LINEXPR_DENSE,a->size);
  assert(a->discr==AP_LINEXPR_DENSE);
  for (i=0;i<a->size;i++) {
    switch (a->p.coeff[i].discr) {
    case AP_COEFF_SCALAR:
      ap_coeff_set_scalar(l->p.coeff+i,a->p.coeff[i].val.scalar);
      break;
    case AP_COEFF_INTERVAL:
      if (lrand48()%2)
	ap_coeff_set_scalar(l->p.coeff+i,a->p.coeff[i].val.interval->inf);
      else 
	ap_coeff_set_scalar(l->p.coeff+i,a->p.coeff[i].val.interval->sup);
      break;
      
    }
  }
  switch (a->cst.discr) {
  case AP_COEFF_SCALAR:
    ap_coeff_set_scalar(&l->cst,a->cst.val.scalar);
    break;
  case AP_COEFF_INTERVAL:
    if (lrand48()%2) ap_coeff_set_scalar(&l->cst,a->cst.val.interval->inf);
    else ap_coeff_set_scalar(&l->cst,a->cst.val.interval->sup);
    break;
    
  }
  return l;
}

ap_lincons0_t random_from_lincons(ap_lincons0_t a)
{
  return ap_lincons0_make(a.constyp,random_from_linexpr(a.linexpr0),NULL);
}


double test_close(size_t dim, size_t nb) {
  //  pr = oct_init_from_manager(mo,0,0);
  for (int i=0;i<AP_FUNID_SIZE;i++) {
    mo->option.funopt[i].flag_exact_wanted = true;
    mo->option.funopt[i].flag_best_wanted = true;
  }
  struct timeval t1, t2;

  size_t i;

  exprmode mode = expr_oct;

  oct_t *o, *o1;
  ap_abstract0_t *p;

  o = random_oct(dim, nb );

#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "BEFORE TEST o\n");
  oct_fdump(stdout, mo, o);
#endif


  gettimeofday(&t1,0);
  oct_close(pr,o);
  gettimeofday(&t2,0);


#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "AFTER TEST o\n");
  oct_fdump(stdout, mo, o);
#endif

  double time_singlethread = (1000000.0*(t2.tv_sec-t1.tv_sec) + t2.tv_usec-t1.tv_usec)/1000000.0;
  if(!o-> closed && !o->m) {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_UNSAT\n", dim, nb, time_singlethread);
  } else {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_SAT\n", dim, nb, time_singlethread);
  }
  
  oct_free(mo,o);
  return time_singlethread;
}

double test_join(size_t dim, size_t nb) {
  pr = oct_init_from_manager(mo,0,0);
  for (int i=0;i<AP_FUNID_SIZE;i++) {
    mo->option.funopt[i].flag_exact_wanted = true;
    mo->option.funopt[i].flag_best_wanted = true;
  }
  struct timeval t1, t2;

  size_t i;

  exprmode mode = expr_oct;

  oct_t *o, *o1;
  ap_abstract0_t *p;

  o = random_oct(dim, nb );
#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "BEFORE TEST o\n");
  oct_fdump(stdout, mo, o);
#endif
  oct_close(pr,o);

  o1 = random_oct(dim, nb);
#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "BEFORE TEST o1\n");
  oct_fdump(stdout, mo, o1);
#endif
  oct_close(pr, o1);

  gettimeofday(&t1,0);
  o1 = oct_join(mo, false, o, o1);
  gettimeofday(&t2,0);

#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "AFTER TEST\n");
  oct_fdump(stdout, mo, o1);
#endif

  double time_singlethread = (1000000.0*(t2.tv_sec-t1.tv_sec) + t2.tv_usec-t1.tv_usec)/1000000.0;
  if(!o1-> closed && !o1->m) {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_UNSAT\n", dim, nb, time_singlethread);
  } else {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_SAT\n", dim, nb, time_singlethread);
  }
  
  oct_free(mo,o);
  oct_free(mo,o1);
  return time_singlethread;
}


double test_meet(size_t dim, size_t nb) {
  pr = oct_init_from_manager(mo,0,0);
  for (int i=0;i<AP_FUNID_SIZE;i++) {
    mo->option.funopt[i].flag_exact_wanted = true;
    mo->option.funopt[i].flag_best_wanted = true;
  }
  struct timeval t1, t2;

  size_t i;

  exprmode mode = expr_oct;

  oct_t *o, *o1;
  ap_abstract0_t *p;

  o = random_oct(dim, nb );
  oct_close(pr,o);

  o1 = random_oct(dim, nb);
  oct_close(pr, o1);

  gettimeofday(&t1,0);
  o1 = oct_meet(mo, false, o, o1);
  gettimeofday(&t2,0);

#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "AFTER TEST\n");
  oct_fdump(stdout, mo, o1);
#endif

  double time_singlethread = (1000000.0*(t2.tv_sec-t1.tv_sec) + t2.tv_usec-t1.tv_usec)/1000000.0;
  if(!o1-> closed && !o1->m) {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_UNSAT\n", dim, nb, time_singlethread);
  } else {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_SAT\n", dim, nb, time_singlethread);
  }
  
  oct_free(mo,o);
  oct_free(mo,o1);
  return time_singlethread;
}



double test_meetlincons(size_t dim, size_t nb) {

  pr = oct_init_from_manager(mo,0,0);
  for (int i=0;i<AP_FUNID_SIZE;i++) {
    mo->option.funopt[i].flag_exact_wanted = true;
    mo->option.funopt[i].flag_best_wanted = true;
  }
  struct timeval t1, t2;

  size_t i;

  exprmode mode = expr_oct;

  oct_t *o, *o1;
  ap_abstract0_t *p;

  o = random_oct(dim, nb );
  oct_close(pr,o);

  double time_singlethread ;
  ap_lincons0_array_t ar = ap_lincons0_array_make(nb);
  int go = rand() %2;
  if(go) {
    for (i=0;i<nb;i++) {
      ar.p[i] = ap_lincons0_make((lrand48()%100>=50)?AP_CONS_EQ:
				 (lrand48()%100>=50)?AP_CONS_SUP:
				 AP_CONS_SUPEQ,
				 random_linexpr(mode,dim),
				 NULL);
    }
  } else {
    for (i=0;i<nb;i++) {
      oct_constraint* newc = create_constraint(dim);
      ar.p[i] = generate_lincons_from_oct_constraint(newc);
    }
  }

#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "BEFORE TEST\n");
  oct_fdump(stdout, mo, o);
#endif

  gettimeofday(&t1,0);
  o1 = oct_meet_lincons_array(mo, false, o, &ar);
  gettimeofday(&t2,0);
  ap_lincons0_array_clear(&ar);

#if defined(BENCHMARKDEBUG)
  fprintf(stdout, "AFTER TEST\n");
  oct_fdump(stdout, mo, o1);
#endif

  time_singlethread = (1000000.0*(t2.tv_sec-t1.tv_sec) + t2.tv_usec-t1.tv_usec)/1000000.0;
  if(!o1-> closed && !o1->m) {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_UNSAT\n", dim, nb, time_singlethread);
  } else {
    fprintf(stderr, "Dimension: %3zu Num new constraints: %3zu Time: %3.8f FINAL_SAT\n", dim, nb, time_singlethread);
  }
  
  oct_free(mo,o);
  oct_free(mo,o1);
  return time_singlethread;
}

void run_experiment(double (*test_func)(size_t dim, size_t nb)) {
  mo = oct_manager_alloc();
  if(!mo) return;

  size_t numreps = 10;
  double sum = 0.0;

  size_t initdim = 5;
  size_t maxdim = 50;
  size_t dimstep = 10;
  
  int seed = 10;
  srand(seed);

  for(size_t i=initdim; i<=maxdim; i+=dimstep) {
    for(size_t numc = 1; numc<=10; numc++) {
      //for(size_t numc = 5; numc<=2*i; numc+=10) {
      sum = 0.0;
      for(size_t j=0; j<numreps; j++) {
	sum += test_func(i, numc);
      }
      fprintf(stderr, "Dim: %zu Numc: %zu AVG: %f\n", i, numc, sum/numreps);
      fprintf(stderr, "--------------------------------------------------------------------------\n");
    }
  }
  ap_manager_free(mo);
}

int main(int argc, const char** argv) {
  if(argc <= 1) {
    printf("No options provided\n");
    return 0;
  }

  if(strcmp(argv[1], "join") == 0) {
    run_experiment(&test_join);
  } else if (strcmp(argv[1], "meet") == 0) {
    run_experiment(&test_meet);
  } else if (strcmp(argv[1], "lincons") == 0) {
    run_experiment(&test_meetlincons);
  } else if (strcmp(argv[1], "close") == 0) {
    run_experiment(&test_close);
  }
  
  return 0;
}
