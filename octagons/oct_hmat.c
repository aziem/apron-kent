/*
 * oct_hmat.c
 *
 * Half-matrices - Basic management.
 *
 * APRON Library / Octagonal Domain
 *
 * Copyright (C) Antoine Mine' 2006
 *
 */

/* This file is part of the APRON Library, released under LGPL license
   with an exception allowing the redistribution of statically linked
   executables.

   Please read the COPYING file packaged in the distribution.
*/

#include <stdlib.h>
#include <fcntl.h>
#include <math.h>
#include "oct.h"
#include "oct_internal.h"
#include "logging.h"
#include <assert.h>


/* We consider matrices of 2n*2n upper bounds.
   Let us denote by (i,j) the matrix element at line i, column j; the matrix
   induces the following constraints:
     Vj-Vi <= (2i,2j)
     Vj+Vi <= (2i+1,2j)
    -Vj-Vi <= (2i,2j+1)
    -Vj+Vi <= (2i+1,2j+1)

   Actually, this representation is redudant, and so, we manipulate 
   2x2 block lower-triangular matrices. 
   Only elements (i,j) such that j/2 <= i/2 are represented:

       j ->  0 1 2 3 4 5
            ___
        0  |_|_|
        1  |_|_|___
  i ->  2  |_|_|_|_|
        3  |_|_|_|_|___
        4  |_|_|_|_|_|_|
        5  |_|_|_|_|_|_|

                 
                 j
             0     -2x0
            2x0      0
       i
           x0-x1  -x0-x1      0   -2x1
           x0+x1  -x0+x1     2x1    0


   Elements such that j/2 > i/2 are retreived by coherence: (i,j) = (j^1,i^1)
*/


/* alloced but not initialized */

#define CACHESIZE 20000
#define A ((sqrt(5) - 1) * 0.5)
#define MEMORY_MODEL __ATOMIC_SEQ_CST

typedef struct element 
{
  short hash;
  short index;
} element;

element pairs[CACHESIZE];

bound_t values[CACHESIZE];

bound_t boundtmps[2];

static volatile short dbmnext = 0;

void setinfty(dbm* d, size_t index);
void setzero(dbm* d, size_t index);

void printvalues() {
  fprintf(stderr, "==================================================\n");
  for(int i=0; i<CACHESIZE; i++) {
    if(pairs[i].hash != -1) {
      fprintf(stderr, "%d -> [%d] -> ", i, pairs[i].index);
      bound_fprint(stderr, values[pairs[i].index]);
      fprintf(stderr, "\n");
    }
  }
  fprintf(stderr, "==================================================\n");
}

short multiplication_hash(bound_t num) {
  double v = bound_to_double2(num);
  double s = v * A;
  double frac = s - (int) s;

  if(frac < 0) {
    frac = 1.0d + frac;
  }
  short hash = (short)(CACHESIZE * frac);
  return hash;
}

short insertlinearprobing(bound_t num, short index) {
  unsigned int i = 0;
  int j = 0;

  short hash = multiplication_hash(num);
  short expected = -1;
  j=hash;

  do {
    if(pairs[j].hash == -1) {
      pairs[j].index = index;
      pairs[j].hash = hash;
      return index;
    } else {
      i = i+1;
      j = (j+1) % CACHESIZE;
    }
  } while(i < CACHESIZE);
  return -1;
}

element* searchlinearprobing(bound_t num) {
  unsigned int i = 0;
  short j = multiplication_hash(num);

  do {
    short hash = pairs[j].hash;
    if(hash == -1) {
      return NULL;
    }

    short index = pairs[j].index;
    if(bound_equal(values[index], num)) {
      return &pairs[j];
    }
    i++;
    j=(j+1) % CACHESIZE;

  } while(i < CACHESIZE && pairs[j].hash != -1);

  return NULL;
}

void inithashtable(void) {
  for(long i=0; i<CACHESIZE; i++) {
    pairs[i].hash = -1;
  }
}


void initcache(void) {
  inithashtable();
  assert(dbmnext == 0);
  bound_t zero, one, infty;
  bound_init(zero);
  bound_init(one); 
  bound_init(infty);
  bound_init(boundtmps[0]);
  bound_init(boundtmps[1]);
  
  bound_set_int(zero, 0);
  bound_set_int(one, 1);
  bound_set_infty(infty, 1);
  
  bound_set(values[0], zero);
  bound_set(values[1], one);
  bound_set(values[2], infty);
  
  insertlinearprobing(zero, 0);
  insertlinearprobing(one, 1);
  insertlinearprobing(infty, 2);
  
  dbmnext = 3;
}

void clearcache(void) {
  dbmnext = 0;
}


#if defined(DBMCACHE)
inline dbm* hmat_alloc(oct_internal_t* pr, size_t dim)
{
  dbm* d;
  d = (dbm*) malloc(sizeof(dbm));
  short* r;
  size_t sz = matsize(dim);
  if (!sz) sz = 1; /* make sure we never malloc a O-sized block */
  checked_malloc(r,short,sz,return NULL;); 
  d->m = r;
  return d;
}

inline void hmat_free(oct_internal_t* pr, dbm* d, size_t dim)
{
  free(d->m);
  free(d);
}

/* all variables are initialized to 0 */
inline dbm* hmat_alloc_zero(oct_internal_t* pr, size_t dim)
{
  size_t i;
  dbm* d = hmat_alloc(pr,dim);
  for (i=0;i<matsize(dim);i++) setzero(d,i);
  return d;
}

/* all variables are initialized to "don't know" */
inline dbm* hmat_alloc_top(oct_internal_t* pr, size_t dim)
{
  size_t i;
  dbm* d = hmat_alloc(pr,dim);
  for (i=0;i<matsize(dim);i++) setinfty(d,i); 
  for (i=0;i<2*dim;i++) setzero(d,matpos(i,i)); 
  return d;
}
#else
inline dbm* hmat_alloc(oct_internal_t* pr, size_t dim)
{
  dbm* d;
  d = (dbm*) malloc(sizeof(dbm));
  bound_t* r;
  size_t sz = matsize(dim);
  if (!sz) sz = 1; /* make sure we never malloc a O-sized block */
  checked_malloc(r,bound_t,sz,return NULL;);
  bound_init_array(r,matsize(dim));
  d->m = r;
  return d;
}

inline void hmat_free(oct_internal_t* pr, dbm* d, size_t dim)
{
  bound_clear_array(d->m,matsize(dim));
  free(d->m);
  free(d);
}

/* all variables are initialized to 0 */
inline dbm* hmat_alloc_zero(oct_internal_t* pr, size_t dim)
{
  size_t i;
  dbm* d = hmat_alloc(pr,dim);
  for (i=0;i<matsize(dim);i++) bound_set_int(*getdbm(d,i),0);
  return d;
}

/* all variables are initialized to "don't know" */
inline dbm* hmat_alloc_top(oct_internal_t* pr, size_t dim)
{
  size_t i;
  dbm* d = hmat_alloc(pr,dim);
  for (i=0;i<matsize(dim);i++) bound_set_infty(*getdbm(d,i),1);
  for (i=0;i<2*dim;i++) bound_set_int(*getdbm(d,matpos(i,i)),0);
  return d;
}
#endif

void hmat_fdump(FILE* stream, oct_internal_t* pr, dbm* d, size_t dim)
{
  size_t i,j;
  for (i=0;i<2*dim;i++) {
    for (j=0;j<=(i|1);j++) {
      if (j) fprintf(stream," ");
      bound_fprint(stream,*getdbm(d, matpos2(i, j)));
    }
    fprintf(stream,"\n");
  }
}
inline dbm* hmat_copy(oct_internal_t* pr, dbm* m, size_t dim)
{
  if (m) {
    dbm* d = hmat_alloc(pr,dim);
    size_t i;
    for(i=0; i<matsize(dim); i++) {
      setdbm(d,i, *getdbm(m,i));
    }
    return d;
  }
  else {
    return NULL;
  }
}

short dbm_insert(bound_t new)
{
  /* pthread_mutex_lock(&mutex); */
  element* elem = searchlinearprobing(new);
  if(elem == NULL) {
    elem = searchlinearprobing(new);

    if(elem == NULL) {
      short new_index = insertlinearprobing(new, dbmnext);
      if(new_index == -1 ) {
	// hashtable full
	return 2; // return infinity
      } else {
	bound_set(values[dbmnext], new);
	__atomic_add_fetch(&dbmnext, 1, MEMORY_MODEL);
	//dbmnext++;
	//dbmnext &= CACHESIZE-1;
	return new_index;
      }
    } else {
      return elem->index;
    }
  } else {
    return elem->index;
  }
}

short dbm_insert_seq(bound_t new)
{

  element* elem = searchlinearprobing(new);
  if(elem == NULL) {
    short new_index = insertlinearprobing(new, dbmnext);
    if(new_index == -1) {
      return 2;
    } else {
      bound_set(values[dbmnext], new);
      dbmnext++;
      return new_index;
    }
  } else {
    return elem->index;
  }
}

#if defined(DBMCACHE)

inline void setinfty(dbm* d, size_t index) {
  d->m[index] = 2;
}

inline void setzero(dbm* d, size_t index) {
  d->m[index] = 0;
}
#endif

#if defined(DBMCACHE)

inline bool is_my_infty(dbm* d, size_t index) {
  return d->m[index] == 2;
}

inline void myadd(bound_t res, bound_t b, bound_t temp, dbm* d, size_t index1, size_t index2) {
  bool b1 = d->m[index1] == 2;
  bool b2 = d->m[index2] == 2;
  if(b1 && b2) {
    bound_set(res, values[2]);
  } else if(b1 && !b2) {
    bound_add(res, values[d->m[index2]], temp);
  } else if(!b1 && b2) {
    bound_add(res, values[d->m[index1]], b);
  } else {
    bound_add(boundtmps[0], values[d->m[index1]], b);
    bound_add(boundtmps[1], values[d->m[index2]], temp);
    bound_min(res, boundtmps[0], boundtmps[1]);
  }
}

inline void myadd2(bound_t res, bound_t b, short index1) {
  bound_add(res, b, values[index1]);
}

// Intended to be used from in a thread
inline void setdbm_thd(dbm* d, size_t k, bound_t new) {
   if(bound_infty(new)) {
     d->m[k]=2;
     return;
   }
  int value_index = dbm_insert(new); 
  d->m[k] = value_index;
}

// Intended to be used in a seq setting
inline void setdbm(dbm* d, size_t k, bound_t new) {
   if(bound_infty(new)) {
     d->m[k]=2;
     return;
   }
  int value_index = dbm_insert_seq(new); 
  d->m[k] = value_index;
}

void setdbminfty(dbm* d, size_t k) {
  d->m[k] = 2;
}

void setdbmzero(dbm* d, size_t k) {
   d->m[k] = 0;
}

void setdbmmin(dbm* d, size_t k, bound_t b1, bound_t b2) {
  bound_t tmp; bound_init(tmp);
  bound_min(tmp, b1, b2);
  setdbm(d, k, tmp);
}

void mysetdbmmax(dbm* d, size_t i, dbm* m1, dbm* m2) {
  short m1_index = m1->m[i];
  short m2_index = m2->m[i];

  // 2 is the index of infinity
  if(m1_index == 2 || m2_index == 2) {
    d->m[i] = 2;
  } else if(m1_index == m2_index) {
    d->m[i] = m1_index;
  } else if(bound_cmp(values[m1_index], values[m2_index]) > 0) {
    d->m[i] = m1_index;
  } else {
    d->m[i] = m2_index;
  }
}
#else
inline bool is_my_infty(dbm* d, size_t index) {
  return bound_infty(d->m[k]);
}

inline void setdbm(dbm* d, size_t k, bound_t new) {
  bound_set(d->m[k], new);
}

inline void setdbminfty(dbm* d, size_t k) {
  bound_set_infty(*getdbm(d,k), 1);
}

inline void setdbmzero(dbm* d, size_t k) {
  bound_set_int(*getdbm(d,k), 0);
}

void setdbmmin(dbm* d, size_t k, bound_t b1, bound_t b2) {
  bound_t tmp; bound_init(tmp);
  bound_min(tmp, b1, b2);
  setdbm(d, k, tmp);
}
#endif

void setdbmbmin_thd(dbm* d, size_t k, bound_t b) {
  if(bound_cmp(*getdbm(d,k), b) > 0) {
    setdbm_thd(d,k,b);
  }
}

void setdbmbmin(dbm* d, size_t k, bound_t new) {
  if(bound_cmp(*getdbm(d,k), new) > 0) {
    setdbm(d,k,new);
  }
}

void setdbmbmax(dbm* d, size_t k, bound_t b) {
  if(bound_cmp(*getdbm(d,k), b) < 0) {
    setdbm(d,k,b);
  }
}

void setdbmmax(dbm* d, size_t k, bound_t b1, bound_t b2) {
  bound_t tmp; bound_init(tmp);
  bound_max(tmp, b1, b2);
  setdbm(d,k,tmp);
}

void setdbmadd(dbm* d, size_t k, bound_t b1, bound_t b2) {
  bound_t tmp; bound_init(tmp);
  bound_add(tmp, b1, b2);
  setdbm(d,k,tmp);
}

void setdbmsub(dbm* d, size_t k, bound_t b1, bound_t b2) {
  bound_t tmp; bound_init(tmp);
  bound_sub(tmp, b1,b2);
  setdbm(d,k,tmp);
}

void setdbmbadd(dbm* d, size_t k, bound_t b) {
  bound_t tmp; bound_init(tmp);
  bound_set(tmp, *getdbm(d,k));
  bound_badd(tmp,b);
  setdbm(d ,k, tmp);
}

void setdbm_mul_2(dbm* d, size_t k, bound_t b) {
  bound_t tmp; bound_init(tmp);
  bound_mul_2(tmp, b);
  setdbm(d,k,tmp);
}


void setdbm_div_2(dbm* d, size_t k, bound_t b) {
  bound_t tmp; bound_init(tmp);
  bound_div_2(tmp, b);
  setdbm(d,k,tmp);
}


#if defined(DBMCACHE)
inline bound_t* getdbm(dbm* d, size_t k) {
  return &values[d->m[k]];
}

inline bound_t* getvalue(size_t k) {
  return &values[k];
}
#else
inline bound_t* getdbm(dbm* d, size_t k) {
  return (d->m)+k;
}
#endif 

inline void dbm_set_array(dbm* dst, dbm* src, size_t size) {
  size_t k;
  for(k=0; k<size; k++) {
    setdbm(dst, k, *getdbm(src, k));
  }
}

inline void dbm_set_array_from_point(dbm* dst, dbm* src, size_t point, size_t point2,size_t size) {
  size_t k;
  for(k=0; k<size; k++) {
    setdbm(dst, point+k, *getdbm(src, point2+k));
  }

}

inline void dbm_bound_set_array(bound_t* dst, dbm* src, size_t size) {
  size_t k;
  for(k=0; k<size; k++) {
    bound_set(dst[k], *getdbm(src,k));
  }
}

inline void dbm_bound_set_array2(dbm* dst, bound_t* src, size_t size) {
  size_t k;
  for(k=0; k<size; k++) {
    setdbm(dst,k, src[k]);
  }
}

inline size_t dbm_serialized_size_array(dbm* src, size_t size) {
  size_t i, n=0;
  for(i=0; i<size; i++) {
    n+= bound_serialized_size(*getdbm(src, i));
  }
  return n;
}

inline size_t dbm_serialize_array(void* dst, dbm* src, size_t size) {
  size_t i,n=0;
  for (i=0;i<size;i++)
    n += bound_serialize((char*)dst+n,*getdbm(src,i));
  return n;
}

inline size_t dbm_deserialize_array(dbm* dst, const void *src, size_t size) {
  size_t i,n=0;
  for (i=0;i<size;i++)
    n += bound_deserialize(*getdbm(dst,i),(const char*)src+n);
  return n;
}
