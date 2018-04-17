#include "oct.h"
#include "oct_internal.h"

bool incrstrongclosure_seq(bound_t* m, size_t dim, size_t a, size_t b, bound_t d) {
  size_t i,j;
  size_t bara = a^1;
  size_t barb = b^1;


  // redundancy check
  if (bound_cmp(d, m[matpos2(a,b)]) >= 0) {
    return false;
  }

  // sat check
  // m_{b,a} + d < 0
  // m_{bara, barb} < 0 (no need by coherence)
  // m_{bara,a} + d + m_{b,barb} + d < 0

  bound_t temp1; bound_init(temp1);
  bound_t temp2; bound_init(temp2);
  bound_t temp3; bound_init(temp3);
  bound_t temp4; bound_init(temp4);
  bound_t temp5; bound_init(temp5);
  bound_t temp6; bound_init(temp6);

  bound_t temp7; bound_init(temp7);
  bound_t temp8; bound_init(temp8);
 
  bound_add(temp1, m[matpos2(b,a)], d);
  bound_add(temp2, m[matpos2(bara,a)], d);
  bound_badd(temp2, m[matpos2(b,barb)]);
  bound_badd(temp2, d);
  
  if ((bound_sgn(temp1) < 0) || (bound_sgn(temp2) < 0)) {
    return true;
  }

  bound_t twod; bound_init(twod);
  bound_mul_2(twod, d);
 
  bound_add(temp1, twod, m[matpos2(bara,a)]);
  bound_add(temp2, twod, m[matpos2(b,barb)]);


  bound_t ia; bound_init(ia);
  bound_t ibarb; bound_init(ibarb);

  bound_t bbari; bound_init(bbari);
  bound_t barabari; bound_init(barabari);
  // incremental strong closure loop
  for(i=0; i<2*dim; i++) {

    bound_set(ia, m[matpos2(i,a)]);
    bound_set(ibarb, m[matpos2(i,barb)]);
    bound_set(bbari, m[matpos2(b, i^1)]);
    bound_set(barabari, m[matpos2(bara,i^1)]);

    bound_add(temp3, ia, d);
    bound_badd(temp3, bbari);

    bound_add(temp4, ibarb, d);
    bound_badd(temp4, barabari);
    bound_bmin(temp4, temp3);

    bound_add(temp3, ibarb, temp1);
    bound_badd(temp3, bbari);
    bound_bmin(temp4, temp3);

    bound_add(temp3, ia, temp2);
    bound_badd(temp3, barabari);
    bound_bmin(temp4, temp3);

    bound_bmin(m[matpos(i, i^1)], temp4);
  }

  bound_clear(bbari);
  bound_clear(barabari);

  // closure loop
  for(i=0; i<2*dim; i++) {

    bound_set(ia, m[matpos2(i,a)]);
    bound_set(ibarb, m[matpos2(i,barb)]);

    bound_add(temp5, ia, d);
    bound_add(temp3, ibarb, temp1);
    bound_min(temp3, temp5, temp3);

    bound_add(temp5, ibarb, d);
    bound_add(temp4, ia, temp2);
    bound_min(temp4, temp5, temp4);
    bound_div_2(temp7, m[matpos(i,i^1)]);
    for(j=0; j<=(i|1); j++) {
	bound_add(temp5, temp3, m[matpos2(b,j)]);
	bound_add(temp6, temp4, m[matpos2(bara,j)]);
	
	bound_bmin(temp6, temp5);
	
	// ibari
	// barjj
	bound_div_2(temp8, m[matpos(j^1,j)]);
	// (ibari+barjj)/2
	bound_badd(temp8, temp7);
	bound_bmin(temp6, temp8);
	
	bound_bmin(m[matpos2(i,j)], temp6);
    }
  }

  bound_clear(temp1);
  bound_clear(temp2);
  bound_clear(temp3);
  bound_clear(temp4);
  bound_clear(temp5);
  bound_clear(temp6);
  bound_clear(temp7);
  bound_clear(temp8);
  bound_clear(twod);
  bound_clear(ia);
  bound_clear(ibarb);

  return false;
  //return hmat_s_step(m, dim);

}

bool unary_inequality_incrstrongclosure(bound_t* m, size_t dim, size_t a, bound_t d) {

  size_t i,j;
  size_t bara = a^1;

  // redundancy ccheck
  if (bound_cmp(d, m[matpos2(a,bara)]) >= 0) {
    return false;
  }

  bound_t ij, ia, ibara;

  bound_t tmp; bound_init(tmp);
  bound_add(tmp, d, m[matpos2(bara,a)]);

  if (bound_sgn(tmp) < 0) {
    bound_clear(tmp);
    return true;
  }

  bound_init(ia);
  // strong closure loop
  for(i=0; i<2*dim; i++) {
    bound_set(ia, m[matpos2(i,a)]);
    bound_badd(ia,d);
    bound_badd(ia, m[matpos2(a^1,i^1)]);
    bound_bmin(m[matpos(i,i^1)], ia);
  }
  
  bound_init(ij);

  bound_t temp2, temp3;
  bound_init(temp2);
  bound_init(temp3);

  // closure loop
  for(i=0; i<2*dim; i++) {
    bound_set(ia, m[matpos2(i,a)]);
    bound_badd(ia, d);
    for(j=0; j<=(i|1); j++) {
      bound_add(ij, ia, m[matpos2(bara,j)]);
      bound_div_2(temp2, m[matpos(i,i^1)]);
      bound_div_2(temp3, m[matpos(j^1,j)]);
      bound_add(tmp, temp2, temp3);
      bound_bmin(ij, tmp);
      bound_bmin(m[matpos2(i,j)], ij);
    }
  }

  bound_clear(ij);
  bound_clear(ia);
  bound_clear(tmp);
  bound_clear(temp2);
  bound_clear(temp3);

  return false;
  // return hmat_s_step(m,dim);
}


bool unary_equality_incrstrongclosure(bound_t* m, size_t dim, size_t a, bound_t d, bound_t dprime ) {
  size_t i, j;
  size_t bara = a^1;

  if (bound_cmp(d, m[matpos2(a,bara)]) >= 0 && bound_cmp(dprime, m[matpos2(bara,a)]) >= 0) {
    return false;
  }

  bound_t ij, ia, ibara;

  bound_t tmp, tmp2;
  bound_init(tmp);
  bound_init(tmp2);

  bound_add(tmp, d, m[matpos2(bara,a)]);
  bound_add(tmp2, dprime, m[matpos2(a,bara)]);
  if ((bound_sgn(tmp) < 0) || (bound_sgn(tmp2) < 0)) {
    bound_clear(tmp);
    bound_clear(tmp2);
    return true;
  }

  bound_init(ij);
  bound_init(ia);
  bound_init(ibara);

  // strong closure loop
  for(i=0; i<2*dim; i++) {
    bound_set(ia, m[matpos2(i,a)]);
    bound_set(ibara, m[matpos2(i,bara)]);
    bound_badd(ia, d);
    bound_badd(ibara, dprime);
    bound_add(ij, ia, m[matpos2(bara,i^1)]);
    bound_set(tmp, ij);
    bound_add(ij, ibara,m[matpos2(a,i^1)]);
    bound_bmin(tmp, ij);
    bound_bmin(m[matpos2(i,i^1)], tmp);
  }

  bound_t temp3, temp4;
  bound_init(temp3);
  bound_init(temp4);
  
  // closure loop
  for(i=0; i<2*dim; i++) {
    bound_set(ia, m[matpos2(i,a)]);
    bound_set(ibara, m[matpos2(i,bara)]);
    bound_badd(ia, d);
    bound_badd(ibara, dprime);
    for(j=0; j<=(i|1); j++)  {
      bound_add(ij, ia, m[matpos2(bara,j)]);
      bound_set(tmp, ij);
      bound_add(ij, ibara,m[matpos2(a,j)]);
      bound_bmin(tmp, ij);

      bound_div_2(temp3, m[matpos(i,i^1)]);
      bound_div_2(temp4, m[matpos(j^1, j)]);
      bound_add(tmp2, temp3, temp4);
      bound_bmin(tmp, tmp2);
      
      bound_bmin(m[matpos2(i,j)], tmp);
    }
  }

  bound_clear(ij);
  bound_clear(ia);
  bound_clear(ibara);
  bound_clear(tmp);
  bound_clear(tmp2);
  bound_clear(temp3);
  bound_clear(temp4);

  return false;
  //  return hmat_s_step(m,dim);
}


