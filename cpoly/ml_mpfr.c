/* $Id: ml_mpfr.c,v 1.1 2013-03-28 13:24:19 deraugla Exp $ */

#include <stdio.h>
#include <string.h>
#include <mpfr.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/intext.h>
#include <caml/alloc.h>

#define Mpfr_val(v) (*((mpfr_t **) Data_custom_val(v)))

static mpfr_t *alloc_mpfr(void)
{
  mpfr_t *x = (mpfr_t *)malloc(sizeof(mpfr_t));
  mpfr_init(*x);
  return x;
}

static mpfr_t *alloc_mpfr_prec(int prec)
{
  mpfr_t *x = (mpfr_t *)malloc(sizeof(mpfr_t));
  if (prec == 0) prec = mpfr_get_default_prec();
  mpfr_init2(*x, prec);
  return x;
}

static void finalize_mpfr(value v)
{
  mpfr_t *x = Mpfr_val(v);
  mpfr_clear(*x);
  free(x);
}

static struct custom_operations custom_mpfr_ops = {
  "mpfr",
  finalize_mpfr,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

static value caml_alloc_mpfr(mpfr_t *x)
{
  value v = alloc_custom(&custom_mpfr_ops, sizeof(mpfr_t *), 0, 1);
  Mpfr_val(v) = x;
  return v;
}

value ml_mpfr_with_prec(value prec_v, value x_v)
{
  CAMLparam2(prec_v, x_v);
  CAMLlocal1(r_v);
  int prec;
  mpfr_t *r, *x;
  prec = Long_val(prec_v);
  x = Mpfr_val(x_v);
  r = alloc_mpfr_prec(prec);
  mpfr_set(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_abs(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_abs(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_neg(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_neg(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_add(value x_v, value y_v)
{
  CAMLparam2(x_v, y_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x, *y;
  x = Mpfr_val(x_v);
  y = Mpfr_val(y_v);
  r = alloc_mpfr();
  mpfr_add(*r, *x, *y, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_sub(value x_v, value y_v)
{
  CAMLparam2(x_v, y_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x, *y;
  x = Mpfr_val(x_v);
  y = Mpfr_val(y_v);
  r = alloc_mpfr();
  mpfr_sub(*r, *x, *y, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_mul(value x_v, value y_v)
{
  CAMLparam2(x_v, y_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x, *y;
  x = Mpfr_val(x_v);
  y = Mpfr_val(y_v);
  r = alloc_mpfr();
  mpfr_mul(*r, *x, *y, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_mul_si(value x_v, value i_v)
{
  CAMLparam2(x_v, i_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_mul_si(*r, *x, Long_val(i_v), GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_sqr(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_sqr(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_div(value x_v, value y_v)
{
  CAMLparam2(x_v, y_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x, *y;
  x = Mpfr_val(x_v);
  y = Mpfr_val(y_v);
  r = alloc_mpfr();
  mpfr_div(*r, *x, *y, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_div_si(value x_v, value i_v)
{
  CAMLparam2(x_v, i_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_div_si(*r, *x, Long_val(i_v), GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_sqrt(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_sqrt(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_pow(value x_v, value y_v)
{
  CAMLparam2(x_v, y_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x, *y;
  x = Mpfr_val(x_v);
  y = Mpfr_val(y_v);
  r = alloc_mpfr();
  mpfr_pow(*r, *x, *y, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_exp(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_exp(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_log(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_log(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_cos(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_cos(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_sin(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *r, *x;
  x = Mpfr_val(x_v);
  r = alloc_mpfr();
  mpfr_sin(*r, *x, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_cmp(value x_v, value y_v)
{
  CAMLparam2(x_v, y_v);
  mpfr_t *x, *y;
  int r;
  x = Mpfr_val(x_v);
  y = Mpfr_val(y_v);
  r = mpfr_cmp(*x, *y);
  CAMLreturn(Val_long(r));
}

value ml_mpfr_to_string(value base_v, value n_v, value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  int base, n;
  mpfr_t *x;
  mp_exp_t exp;
  char *s;
  base = Long_val(base_v);
  n = Long_val(n_v);
  if (n <= 1) n = 0;
  x = Mpfr_val(x_v);
  s = mpfr_get_str(0, &exp, base, n, *x, GMP_RNDN);
  r_v = caml_alloc(2, 0);
  Store_field(r_v, 0, caml_copy_string(s));
  Store_field(r_v, 1, Val_long(exp));
  mpfr_free_str(s);
  CAMLreturn(r_v);
}

value ml_mpfr_of_string(value prec_v, value s_v)
{
  CAMLparam2(s_v, prec_v);
  CAMLlocal1(r_v);
  mpfr_t *r;
  int prec = Long_val(prec_v);
  r = alloc_mpfr_prec(prec);
  mpfr_set_str(*r, String_val(s_v), 10, GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_to_float(value x_v)
{
  CAMLparam1(x_v);
  CAMLlocal1(r_v);
  mpfr_t *x;
  double r;
  x = Mpfr_val(x_v);
  r = mpfr_get_d(*x, GMP_RNDN);
  r_v = caml_copy_double(r);
  CAMLreturn(r_v);
}

value ml_mpfr_of_float(value f_v)
{
  CAMLparam1(f_v);
  CAMLlocal1(r_v);
  mpfr_t *r;
  r = alloc_mpfr();
  mpfr_set_d(*r, Double_val(f_v), GMP_RNDN);
  r_v = caml_alloc_mpfr(r);
  CAMLreturn(r_v);
}

value ml_mpfr_get_prec(value x_v)
{
  CAMLparam1(x_v);
  mpfr_t *x = Mpfr_val(x_v);
  int prec = mpfr_get_prec(*x);
  CAMLreturn(Val_long(prec));
}

value ml_mpfr_set_default_prec(value prec_v)
{
  CAMLparam1(prec_v);
  CAMLlocal1(x_v);
  int prec = Long_val(prec_v);
  mpfr_t **p, *x;
  if (prec >= MPFR_PREC_MIN && prec <= MPFR_PREC_MAX) {
    mpfr_set_default_prec(prec);
  }
  CAMLreturn(Val_long(0));
}
