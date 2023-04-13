/*
Tor Myklebust's function approximation heuristic
Copyright (C) 2014-2015 Tor Myklebust (tmyklebu@csclub.uwaterloo.ca)

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

/*
Roughly eyeballed performance numbers:

Baseline:
  Time: 622.171875s
Memory: 3168MB

Fewer redundant expressions:
  Time: 460.390625s
Memory:  566MB

Improved getbounds
  Time: 453.671875s
Memory:  566MB

Removed unused variables
  No change.

Stopped recreating the exprs vector every time.
  Time: 423.609375s
Memory:  553MB

Made all Intervals inclusive
  Time: 362.593750s
Memory: 553MB

Added Interval datatype
  Time: 368.312500s
Memory: 553MB

Moved vector con- and destruction out of the dive loops
  Time: 375.875000s
Memory: 553MB

*/

#include <stdio.h>
#include <assert.h>
#include <float.h>
#include <math.h>
#include <queue>
#include <algorithm>
#include <sys/types.h>
#include <sys/resource.h>
#include <gmpxx.h>
#include <vector>
extern "C" {
#include <QSopt_ex.h>
}
using namespace std;

struct Interval {
  float lower, upper;
};


#define FOR(i,n) for (int i=0;i<(signed int)(n);i++)

long long get_cpu_usecs() {
 rusage r;
 getrusage(RUSAGE_SELF, &r);
 return            r.ru_utime.tv_usec
     + 1000000LL * r.ru_utime.tv_sec;
}

long long program_start;

// Wrapper class for a QSopt_ex rational linear program.
struct lp_t {
  mpq_QSprob prob;
  int nvar;
  int nextrow;

  lp_t(int nvar, const Interval *iv) : nvar(nvar) {
    nextrow = 0;
    prob = mpq_QScreate_prob("funapprox", QS_MIN);
    FOR(i,nvar) {
      mpq_class zero = 0;
      mpq_class l = iv[i].lower, h = iv[i].upper;
      mpq_QSnew_col(prob, zero.get_mpq_t(), l.get_mpq_t(), h.get_mpq_t(), 0);
    }
  }

  ~lp_t() {
    mpq_QSfree_prob(prob);
  }

  mpq_class solve() {
    int stat;
    if (QSexact_solver(prob, 0, 0, 0, DUAL_SIMPLEX, &stat)) {
      printf("solve failed\n");
      throw ":(";
    }
    if (stat != QS_LP_OPTIMAL) {
      throw ":(";
    }
    mpq_t foo;
    mpq_init(foo);
    mpq_QSget_objval(prob, &foo);
    mpq_class ans = mpq_class(foo);
    mpq_clear(foo);
    return ans;
  }

  void set_objective(vector<mpq_class> obj) {
    FOR(i, nvar) mpq_QSchange_objcoef(prob, i, obj[i].get_mpq_t());
  }

  void introduce_row(vector<mpq_class> lhs, char kind, mpq_class rhs) {
    mpq_QSnew_row(prob, rhs.get_mpq_t(), kind, 0);
    FOR(i, nvar)
      mpq_QSchange_coef(prob, nextrow, i, lhs[i].get_mpq_t());
    nextrow++;
  }
};

// Find all `x` such that `lb <= fma(x, y, z) <= ub`.  The output is the
// interval `[lo, hi]`.
//
// The implementation of this function is quite savage.  It could profitably be
// replaced by a couple of binary searches.  However, this implementation works
// and I'm not too keen on touching it.
Interval reverse_fmaf(float y, float z, Interval d) {
  if (y < 0) {
    y = -y;
    z = -z;
    d = { -d.upper, -d.upper };
  }

  float lo = -FLT_MAX, hi = FLT_MAX;
  while (nextafterf(lo, hi) < hi) {
    float c = lo/2 + hi/2;   // This BS is bad for floats.
    float cc = fmaf(c, y, z);
    if (cc < d.lower) lo = nextafterf(c, 1.0/0.0);
    else hi = c;
  }
  lo = nextafterf(lo, -1.0/0.0);
  lo = nextafterf(lo, -1.0/0.0);
  assert(fmaf(lo, y, z) < d.lower);
  while (fmaf(lo, y, z) < d.lower) lo = nextafterf(lo, 1.0/0.0);
  hi = lo;
  #define STEPIT(step) while (hi + (float)step != hi && fmaf(hi+(float)step, y, z) < d.upper) hi = hi + (float)step;
  for (int zzz = 0; zzz < 3; zzz++) {
    STEPIT(0x1.0p+120)
    STEPIT(0x1.0p+110)
    STEPIT(0x1.0p+100)
    STEPIT(0x1.0p+90)
    STEPIT(0x1.0p+80)
    STEPIT(0x1.0p+70)
    STEPIT(0x1.0p+60)
    STEPIT(0x1.0p+50)
    STEPIT(0x1.0p+45)
    STEPIT(0x1.0p+40)
    STEPIT(0x1.0p+35)
    STEPIT(0x1.0p+30)
    STEPIT(0x1.0p+25)
    STEPIT(0x1.0p+20)
    STEPIT(0x1.0p+15)
    STEPIT(0x1.0p+10)
    STEPIT(0x1.0p+5)
    STEPIT(0x1.0p+0)
    STEPIT(0x1.0p-5)
    STEPIT(0x1.0p-10)
    STEPIT(0x1.0p-15)
    STEPIT(0x1.0p-20)
    STEPIT(0x1.0p-25)
    STEPIT(0x1.0p-30)
    STEPIT(0x1.0p-35)
    STEPIT(0x1.0p-40)
    STEPIT(0x1.0p-45)
    STEPIT(0x1.0p-50)
    STEPIT(0x1.0p-55)
    STEPIT(0x1.0p-60)
    STEPIT(0x1.0p-65)
    STEPIT(0x1.0p-70)
    STEPIT(0x1.0p-80)
    STEPIT(0x1.0p-90)
    STEPIT(0x1.0p-100)
    STEPIT(0x1.0p-110)
    STEPIT(0x1.0p-120)
  }
  #undef STEPIT
  while (fmaf(hi, y, z) <= d.upper) hi = nextafterf(hi, 1.0/0.0);
  hi = nextafterf(hi, -1.0/0.0);
  assert(d.lower <= fmaf(           lo,            y, z));
  assert(           fmaf(           hi,            y, z) <= d.upper);
  assert(           fmaf(nextafterf(lo, -1.0/0.0), y, z) <  d.lower);
  assert(d.upper <  fmaf(nextafterf(hi,  1.0/0.0), y, z));

  return { lo, hi };
}

// A node in a straight-line program that only has constants, variables, and
// fused multiply-adds.
struct expression {
  int tag;
  union {
    float val;
    int varno;
    struct { expression *a, *b, *c; };
  };

  Interval getbounds(const Interval *x) {
    switch (tag) {
      case 0: return { val, val};
      case 1: return x[varno];
      case 2: {
        Interval ia = a->getbounds(x);
        Interval ib = b->getbounds(x);
        Interval ic = c->getbounds(x);
        float v1 = fmaf(ia.lower, ib.lower, ic.lower);
        float v2 = fmaf(ia.upper, ib.lower, ic.lower);
        float v3 = fmaf(ia.lower, ib.upper, ic.lower);
        float v4 = fmaf(ia.upper, ib.upper, ic.lower);
        float v5 = fmaf(ia.lower, ib.lower, ic.upper);
        float v6 = fmaf(ia.upper, ib.lower, ic.upper);
        float v7 = fmaf(ia.lower, ib.upper, ic.upper);
        float v8 = fmaf(ia.upper, ib.upper, ic.upper);
        return {
          min(min(v1, v2), min(v3, v4)),
          max(max(v5, v6), max(v7, v8))
        };
      }
      default: abort();
    }
  }

  static expression *con(float f) {
    expression *e = new expression();
    e->tag = 0;
    e->val = f;
    return e;
  }

  static expression *var(int k) {
    expression *e = new expression();
    e->tag = 1;
    e->varno = k;
    return e;
  }

  static expression *fma(expression *a, expression *b, expression *c)  {
    expression *e = new expression();
    e->tag = 2;
    e->a = a; e->b = b; e->c = c;
    return e;
  }
};

expression *subs(expression *e, int varno, float value) {
  switch (e->tag) {
    case 1: {
      if (e->varno == varno) return expression::con(value);
    } break;
    case 2: {
      expression *a2 = subs(e->a, varno, value),
                 *b2 = subs(e->b, varno, value),
                 *c2 = subs(e->c, varno, value);

      if (a2->tag == 0 && b2->tag == 0 && c2->tag == 0)
        return expression::con(fmaf(a2->val, b2->val, c2->val));

      if (a2 != e->a || b2 != e->b || c2 != e->c)
        return expression::fma(a2, b2, c2);
    } break;
  }
  return e;
}

float eval(expression *e, float *x) {
  switch (e->tag) {
    case 0: return e->val;
    case 1: return x[e->varno];
    case 2: return fmaf(eval(e->a, x), eval(e->b, x), eval(e->c, x));
    default: abort();
  }
}


float half_ulp(float x) {
  x = fabs(x);
  return (nextafterf(x, 1.0/0.0) - x) / 2;
}

// Compute the range `[lower, upper]` of acceptable function values at `x`.
//
// Hack this function, and `main()` below, if you'd like to do something
// other than approximate `tan(x)` on `(10^{-4}, pi/4)` within `0.999` ulp.
static double ulps_wrong = 0.999;
Interval get_bounds(float x) {
  double d = tan((double)x);
  float ulp = 2 * half_ulp((float)d);
  double lo = d - ulps_wrong * ulp, up = d + ulps_wrong * ulp;
  float lower = lo, upper = up;
  if (lower < lo) lower = nextafterf(lower, 1.0/0.0);
  if (upper > up) upper = nextafterf(upper, -1.0/0.0);
  return { lower, upper };
}

// Given a straight-line program `e` and bounds
// `[clb_0, cub_0] x ... x [clb_{nvar-1}, cub_{nvar-1}]` on the unspecified
// coefficients in `e`, this function computes an upper bound on the roundoff
// error incurred when evaluating `e` in `float` arithmetic.
mpq_class get_max_roundoff(expression *e, const Interval *cb) {
  switch (e->tag) {
    case 0: return 0;
    case 1: return 0;
    case 2: {
      Interval ia = e->a->getbounds(cb);
      Interval ib = e->b->getbounds(cb);
      Interval ie = e->getbounds(cb);
      float abound = max(fabs(ia.lower), fabs(ia.upper));
      float bbound = max(fabs(ib.lower), fabs(ib.upper));
      float ebound = max(fabs(ie.lower), fabs(ie.upper));
      mpq_class around = get_max_roundoff(e->a, cb);
      mpq_class bround = get_max_roundoff(e->b, cb);
      mpq_class cround = get_max_roundoff(e->c, cb);
      return half_ulp(ebound) + cround + bbound * around + abound * bround;
    }
    default: abort();
  }
}

// Returns the (rational) coefficients of the linear polynomial represented by
// the straight-line program `e`; `poly` gets the degree-1 terms and `con` gets
// the constant term.
//
// Each `fma` encountered by this function must have the form
// `fma(constant, x, y)` or `fma(x, constant, y)` where `x` and `y` are
// arbitrary.  If an `fma` encountered does not have this form, this function
// calls `abort()`.  Further, if `e` contains a variable for which `poly` does
// not have a corresponding index, undefined behaviour results.
void get_linear_poly(expression *e, vector<mpq_class> &poly, mpq_class &con) {
  FOR(i, poly.size()) poly[i] = 0;
  con = 0;
  switch (e->tag) {
    case 0: con = e->val; return;
    case 1: poly[e->varno] = 1; return;
    case 2: {
      vector<mpq_class> cp(poly.size());
      mpq_class cc;
      get_linear_poly(e->c, cp, cc);
      float constant;
      if (e->a->tag == 0) {
        constant = e->a->val;
        get_linear_poly(e->b, poly, con);
      } else if (e->b->tag == 0) {
        constant = e->b->val;
        get_linear_poly(e->a, poly, con);
      } else abort();
      FOR(i,poly.size()) poly[i] = constant * poly[i] + cp[i];
      con = constant * con + cc;
      return;
    }
    default: abort();
  }
}

// Peel back fma(const, f, const) -> f using reverse_fma.
// Now we have an expression tree and some bounds on the value it must take.
// Convert the expression tree to an inequality pair.
void peel_bounded_expression(expression *&e, Interval &iv) {
  while (e->tag == 2 && e->c->tag == 0
         && (e->a->tag == 0 || e->b->tag == 0)) {
    if (e->a->tag == 0 && e->b->tag == 0) abort();
    float cee = e->c->val, bee;
    if (e->a->tag == 0) bee = e->a->val;
    else if (e->b->tag == 0) bee = e->b->val;
    else abort();
    iv = reverse_fmaf(bee, cee, iv);
    if (e->a->tag == 0) e = e->b; else e = e->a;
  }
}

// This function does the dirty work of `gen_inequalities` below.
void gen_inequalities_inner(expression *e, Interval iv, int nvar, const Interval *cb, lp_t *lp) {
  peel_bounded_expression(e, iv);

  vector<mpq_class> poly(nvar); mpq_class con;
  get_linear_poly(e, poly, con);

  mpq_class err = get_max_roundoff(e, cb);
  mpq_class rhslo = iv.lower - con - err;
  mpq_class rhsup = iv.upper - con + err;

  lp->introduce_row(poly, 'G', rhslo);
  lp->introduce_row(poly, 'L', rhsup);
}

// Given a straight-line program `e`, the number of unspecified coefficients
// `nvar`, bounds `[clb_0, cub_0] x ... x [clb_{nvar-1}, cub_{nvar-1}]` on the
// unspecified coefficients, and a test point `x`, add two inequalities to the
// linear program `lp` that provably must be satisfied by the unspecified
// coefficients.  These inequalities are derived by considering evaluation at
// the test point `x`.
void gen_inequalities(expression *e, int nvar, const Interval *cb, float x, lp_t *lp) {
  expression *ee = subs(e, -1, x);
  Interval iv = get_bounds(x);
  gen_inequalities_inner(ee, iv, nvar, cb, lp);
}

// Compute lower and upper bounds on variable `varno` implied by the polyhedron
// defined by the constraints of `lp`.  Outputs a range `[lower, upper]`.
Interval get_var_bounds(lp_t *lp, int varno) {
  vector<mpq_class> obj(lp->nvar);
  obj[varno] = 1; lp->set_objective(obj);
  mpq_class lo = lp->solve();
  obj[varno] = -1; lp->set_objective(obj);
  mpq_class up = -lp->solve();
  float lower = lo.get_d(); // XXX Possible double-rounding anomaly?
  float upper = up.get_d(); // XXX Possible double-rounding anomaly?
  while (lower < lo) lower = nextafterf(lower,  1.0/0.0);
  while (up < upper) upper = nextafterf(upper, -1.0/0.0);
  return { lower, upper };
}

// Bias guesses toward the centre of the interval.
// There is probably a better distribution.
double randpt() {
  return (drand48() + drand48()) / 2;
}

// This is the body of the diving heuristic.
vector<float> dive(int nvar, const Interval *cb,
    const vector<pair<expression *, Interval>> &ineqs,
    const vector<float> &preferred, int tries = 8) {
  if (nvar == 0) return vector<float>();
  lp_t lp(nvar, cb);
  FOR(i, ineqs.size()) {
    gen_inequalities_inner(ineqs[i].first, ineqs[i].second, nvar, cb, &lp);
  }
  Interval a = get_var_bounds(&lp, nvar-1);

  double num_ulps = (cb[nvar-1].upper - cb[nvar-1].lower)
      / half_ulp(max(fabs(cb[nvar-1].lower), fabs(cb[nvar-1].upper)));
  printf("%a\n", num_ulps);

  vector<pair<expression *, Interval>> new_ineqs = ineqs;
  if (num_ulps > tries) {
    FOR(zzz, tries) {
      float f = randpt() * (a.upper - a.lower) + a.lower;
      if (zzz == 0 && preferred[nvar-1] >= a.lower && preferred[nvar-1] <= a.upper)
        f = preferred[nvar-1];
      FOR(i, ineqs.size())
        new_ineqs[i].first = subs(ineqs[i].first, nvar-1, f);
      try {
        vector<float> ans = dive(nvar-1, cb, new_ineqs, preferred);
        ans.push_back(f);
        return ans;
      } catch (const char *) {}
    }
  } else {
    for (float f = cb[nvar-1].lower; f <= cb[nvar-1].upper; f = nextafterf(f, 1.0/0.0)) {
      FOR(i, ineqs.size())
        new_ineqs[i].first = subs(ineqs[i].first, nvar-1, f);
      try {
        vector<float> ans = dive(nvar-1, cb, new_ineqs, preferred, 100);
        ans.push_back(f);
        return ans;
      } catch (const char *) {}
    }
  }
  throw ":(";
}

// Given a straight-line program `e`, an interval `[xlb, xub]` of `float`s, and
// a list `c` of coefficients, find at least one point `x` at which `e` with
// coefficients `c` yields an unacceptable function value.
int find_cuts(expression *e, Interval xb, const vector<float> &c, vector<float> &testpoints) {
  float foo[c.size()+1];
  FOR(i, c.size()) foo[i+1] = c[i];
  int found = 0;
  FOR(i, 1000000) {
    float x = xb.lower + drand48() * (xb.upper - xb.lower);
    foo[0] = x;
    float fx = eval(e, foo+1);
    Interval b = get_bounds(x);
    if (fx < b.lower || fx > b.upper) testpoints.push_back(x), found++;
    if (found) return found;
  }
  for (float x = xb.upper; x >= xb.lower && !found; x = nextafterf(x, -1.0/0.0)) {
    foo[0] = x;
    float fx = eval(e, foo+1);
    Interval b = get_bounds(x);
    if (fx < b.lower || fx > b.upper) testpoints.push_back(x), found++;
  }
  return found;
}

// Driver for the heuristic.  Given a straight-line program `e`, the number of
// unspecified coefficients `nvar`, an interval `[xlb, xub]` of `float`s,
// bounds `[clb_0, cub_0] x ... x [clb_{nvar-1}, cub_{nvar-1}]` on the
// unspecified coefficients, and a nonempty vector `testpoints` of test points,
// try to find coefficients that yield an acceptable approximation.
int findit(expression *e, int nvar, Interval xb, Interval *cb, vector<float> &testpoints) {
  vector<float> coeffs(nvar);
  vector<pair<expression *, Interval>> exprs;
  while (1) {
    try {
      lp_t lp(nvar, cb);
      FOR(i, testpoints.size()) {
        gen_inequalities(e, nvar, cb, testpoints[i], &lp);
      }
      FOR(i, nvar) {
        cb[i] = get_var_bounds(&lp, i);
      }
      FOR(i, nvar) printf("%.6a <= c%i <= %.6a\n", cb[i].lower, i, cb[i].upper);
    } catch (const char *) { return -2; } // infeasible.

    {
      float t = testpoints[testpoints.size() - 1];
      exprs.push_back(make_pair(subs(e, -1, t), get_bounds(t)));
    }
    try {
      coeffs = dive(nvar, cb, exprs, coeffs, 50);
    } catch (const char *) { return -1; } // infeasible or too hard to solve.
    printf("usces: %lli\n", get_cpu_usecs() - program_start);
    FOR(i, coeffs.size()) printf("float c%i = %a\n", i, coeffs[i]);
    if (!find_cuts(e, xb, coeffs, testpoints)) return 0;
    printf("vector<float> testpoints = {");
    FOR(i, testpoints.size()) printf(i?",%a":"%a", testpoints[i]);
    printf("};\n");
  }
}

int main() {
  program_start = get_cpu_usecs();
  auto fma = expression::fma;
  expression *x = expression::var(-1);
  expression *c3 = expression::var(6);
  expression *c5 = expression::var(5);
  expression *c7 = expression::var(4);
  expression *c9 = expression::var(3);
  expression *c11 = expression::var(2);
  expression *c13 = expression::var(1);
  expression *c15 = expression::var(0);

  expression *s = fma(x, x, expression::con(0));
  expression *tan_poly = fma(s, c15, c13);
  tan_poly = fma(s, tan_poly, c11);
  tan_poly = fma(s, tan_poly, c9);
  tan_poly = fma(s, tan_poly, c7);
  tan_poly = fma(s, tan_poly, c5);
  tan_poly = fma(s, tan_poly, c3);
  tan_poly = fma(s, tan_poly, expression::con(0));
  tan_poly = fma(x, tan_poly, x);

  Interval cb[8] = {
    {-1, 1},
    {-1, 1},
    {-1, 1},
    {-1, 1},
    {-1, 1},
    {-1, 1},
    {-1, 1},
    {-1, 1}
  };

  vector<float> testpoints = {0x1p-1};

  int k = findit(tan_poly, 7, {1e-4, M_PI/4}, cb, testpoints);

  printf("%i\n", k);
}
