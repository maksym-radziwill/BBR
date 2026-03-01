import BBR.Basic

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section

open Real BigOperators

set_option linter.style.longLine false

/-!
# Proof of Lemma 7.2 in [BBR]

We construct a bivariate polynomial `f(x,y) = Σ_{i,j} a(i,j) xⁱyʲ` satisfying:

1. **Support**: nonzero coefficients lie in `{i,j ≤ 4} ∪ {j=0, i≤8} ∪ {i=0, j≤8}`.
2. **Catalan bound**: `Σ_{i,j} a(2i,2j) · C(i) · C(j) < 1/2`.
3. **Non-negativity**: `f(x,y) ≥ 0` for all real x,y.
4. **Diagonal lower bound**: `f(x,y) ≥ 1` whenever `|x-y|` is small enough.

## Formalization -- Definitions

-/

@[simp] def InSupport (i j : ℕ) : Prop :=
  (i ≤ 4 ∧ j ≤ 4) ∨ (j = 0 ∧ i ≤ 8) ∨ (i = 0 ∧ j ≤ 8)

@[simp] def eval_poly (a : ℕ → ℕ → ℝ) (N : ℕ) (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j * x ^ i * y ^ j

@[simp] def catalan (n : ℕ) : ℕ := Nat.choose (2 * n) n / (n + 1)

@[simp] def catalan_sum (a : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    a (2 * i) (2 * j) * (catalan i : ℝ) * (catalan j : ℝ)

/-!

## Formalization -- Main result

See the theorem poly_lemma at the end of the file.
The statement is repeated here for convenience.

```
theorem poly_lemma : ∃ (a : ℕ → ℕ → ℝ) (N : ℕ),
    (∀ i j, a i j ≠ 0 → InSupport i j ∧ i < N ∧ j < N)
    ∧ catalan_sum a N < 1 / 2
    ∧ (∀ x y : ℝ, 0 ≤ eval_poly a N x y)
    ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ x y : ℝ, |x - y| ≤ ε → 1 ≤ eval_poly a N x y)
```

-/


/-- Zero out odd-total-degree coefficients: the coefficient-level
    effect of the symmetrization g ↦ (g + g∘neg)/2. -/
@[simp] def even_part (a : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i j =>
  if (i + j) % 2 = 0 then a i j else 0

theorem catalan_values : (catalan 0, catalan 1, catalan 2, catalan 3, catalan 4)
    = (1, 1, 2, 5, 14) := by  decide

/-! ## Coefficient data -/

@[simp] def u_coeff : ℕ → ℕ → ℤ
  | 0, 0 => 5217874549248
  | 0, 1 => 16623868928
  | 0, 2 => -3336250252672
  | 0, 3 => -25477793408
  | 0, 4 => 655195946720
  | 0, 5 => 10587831584
  | 0, 6 => -152613570520
  | 0, 7 => -1371845320
  | 0, 8 => 41790603610
  | 1, 0 => -16640770048
  | 1, 1 => 5796896462336
  | 1, 2 => 2432177280
  | 1, 3 => -2074067626368
  | 1, 4 => -167534816
  | 2, 0 => -3336702739328
  | 2, 1 => -2399492480
  | 2, 2 => 5223381207392
  | 2, 3 => 2035437600
  | 2, 4 => -1238781629424
  | 3, 0 => 25484108416
  | 3, 1 => -2074041622592
  | 3, 2 => -2039508160
  | 3, 3 => 914071084096
  | 3, 4 => 409594776
  | 4, 0 => 655694115936
  | 4, 1 => 155563456
  | 4, 2 => -1238844857440
  | 4, 3 => -407914952
  | 4, 4 => 359512561893
  | 5, 0 => -10586722304
  | 6, 0 => -152799075816
  | 7, 0 => 1371693928
  | 8, 0 => 41813434533
  | _, _ => 0

/-! ## Derived polynomials -/

@[simp] def u (x y : ℝ) : ℝ := eval_poly (fun i j => (u_coeff i j : ℝ)) 9 x y

/-- f(x,y) = (u(x,y) + u(-x,-y)) / 20^10. -/
@[simp] def f (x y : ℝ) : ℝ := (1 / (20 : ℝ) ^ 10) * (u x y + u (-x) (-y))

/-- The coefficients of f: scale u_coeff and keep even-total-degree only. -/
@[simp] private def f_coeffs : ℕ → ℕ → ℝ :=
  even_part (fun i j => 2 * (u_coeff i j : ℝ) / (20 : ℝ) ^ 10)

/-! ## Property (1): Support -/

private lemma u_coeff_zero_large_i (i j : ℕ) (hi : 8 < i) : u_coeff i j = 0 := by
  unfold u_coeff; split <;> omega

private lemma u_coeff_zero_large_j (i j : ℕ) (hj : 8 < j) : u_coeff i j = 0 := by
  unfold u_coeff; split <;> omega

theorem u_coeff_support (i j : ℕ) (h : u_coeff i j ≠ 0) : InSupport i j := by
  have hi : i ≤ 8 := by
    by_contra hi'; push_neg at hi'; exact h (u_coeff_zero_large_i i j hi')
  have hj : j ≤ 8 := by
    by_contra hj'; push_neg at hj'; exact h (u_coeff_zero_large_j i j hj')
  unfold InSupport
  interval_cases i <;> interval_cases j <;> simp_all [u_coeff]

/-! ## Property (2): Catalan sum -/

@[simp] def catalan_inner_sum : ℤ :=
  ∑ i ∈ Finset.range 9, ∑ j ∈ Finset.range 9,
    u_coeff (2 * i) (2 * j) * (catalan i : ℤ) * (catalan j : ℤ)

theorem catalan_inner_sum_val : catalan_inner_sum = 2516273466118 := by
  decide

theorem catalan_bound : 2 * (2516273466118 : ℝ) / (20 : ℝ) ^ 10 < 1 / 2 := by
  norm_num

/-! ## SOS polynomials p₁–p₁₅ -/

@[simp] def p1 (x y : ℝ) : ℝ :=
  110664 * x ^ 4 - 62436 * x ^ 3 * y - 125829 * x ^ 2 * y ^ 2
  - 62424 * x * y ^ 3 + 110640 * y ^ 4 + 872 * x ^ 3 + 364 * x ^ 2 * y
  - 364 * x * y ^ 2 - 870 * y ^ 3 - 346208 * x ^ 2 + 111564 * x * y
  - 346144 * y ^ 2 - 2208 * x + 2200 * y + 369968

@[simp] def p2 (x y : ℝ) : ℝ :=
  72082 * x ^ 4 + 115475 * x ^ 3 * y + 85682 * x ^ 2 * y ^ 2
  + 115539 * x * y ^ 3 + 72018 * y ^ 4 + 262 * x ^ 3 - 222 * x ^ 2 * y
  + 224 * x * y ^ 2 - 262 * y ^ 3 - 301192 * x ^ 2
  - 566348 * x * y - 301000 * y ^ 2 - 1264 * x + 1256 * y + 123456

@[simp] def p3 (x y : ℝ) : ℝ :=
  55620 * x ^ 4 - 53290 * x ^ 3 * y - 10 * x ^ 2 * y ^ 2
  + 53273 * x * y ^ 3 - 55648 * y ^ 4 - 3232 * x ^ 3 + 776 * x ^ 2 * y
  + 776 * x * y ^ 2 - 3232 * y ^ 3 - 167796 * x ^ 2
  + 60 * x * y + 167896 * y ^ 2 + 8488 * x + 8488 * y - 16

@[simp] def p4 (x y : ℝ) : ℝ :=
  19116 * x ^ 4 + 81137 * x ^ 3 * y - 291925 * x ^ 2 * y ^ 2
  + 81119 * x * y ^ 3 + 19126 * y ^ 4 - 432 * x ^ 3 + 370 * x ^ 2 * y
  - 370 * x * y ^ 2 + 434 * y ^ 3 + 547060 * x ^ 2
  - 702352 * x * y + 547024 * y ^ 2 + 2032 * x - 2032 * y - 1567392

@[simp] def p5 (x y : ℝ) : ℝ :=
  1021 * x ^ 4 - 503 * x ^ 3 * y + 503 * x * y ^ 3 - 1022 * y ^ 4
  + 101755 * x ^ 3 + 4272 * x ^ 2 * y + 4262 * x * y ^ 2
  + 101760 * y ^ 3 - 3670 * x ^ 2 + 3672 * y ^ 2
  - 306992 * x - 307004 * y

@[simp] def p6 (x y : ℝ) : ℝ :=
  462 * x ^ 4 + 1121 * x ^ 3 * y - 1122 * x * y ^ 3 - 463 * y ^ 4
  - 406 * x ^ 3 + 2114 * x ^ 2 * y + 2114 * x * y ^ 2
  - 404 * y ^ 3 - 3192 * x ^ 2 + 3192 * y ^ 2
  - 1544 * x - 1544 * y

@[simp] def p7 (x y : ℝ) : ℝ :=
  368 * x ^ 4 + 16 * x ^ 3 * y + 283 * x ^ 2 * y ^ 2
  + 16 * x * y ^ 3 + 368 * y ^ 4 + 54 * x ^ 3 + 52 * x ^ 2 * y
  - 52 * x * y ^ 2 - 56 * y ^ 3 + 884 * x ^ 2
  + 1220 * x * y + 884 * y ^ 2 - 56 * x + 56 * y - 9664

@[simp] def p8 (x y : ℝ) : ℝ :=
  362 * x ^ 4 + 863 * x ^ 3 * y - 863 * x * y ^ 3 - 362 * y ^ 4
  + 528 * x ^ 3 - 2896 * x ^ 2 * y - 2896 * x * y ^ 2 + 530 * y ^ 3
  - 2524 * x ^ 2 + 2524 * y ^ 2
  + 2272 * x + 2272 * y

@[simp] def p9 (x y : ℝ) : ℝ :=
  222 * x ^ 4 + 63 * x ^ 3 * y - 62 * x * y ^ 3 - 222 * y ^ 4
  + 22 * x ^ 3 + 8 * x ^ 2 * y + 8 * x * y ^ 2 + 22 * y ^ 3
  + 860 * x ^ 2 + 4 * x * y
  - 860 * y ^ 2 + 120 * x + 120 * y + 16

@[simp] def p10 (x y : ℝ) : ℝ :=
  61 * x ^ 4 - 17 * x ^ 3 * y + 37 * x ^ 2 * y ^ 2
  - 17 * x * y ^ 3 + 61 * y ^ 4 + 4 * x ^ 3 - 4 * x ^ 2 * y
  + 4 * x * y ^ 2 - 2 * y ^ 3 + 312 * x ^ 2
  - 76 * x * y + 312 * y ^ 2 + 24 * x - 24 * y + 2208

@[simp] def p11 (x y : ℝ) : ℝ :=
  15 * x ^ 4 - x ^ 3 * y + 11 * x ^ 2 * y ^ 2
  - x * y ^ 3 + 14 * y ^ 4 - 536 * x ^ 3 - 988 * x ^ 2 * y
  + 988 * x * y ^ 2 + 536 * y ^ 3 + 28 * x ^ 2
  + 48 * x * y + 24 * y ^ 2 - 136 * x + 128 * y - 512

@[simp] def p12 (x y : ℝ) : ℝ :=
  15 * x ^ 4 - 4 * x ^ 3 * y + 13 * x ^ 2 * y ^ 2
  - 4 * x * y ^ 3 + 15 * y ^ 4 - 1582 * x ^ 3 + 808 * x ^ 2 * y
  - 808 * x * y ^ 2 + 1582 * y ^ 3 + 20 * x ^ 2
  + 24 * x * y + 20 * y ^ 2 + 6616 * x - 6616 * y - 432

@[simp] def p13 (x y : ℝ) : ℝ :=
  10 * x ^ 4 + 3 * x ^ 3 * y - 4 * x * y ^ 3 - 10 * y ^ 4
  - 266 * x ^ 3 - 118 * x ^ 2 * y - 118 * x * y ^ 2 - 266 * y ^ 3
  + 36 * x ^ 2 - 4 * x * y - 36 * y ^ 2 - 1440 * x - 1432 * y

@[simp] def p14 (x y : ℝ) : ℝ :=
  5 * x ^ 4 + 199 * x ^ 3 * y - 99 * x ^ 2 * y ^ 2
  + 199 * x * y ^ 3 + 7 * y ^ 4 + 12 * x ^ 3 - 12 * x ^ 2 * y
  + 10 * x * y ^ 2 - 14 * y ^ 3 - 20 * x ^ 2
  + 1128 * x * y - 12 * y ^ 2 + 88 * x - 96 * y + 1776

@[simp] def p15 (x y : ℝ) : ℝ :=
  3 * x ^ 4 + 5 * x ^ 3 * y - x ^ 2 * y ^ 2
  + 5 * x * y ^ 3 + 3 * y ^ 4 - 224 * x ^ 3 + 130 * x ^ 2 * y
  - 130 * x * y ^ 2 + 224 * y ^ 3 + 12 * x ^ 2
  + 32 * x * y + 12 * y ^ 2 - 1112 * x + 1112 * y + 128

@[simp] def c (x y : ℝ) : ℝ :=
  144792 * (x ^ 4 - x ^ 3 * y) ^ 2
  + 173336 * (x ^ 4 + x ^ 2 * y ^ 2) ^ 2
  + 106511 * (x ^ 4 - x ^ 2 * y ^ 2) ^ 2
  + 219778 * (x ^ 4 - x * y ^ 3) ^ 2
  + 177162 * (x ^ 4 - 2 * x ^ 2 * y) ^ 2
  + 293174 * (x ^ 4 + 2 * x * y ^ 2) ^ 2
  + 230298 * (x ^ 4 + 4 * x * y) ^ 2
  + 68230 * (x ^ 3 * y - y ^ 4) ^ 2
  + 157876 * (x ^ 2 * y ^ 2 + y ^ 4) ^ 2
  + 147938 * (x ^ 2 * y ^ 2 - y ^ 4) ^ 2
  + 774352 * (x ^ 2 * y ^ 2 + 2 * y ^ 3) ^ 2
  + 580764 * (x ^ 2 * y ^ 2 - 2 * y ^ 3) ^ 2
  + 76098 * (x * y ^ 3 - y ^ 4) ^ 2
  + 20320 * (y ^ 4 + 2 * x * y ^ 2) ^ 2
  + 40640 * (y ^ 4 - 2 * x * y ^ 2) ^ 2
  + 56386 * (y ^ 4 + 4 * x * y) ^ 2

@[simp] def sos_sum (x y : ℝ) : ℝ :=
  2 * (p1 x y ^ 2 + p2 x y ^ 2 + p3 x y ^ 2 + p4 x y ^ 2 + p5 x y ^ 2
     + p6 x y ^ 2 + p7 x y ^ 2 + p8 x y ^ 2 + p9 x y ^ 2 + p10 x y ^ 2
     + p11 x y ^ 2 + p12 x y ^ 2 + p13 x y ^ 2 + p14 x y ^ 2 + p15 x y ^ 2)
  + 6 * p5 x y ^ 2

/-! ## Property (3): Non-negativity via SOS -/

lemma c_nonneg (x y : ℝ) : 0 ≤ c x y := by
  unfold c
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · apply add_nonneg
        · apply add_nonneg
          · apply add_nonneg
            · apply add_nonneg
              · apply add_nonneg
                · apply add_nonneg
                  · apply add_nonneg
                    · apply add_nonneg
                      · apply add_nonneg
                        · apply add_nonneg
                          · apply add_nonneg
                            · apply add_nonneg
                              · positivity
                              · positivity
                            · positivity
                          · positivity
                        · positivity
                      · positivity
                    · positivity
                  · positivity
                · positivity
              · positivity
            · positivity
          · positivity
        · positivity
      · positivity
    · positivity
  · apply mul_nonneg (by positivity) (sq_nonneg _)

lemma sos_sum_nonneg (x y : ℝ) : 0 ≤ sos_sum x y := by
  unfold sos_sum
  apply add_nonneg
  · apply mul_nonneg (by norm_num) _
    apply add_nonneg
    · apply add_nonneg
      · apply add_nonneg
        · apply add_nonneg
          · apply add_nonneg
            · apply add_nonneg
              · apply add_nonneg
                · apply add_nonneg
                  · apply add_nonneg
                    · apply add_nonneg
                      · apply add_nonneg
                        · apply add_nonneg
                          · apply add_nonneg
                            · apply add_nonneg
                              · positivity
                              · positivity
                            · positivity
                          · positivity
                        · positivity
                      · positivity
                    · positivity
                  · positivity
                · positivity
              · positivity
            · positivity
          · positivity
        · positivity
      · positivity
    · positivity
  · exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem u_sos_decomposition (x y : ℝ) :
    u x y = sos_sum x y + c x y := by
  unfold u eval_poly
  simp only [u_coeff, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [sos_sum, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, c]
  push_cast
  ring

theorem u_nonneg (x y : ℝ) : 0 ≤ u x y := by
  rw [u_sos_decomposition]; exact add_nonneg (sos_sum_nonneg x y) (c_nonneg x y)

theorem f_nonneg (x y : ℝ) : 0 ≤ f x y := by
  unfold f; apply mul_nonneg; · positivity
  exact add_nonneg (u_nonneg x y) (u_nonneg (-x) (-y))

/-! ## Property (4): Diagonal lower bound

The diagonal Δ(x) = f(x,x) is a polynomial in t = x².
As a quadratic form in [1, t, t²], its Gram matrix has rational LDL^T
factorization, giving a sum-of-squares with rational coefficients. -/

@[simp] def Δ (x : ℝ) : ℝ := f x x

/-- The three SOS components — all purely rational. -/
@[simp] def q1 (x : ℝ) : ℝ :=
  1 + (-3422095819 / 760644916 : ℝ) * x ^ 2 + (405650000 / 190161229 : ℝ) * x ^ 4

@[simp] def q2 (x : ℝ) : ℝ :=
  x ^ 2 + (-2058120071711801 / 2699112120326600 : ℝ) * x ^ 4

@[simp] def q3 (x : ℝ) : ℝ := x ^ 4

set_option maxHeartbeats 800000 in
-- Heavy simp calculation
/-- Δ(x) = 1 + 1/10000 + d₁·q₁² + d₂·q₂² + d₃·q₃² with dᵢ > 0 rational. -/
theorem diagonal_sos (x : ℝ) :
    Δ x = 1 + 1 / 10000
      + (190161229 / 10000000000 : ℝ) * q1 x ^ 2
      + (13495560601633 / 608515932800000000 : ℝ) * q2 x ^ 2
      + (812796954232736852431 / 1727431757009024000000000000 : ℝ) * q3 x ^ 2 := by
    simp only [Δ, f, u, eval_poly, u_coeff, q1, q2, q3,
             Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring

theorem diagonal_lower_bound (x : ℝ) : 1 + 1 / 100000 ≤ Δ x := by
  rw [diagonal_sos]
  have h1 : (0 : ℝ) ≤ (190161229 / 10000000000 : ℝ) * q1 x ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ (13495560601633 / 608515932800000000 : ℝ) * q2 x ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ (812796954232736852431 / 1727431757009024000000000000 : ℝ) * q3 x ^ 2 :=
    by positivity
  linarith



set_option maxHeartbeats 800000 in
-- Heavy simp calculation
theorem diagonal_growth (x : ℝ) : (1 : ℝ) / 1000000 * x ^ 8 ≤ Δ x := by
  -- Suffices to show Δ(x) - x⁸/10⁶ ≥ 0.
  -- This polynomial has a rational LDL^T SOS decomposition.
  suffices h : 0 ≤ Δ x - 1 / 1000000 * x ^ 8 by linarith
  -- Define the SOS components (purely rational, no √)
  let r1 : ℝ := 1 + (-3422095819 / 40764644916 : ℝ) * x ^ 2
               + (-726280000 / 10191161229 : ℝ) * x ^ 4
  let r2 : ℝ := x ^ 2 + (-1230201066039551431801 / 3940286757157328486600 : ℝ) * x ^ 4
  let r3 : ℝ := x ^ 4
  -- Δ(x) - x⁸/10⁶ = d₁·r₁² + d₂·r₂² + d₃·r₃²
  have key : Δ x - 1 / 1000000 * x ^ 8
      = (10191161229 / 10000000000 : ℝ) * r1 ^ 2
      + (19701433785786642433 / 32611715932800000000 : ℝ) * r2 ^ 2
      + (56695120715915332985085389212431 / 2521783524580690231424000000000000 : ℝ) * r3 ^ 2 := by
    simp only [Δ, f, u, eval_poly, u_coeff, r1, r2, r3,
               Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  rw [key]
  have h1 : (0 : ℝ) ≤ (10191161229 / 10000000000 : ℝ) * r1 ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ (19701433785786642433 / 32611715932800000000 : ℝ) * r2 ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ (56695120715915332985085389212431 / 2521783524580690231424000000000000 : ℝ) * r3 ^ 2 :=
    by positivity
  linarith

/-! ## Lipschitz bound for f near the diagonal

f(x,x) - f(x,y) = (x-y) · Q(x,y) where Q is the quotient polynomial.
Each monomial |x|^a · |y|^b with a+b ≤ 7 satisfies |x|^a · |y|^b ≤ 2 + 2x⁸
when |y| ≤ |x| + 1/10. The sum of |Q|'s coefficient magnitudes is < 5 < 56. -/

private noncomputable def Q (x y : ℝ) : ℝ :=
  (-26064455099 : ℝ) / 40000000000 * y ^ 1 +
  (4094974667 : ℝ) / 32000000000 * y ^ 3 +
  (-3815339263 : ℝ) / 128000000000 * y ^ 5 +
  (4179060361 : ℝ) / 512000000000 * y ^ 7 +
  (19223798513 : ℝ) / 40000000000 * x ^ 1 +
  (-44339739989 : ℝ) / 160000000000 * x ^ 1 * y ^ 2 +
  (-3815339263 : ℝ) / 128000000000 * x ^ 1 * y ^ 4 +
  (4179060361 : ℝ) / 512000000000 * x ^ 1 * y ^ 6 +
  (59445461371 : ℝ) / 80000000000 * x ^ 2 * y ^ 1 +
  (-173924399993 : ℝ) / 640000000000 * x ^ 2 * y ^ 3 +
  (4179060361 : ℝ) / 512000000000 * x ^ 2 * y ^ 5 +
  (13519280509 : ℝ) / 40000000000 * x ^ 3 +
  (-59665514481 : ℝ) / 640000000000 * x ^ 3 * y ^ 2 +
  (4179060361 : ℝ) / 512000000000 * x ^ 3 * y ^ 4 +
  (-214521121661 : ℝ) / 640000000000 * x ^ 4 * y ^ 1 +
  (401303165503 : ℝ) / 5120000000000 * x ^ 4 * y ^ 3 +
  (-214521121661 : ℝ) / 640000000000 * x ^ 5 +
  (401303165503 : ℝ) / 5120000000000 * x ^ 5 * y ^ 2 +
  (401303165503 : ℝ) / 5120000000000 * x ^ 6 * y ^ 1 +
  (401303165503 : ℝ) / 5120000000000 * x ^ 7

set_option maxHeartbeats 3200000 in
-- Heavy simp calculation
private lemma Q_factor (x y : ℝ) : f x x - f x y = (x - y) * Q x y := by
  simp only [f, u, eval_poly, u_coeff, Q, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast; ring

private lemma monomial_bound_near (a b : ℕ) (hab : a + b ≤ 7) (x y : ℝ)
    (hy : |y| ≤ |x| + 1 / 10) :
    |x| ^ a * |y| ^ b ≤ 2 + 2 * x ^ 8 := by
  have hx8 : |x| ^ 8 = x ^ 8 := by grind -- Even.pow_abs ⟨4, rfl⟩
  have hxn : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hyn : (0 : ℝ) ≤ |y| := abs_nonneg y
  have h1110 : ((11 : ℝ) / 10) ^ 7 ≤ 2 := by norm_num
  by_cases hx1 : |x| ≤ 1
  · -- Case |x| ≤ 1: |y| ≤ 11/10
    have hyb : |y| ≤ 11 / 10 := by linarith
    have hxa : |x| ^ a ≤ 1 := pow_le_one₀ hxn hx1
    have U : 0 ≤ x^8 := by positivity
    have hyp : |y| ^ b ≤ (11 / 10 : ℝ) ^ 7 := by
      calc |y| ^ b ≤ (11 / 10 : ℝ) ^ b := by gcongr -- pow_le_pow_left hyn hyb
        _ ≤ (11 / 10 : ℝ) ^ 7 := by
            have U0 : b ≤ 7 := by grind
            gcongr
            grind
    calc |x| ^ a * |y| ^ b
        ≤ 1 * (11 / 10 : ℝ) ^ 7 := by
          apply mul_le_mul hxa hyp (by positivity) (by linarith)
      _ ≤ 1 * 2 := by
          apply mul_le_mul_of_nonneg_left h1110 (by linarith)
      _ = 2 := one_mul 2
      _ ≤ 2 + 2 * x ^ 8 := by grind
  · -- Case |x| > 1: |y| ≤ 11/10 * |x|
    push_neg at hx1
    have hx_ge : 1 ≤ |x| := le_of_lt hx1
    have hy11 : |y| ≤ 11 / 10 * |x| := by nlinarith
    have hyp : |y| ^ b ≤ (11 / 10) ^ 7 * |x| ^ b := by
      calc |y| ^ b ≤ (11 / 10 * |x|) ^ b := by exact pow_le_pow_left₀ hyn hy11 b
        _ = (11 / 10) ^ b * |x| ^ b := mul_pow (11 / 10 : ℝ) |x| b
        _ ≤ (11 / 10) ^ 7 * |x| ^ b := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have U0 : b ≤ 7 := by grind
            gcongr
            grind
    calc |x| ^ a * |y| ^ b
        ≤ |x| ^ a * ((11 / 10) ^ 7 * |x| ^ b) := by
          exact mul_le_mul_of_nonneg_left hyp (by positivity)
      _ = (11 / 10) ^ 7 * (|x| ^ a * |x| ^ b) := by ring
      _ = (11 / 10) ^ 7 * |x| ^ (a + b) := by rw [pow_add]
      _ ≤ (11 / 10) ^ 7 * |x| ^ 7 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (pow_le_pow_iff_right₀ hx1).mpr hab -- exact pow_le_pow_right hx_ge (by omega)
      _ ≤ 2 * |x| ^ 7 := by
          apply mul_le_mul_of_nonneg_right h1110 (by positivity)
      _ ≤ 2 * |x| ^ 8 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          gcongr
          · grind
          · grind
      _ = 2 * x ^ 8 := by rw [hx8]
      _ ≤ 2 + 2 * x ^ 8 := by linarith

private lemma term_abs_bound (c : ℝ) (a b : ℕ) (x y M : ℝ)
    (hM : |x| ^ a * |y| ^ b ≤ M) (_ : 0 ≤ M) :
    c * x ^ a * y ^ b ≤ |c| * M ∧ -(c * x ^ a * y ^ b) ≤ |c| * M := by
  have hab : |x ^ a * y ^ b| = |x| ^ a * |y| ^ b := by
    rw [abs_mul, abs_pow, abs_pow]
  have hle : |c * (x ^ a * y ^ b)| ≤ |c| * M := by
    rw [abs_mul, hab]
    exact mul_le_mul_of_nonneg_left hM (abs_nonneg c)
  constructor
  · calc c * x ^ a * y ^ b = c * (x ^ a * y ^ b) := by ring
      _ ≤ |c * (x ^ a * y ^ b)| := le_abs_self _
      _ ≤ |c| * M := hle
  · calc -(c * x ^ a * y ^ b) = -(c * (x ^ a * y ^ b)) := by ring
      _ ≤ |c * (x ^ a * y ^ b)| := neg_le.mpr (neg_abs_le _)
      _ ≤ |c| * M := hle

set_option maxHeartbeats 800000 in
-- Heavy simp calculation
private lemma Q_abs_bound (x y : ℝ) (hy : |y| ≤ |x| + 1 / 10) :
    |Q x y| ≤ 56 * (4 + 2 * x ^ 8) := by
  unfold Q
  set M := 2 + 2 * x ^ 8 with hM_def
  have hMn : (0 : ℝ) ≤ M := by positivity
  have m0 := monomial_bound_near 0 1 (by omega) x y hy
  have m1 := monomial_bound_near 0 3 (by omega) x y hy
  have m2 := monomial_bound_near 0 5 (by omega) x y hy
  have m3 := monomial_bound_near 0 7 (by omega) x y hy
  have m4 := monomial_bound_near 1 0 (by omega) x y hy
  have m5 := monomial_bound_near 1 2 (by omega) x y hy
  have m6 := monomial_bound_near 1 4 (by omega) x y hy
  have m7 := monomial_bound_near 1 6 (by omega) x y hy
  have m8 := monomial_bound_near 2 1 (by omega) x y hy
  have m9 := monomial_bound_near 2 3 (by omega) x y hy
  have m10 := monomial_bound_near 2 5 (by omega) x y hy
  have m11 := monomial_bound_near 3 0 (by omega) x y hy
  have m12 := monomial_bound_near 3 2 (by omega) x y hy
  have m13 := monomial_bound_near 3 4 (by omega) x y hy
  have m14 := monomial_bound_near 4 1 (by omega) x y hy
  have m15 := monomial_bound_near 4 3 (by omega) x y hy
  have m16 := monomial_bound_near 5 0 (by omega) x y hy
  have m17 := monomial_bound_near 5 2 (by omega) x y hy
  have m18 := monomial_bound_near 6 1 (by omega) x y hy
  have m19 := monomial_bound_near 7 0 (by omega) x y hy
  have t0 := term_abs_bound ((-26064455099 : ℝ) / 40000000000) 0 1 x y M m0 hMn
  have t1 := term_abs_bound ((4094974667 : ℝ) / 32000000000) 0 3 x y M m1 hMn
  have t2 := term_abs_bound ((-3815339263 : ℝ) / 128000000000) 0 5 x y M m2 hMn
  have t3 := term_abs_bound ((4179060361 : ℝ) / 512000000000) 0 7 x y M m3 hMn
  have t4 := term_abs_bound ((19223798513 : ℝ) / 40000000000) 1 0 x y M m4 hMn
  have t5 := term_abs_bound ((-44339739989 : ℝ) / 160000000000) 1 2 x y M m5 hMn
  have t6 := term_abs_bound ((-3815339263 : ℝ) / 128000000000) 1 4 x y M m6 hMn
  have t7 := term_abs_bound ((4179060361 : ℝ) / 512000000000) 1 6 x y M m7 hMn
  have t8 := term_abs_bound ((59445461371 : ℝ) / 80000000000) 2 1 x y M m8 hMn
  have t9 := term_abs_bound ((-173924399993 : ℝ) / 640000000000) 2 3 x y M m9 hMn
  have t10 := term_abs_bound ((4179060361 : ℝ) / 512000000000) 2 5 x y M m10 hMn
  have t11 := term_abs_bound ((13519280509 : ℝ) / 40000000000) 3 0 x y M m11 hMn
  have t12 := term_abs_bound ((-59665514481 : ℝ) / 640000000000) 3 2 x y M m12 hMn
  have t13 := term_abs_bound ((4179060361 : ℝ) / 512000000000) 3 4 x y M m13 hMn
  have t14 := term_abs_bound ((-214521121661 : ℝ) / 640000000000) 4 1 x y M m14 hMn
  have t15 := term_abs_bound ((401303165503 : ℝ) / 5120000000000) 4 3 x y M m15 hMn
  have t16 := term_abs_bound ((-214521121661 : ℝ) / 640000000000) 5 0 x y M m16 hMn
  have t17 := term_abs_bound ((401303165503 : ℝ) / 5120000000000) 5 2 x y M m17 hMn
  have t18 := term_abs_bound ((401303165503 : ℝ) / 5120000000000) 6 1 x y M m18 hMn
  have t19 := term_abs_bound ((401303165503 : ℝ) / 5120000000000) 7 0 x y M m19 hMn
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

private lemma f_lipschitz_y (x y : ℝ) (hxy : |x - y| ≤ (1 : ℝ) / 10 ^ 15) :
    |f x x - f x y| ≤ (1 : ℝ) / 10 ^ 15 * 56 * (4 + 2 * x ^ 8) := by
  have hy : |y| ≤ |x| + 1 / 10 := by
    have h1 : |y| - |x| ≤ |y - x| := abs_sub_abs_le_abs_sub y x
    have h2 : |y - x| = |x - y| := abs_sub_comm y x
    have h3 : (1 : ℝ) / 10 ^ 15 ≤ 1 / 10 := by norm_num
    linarith
  rw [Q_factor]
  rw [abs_mul]
  have hQ := Q_abs_bound x y hy
  calc |x - y| * |Q x y|
      ≤ (1 / 10 ^ 15) * (56 * (4 + 2 * x ^ 8)) :=
        mul_le_mul hxy hQ (abs_nonneg _) (by positivity)
    _ = (1 : ℝ) / 10 ^ 15 * 56 * (4 + 2 * x ^ 8) := by ring


theorem f_mvt_lower_bound (x y : ℝ) (hxy : |x - y| ≤ ((1 : ℝ) / 10 ^ 15)) :
    Δ x - (1 : ℝ) / 10 ^ 15 * 56 * (4 + 2 * x ^ 8) ≤ f x y := by
  simp only [Δ]
  have h := f_lipschitz_y x y hxy
  -- From |a - b| ≤ C we get a - C ≤ b
  linarith [le_abs_self (f x x - f x y)]

theorem case_small_x (x : ℝ) (hx : |x| ≤ 6) :
    1 < Δ x - ((1 : ℝ) / 10^15) * 56 * (4 + 2 * x ^ 8) := by
  have hΔ := diagonal_lower_bound x
  have h2 : x ^ 2 ≤ 6 ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have h4 : x ^ 4 ≤ 6 ^ 4 := by nlinarith [sq_nonneg x]
  have hx8 : x ^ 8 ≤ 6 ^ 8 := by nlinarith [sq_nonneg (x ^ 2)]
  nlinarith

theorem case_large_x (x : ℝ) (hx : 6 < |x|) :
    1 < Δ x - ((1 : ℝ) / 10^15) * 56 * (4 + 2 * x ^ 8) := by
  have hΔ := diagonal_growth x
  have h2 : (6 : ℝ) ^ 2 < x ^ 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 6), abs_nonneg x]
  have h4 : (6 : ℝ) ^ 4 < x ^ 4 := by nlinarith [sq_nonneg (x ^ 2 - 6 ^ 2)]
  have hx8 : (6 : ℝ) ^ 8 < x ^ 8 := by nlinarith [sq_nonneg (x ^ 4 - 6 ^ 4)]
  nlinarith

theorem f_gt_one_near_diagonal (x y : ℝ) (hxy : |x - y| ≤ (1 : ℝ) / 10 ^ 15) :
    1 < f x y := by
  have hmvt := f_mvt_lower_bound x y hxy
  --have u : (10 : ℝ )^ (- 15 : ℝ ) = 1 / 10^15 := by ring_nf
  --rw [u] at hmvt
  by_cases hx : |x| ≤ 6
  · exact lt_of_lt_of_le (case_small_x x hx) hmvt
  · push_neg at hx; exact lt_of_lt_of_le (case_large_x x hx) hmvt

/-! ## Main result -/

set_option maxHeartbeats 800000 in
-- Heavy simp calculation
/-- Bridge: f = eval_poly of f_coeffs. -/
private lemma f_eq_eval (x y : ℝ) :
    f x y = eval_poly f_coeffs 9 x y := by
  unfold f u eval_poly f_coeffs even_part
  simp only [u_coeff, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

set_option maxHeartbeats 800000 in
-- Heavy simp calculation

/--
**Lemma 7.2 [BBR].** There exist `a : ℕ → ℕ → ℝ` and `N : ℕ` such that
`f(x,y) = Σ_{i,j < N} a(i,j) xⁱyʲ` satisfies:
1. `a(i,j) = 0` unless `(i,j) ∈ S`, and `i,j ≤ N`;
2. `Σ_{i,j < N} a(2i,2j) C(i) C(j) < 1/2`;
3. `f(x,y) ≥ 0` for all `x, y`;
4. there exists `ε > 0` with `f(x,y) ≥ 1` whenever `|x − y| ≤ ε`.
-/
theorem poly_lemma : ∃ (a : ℕ → ℕ → ℝ) (N : ℕ),
    (∀ i j, a i j ≠ 0 → InSupport i j ∧ i < N ∧ j < N)
    ∧ catalan_sum a N < 1 / 2
    ∧ (∀ x y : ℝ, 0 ≤ eval_poly a N x y)
    ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ x y : ℝ, |x - y| ≤ ε → 1 ≤ eval_poly a N x y) := by
  refine ⟨f_coeffs, 9, ?_, ?_, ?_, ?_⟩
  · -- (1) Support and degree bound
    intro i j h
    simp only [f_coeffs, even_part] at h
    split_ifs at h with hp
    · have hu : u_coeff i j ≠ 0 := by intro hz; exact h (by rw [hz]; simp)
      have hs := u_coeff_support i j hu
      exact ⟨hs, by rcases hs with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega,
                 by rcases hs with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega⟩
    · exact absurd rfl h
  · -- (2) Catalan sum < 1/2
    show catalan_sum f_coeffs 9 < 1 / 2
    have key : catalan_sum f_coeffs 9 = 2 * (catalan_inner_sum : ℝ) / (20 : ℝ) ^ 10 := by
      unfold catalan_sum catalan_inner_sum f_coeffs even_part
      simp only [u_coeff, catalan, Finset.sum_range_succ, Finset.sum_range_zero]
      push_cast; ring_nf
      --simp
      --unfold Nat.choose
      simp [Nat.choose]
    rw [key, show (catalan_inner_sum : ℝ) = 2516273466118 from by
      exact_mod_cast catalan_inner_sum_val]
    norm_num
  · -- (3) Non-negativity
    intro x y
    rw [show eval_poly f_coeffs 9 x y = f x y from (f_eq_eval x y).symm]
    exact f_nonneg x y
  · -- (4) Diagonal lower bound
    exact ⟨(1 : ℝ) / (10^15), by positivity, fun x y hxy => by
      rw [show eval_poly f_coeffs 9 x y = f x y from (f_eq_eval x y).symm]
      exact le_of_lt (f_gt_one_near_diagonal x y hxy)⟩
