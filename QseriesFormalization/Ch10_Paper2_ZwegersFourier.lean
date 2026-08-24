import QseriesFormalization.Ch10_Paper2_CompletedTheta
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Ch10 / Paper 2: the Gaussian core of Zwegers' Lemma 2.8

Zwegers, *Mock Theta Functions* (arXiv:0807.4834), Lemma 2.8, specialized to
this paper's data: `r = 2`, `A = diag(1,-5)`, `Q(X,Y) = (X²-5Y²)/2`,
`B((X,Y),(X',Y')) = XX' - 5YY'`, `c₁ = (0,1)`, `c₂ = (-5,3)`.

This file is scoped to the analytic ingredients that Lemma 2.8's proof rests
on, and **claims no modular transformation of anything**:

* the three positive-definite quadratic forms — Zwegers' `Q_c` of Lemma 2.5 at
  `c₁` and at `c₂`, and his `Q⁺` of Lemma 2.6 — with closed forms and a common
  uniform lower bound;
* the one-dimensional Gaussian Fourier formula in the normalization Zwegers
  quotes, matched to Mathlib's `integral_cexp_quadratic`, with the square-root
  branch pinned down;
* the two-dimensional diagonal case, which is the `r = 2` shape his change of
  basis along `c` and `⟨c⟩^⊥` produces, with the constant `1/(-iτ)` obtained
  branch-free by multiplying one square root by itself.

Nothing here is a statement about `paper2LatticeTheta`, about Poisson
summation, or about the `S`-transformation.

Reused: `paper2Q0` and `paper2B0` from `Ch10_Paper2_CompletedTheta` (so no
second copy of `Q` or `B` is created).  `Mathlib.Analysis.SpecialFunctions.
Gaussian.FourierTransform` is imported for `integral_cexp_quadratic` and
`integrable_cexp_quadratic'`; `Ch10_Paper2_ErrorKernel` already brings in
`GaussianIntegral`, but not `FourierTransform`.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Zwegers' positive-definite forms at this data

`Q_c(ν) = Q(ν) - B(c,ν)²/(2Q(c))` (Lemma 2.5) and
`Q⁺(ν) = Q(ν) + B(c₁,c₂)/(4Q(c₁)Q(c₂) - B(c₁,c₂)²)·B(c₁,ν)B(c₂,ν)` (Lemma 2.6).
Both are written with the structure constants left as `paper2Q0`/`paper2B0`
applications, so the definitions are Zwegers' formulas rather than
precomputed numbers. -/

/-- Zwegers' `Q_{c₁}`, Lemma 2.5, at `c₁ = (0,1)`. -/
noncomputable def paper2Qc1 (X Y : ℝ) : ℝ :=
  paper2Q0 X Y - paper2B0 0 1 X Y ^ 2 / (2 * paper2Q0 0 1)

/-- Zwegers' `Q_{c₂}`, Lemma 2.5, at `c₂ = (-5,3)`. -/
noncomputable def paper2Qc2 (X Y : ℝ) : ℝ :=
  paper2Q0 X Y - paper2B0 (-5) 3 X Y ^ 2 / (2 * paper2Q0 (-5) 3)

/-- Zwegers' `Q⁺`, Lemma 2.6, at `c₁ = (0,1)`, `c₂ = (-5,3)`. -/
noncomputable def paper2QPlus (X Y : ℝ) : ℝ :=
  paper2Q0 X Y +
    paper2B0 0 1 (-5) 3 / (4 * paper2Q0 0 1 * paper2Q0 (-5) 3 - paper2B0 0 1 (-5) 3 ^ 2) *
      (paper2B0 0 1 X Y * paper2B0 (-5) 3 X Y)

theorem paper2Q0_c1_val : paper2Q0 0 1 = -(5 / 2) := by
  rw [paper2Q0]; norm_num

theorem paper2Q0_c2_val : paper2Q0 (-5) 3 = -10 := by
  rw [paper2Q0]; norm_num

theorem paper2B0_c1_c2_val : paper2B0 0 1 (-5) 3 = -15 := by
  rw [paper2B0]; norm_num

/-- `Q_{c₁}(X,Y) = (X² + 5Y²)/2`. -/
theorem paper2Qc1_eq (X Y : ℝ) : paper2Qc1 X Y = (X ^ 2 + 5 * Y ^ 2) / 2 := by
  rw [paper2Qc1, paper2Q0_c1_val, paper2Q0, paper2B0]
  ring

/-- `Q_{c₂}(X,Y) = (7X² + 30XY + 35Y²)/4`. -/
theorem paper2Qc2_eq (X Y : ℝ) : paper2Qc2 X Y = (7 * X ^ 2 + 30 * X * Y + 35 * Y ^ 2) / 4 := by
  rw [paper2Qc2, paper2Q0_c2_val, paper2Q0, paper2B0]
  ring

/-- `Q⁺(X,Y) = (X² + 6XY + 13Y²)/2`. -/
theorem paper2QPlus_eq (X Y : ℝ) : paper2QPlus X Y = (X ^ 2 + 6 * X * Y + 13 * Y ^ 2) / 2 := by
  simp only [paper2QPlus, paper2Q0, paper2B0]
  norm_num
  ring

/-- All three forms dominate `(X²+Y²)/10`.  The smallest eigenvalue is
`≈ 0.1205` for `Q_{c₂}` and `≈ 0.1459` for `Q⁺`, so `1/10` is a valid common
constant. -/
theorem paper2Qc1_lower (X Y : ℝ) : (X ^ 2 + Y ^ 2) / 10 ≤ paper2Qc1 X Y := by
  rw [paper2Qc1_eq]
  nlinarith [sq_nonneg X, sq_nonneg Y]

theorem paper2Qc2_lower (X Y : ℝ) : (X ^ 2 + Y ^ 2) / 10 ≤ paper2Qc2 X Y := by
  rw [paper2Qc2_eq]
  nlinarith [sq_nonneg (33 * X + 75 * Y), sq_nonneg Y]

theorem paper2QPlus_lower (X Y : ℝ) : (X ^ 2 + Y ^ 2) / 10 ≤ paper2QPlus X Y := by
  rw [paper2QPlus_eq]
  nlinarith [sq_nonneg (4 * X + 15 * Y), sq_nonneg Y]

theorem paper2Qc1_pos {X Y : ℝ} (h : X ≠ 0 ∨ Y ≠ 0) : 0 < paper2Qc1 X Y := by
  refine lt_of_lt_of_le ?_ (paper2Qc1_lower X Y)
  rcases h with h | h
  · have h1 : (0 : ℝ) < X ^ 2 := lt_of_le_of_ne (sq_nonneg X) (Ne.symm (pow_ne_zero 2 h))
    have h2 := sq_nonneg Y
    linarith
  · have h1 : (0 : ℝ) < Y ^ 2 := lt_of_le_of_ne (sq_nonneg Y) (Ne.symm (pow_ne_zero 2 h))
    have h2 := sq_nonneg X
    linarith

theorem paper2Qc2_pos {X Y : ℝ} (h : X ≠ 0 ∨ Y ≠ 0) : 0 < paper2Qc2 X Y := by
  refine lt_of_lt_of_le ?_ (paper2Qc2_lower X Y)
  rcases h with h | h
  · have h1 : (0 : ℝ) < X ^ 2 := lt_of_le_of_ne (sq_nonneg X) (Ne.symm (pow_ne_zero 2 h))
    have h2 := sq_nonneg Y
    linarith
  · have h1 : (0 : ℝ) < Y ^ 2 := lt_of_le_of_ne (sq_nonneg Y) (Ne.symm (pow_ne_zero 2 h))
    have h2 := sq_nonneg X
    linarith

theorem paper2QPlus_pos {X Y : ℝ} (h : X ≠ 0 ∨ Y ≠ 0) : 0 < paper2QPlus X Y := by
  refine lt_of_lt_of_le ?_ (paper2QPlus_lower X Y)
  rcases h with h | h
  · have h1 : (0 : ℝ) < X ^ 2 := lt_of_le_of_ne (sq_nonneg X) (Ne.symm (pow_ne_zero 2 h))
    have h2 := sq_nonneg Y
    linarith
  · have h1 : (0 : ℝ) < Y ^ 2 := lt_of_le_of_ne (sq_nonneg Y) (Ne.symm (pow_ne_zero 2 h))
    have h2 := sq_nonneg X
    linarith

/-! ## Branch bookkeeping for the square root

Everything below uses the principal branch `z ^ (1/2 : ℂ)`.  Three facts pin
it down: a positive real factor splits off, `((r:ℝ):ℂ)^{1/2}` is the real
square root, and the square root times itself is the argument.  Together these
make the `r = 2` constant unambiguous without ever computing an argument. -/

theorem paper2_ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    ((r : ℂ) * x) ^ s = (r : ℂ) ^ s * x ^ s := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr' hx), Complex.log_ofReal_mul hr hx,
    Complex.ofReal_log hr.le, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero hr', ← Complex.cpow_def_of_ne_zero hx]

theorem paper2_ofReal_cpow_half {r : ℝ} (hr : 0 ≤ r) :
    ((r : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr]
  norm_num

theorem paper2_cpow_half_mul_self {z : ℂ} (hz : z ≠ 0) :
    z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
  rw [← Complex.cpow_add _ _ hz]
  norm_num

theorem paper2_neg_I_mul_re (τ : ℂ) : (-Complex.I * τ).re = τ.im := by
  simp [Complex.mul_re]

theorem paper2_neg_I_mul_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : -Complex.I * τ ≠ 0 := by
  intro h
  have : (-Complex.I * τ).re = 0 := by rw [h]; simp
  rw [paper2_neg_I_mul_re] at this
  exact absurd this hτ.ne'

/-! ## The one-dimensional Gaussian formula

Zwegers quotes, for `τ ∈ ℍ` and `M` positive definite symmetric `n × n`,
`∫_{ℝⁿ} e^{πi⟨a,Ma⟩τ + 2πi⟨a,Mα⟩} da = (-iτ)^{-n/2}(det M)^{-1/2}e^{-πi⟨α,Mα⟩/τ}`.
At `n = 1`, `M = (m)`, this is the statement below; it is Mathlib's
`integral_cexp_quadratic` with `b = πimτ`, `c = 2πimα`, `d = 0`, after
identifying `(π / -b)^{1/2}` with `(√m)⁻¹ ((-iτ)⁻¹)^{1/2}`. -/

theorem paper2_gaussian_1d_re {τ : ℂ} {m : ℝ} :
    ((Real.pi : ℂ) * Complex.I * (m : ℂ) * τ).re = -(Real.pi * m * τ.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem paper2_gaussian_1d_bre {τ : ℂ} (hτ : 0 < τ.im) {m : ℝ} (hm : 0 < m) :
    ((Real.pi : ℂ) * Complex.I * (m : ℂ) * τ).re < 0 := by
  rw [paper2_gaussian_1d_re]
  have hpi := Real.pi_pos
  have : 0 < Real.pi * m * τ.im := mul_pos (mul_pos hpi hm) hτ
  linarith

theorem paper2_integrable_gaussian_1d {τ : ℂ} (hτ : 0 < τ.im) {m : ℝ} (hm : 0 < m) (α : ℝ) :
    MeasureTheory.Integrable (fun a : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ) * τ * (a : ℂ) ^ 2
      + 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ) * (a : ℂ))) := by
  have h := integrable_cexp_quadratic' (paper2_gaussian_1d_bre hτ hm)
    (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ)) 0
  simpa using h

/-- **The one-dimensional Gaussian Fourier formula**, in Zwegers'
normalization, with the square root pinned to the principal branch of
`((-iτ)⁻¹)^{1/2}` and the positive real factor `(√m)⁻¹` extracted. -/
theorem paper2_gaussian_1d {τ : ℂ} (hτ : 0 < τ.im) {m : ℝ} (hm : 0 < m) (α : ℝ) :
    (∫ a : ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ) * τ * (a : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ) * (a : ℂ)))
      = ((Real.sqrt m : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)
        * Complex.exp (-((Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ) ^ 2) / τ) := by
  have hτ0 : τ ≠ 0 := fun h => absurd (by rw [h]; simp : τ.im = 0) hτ.ne'
  have hm0 : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hw : (-Complex.I * τ) ≠ 0 := paper2_neg_I_mul_ne_zero hτ
  have key := integral_cexp_quadratic (paper2_gaussian_1d_bre hτ hm)
    (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ)) 0
  simp only [add_zero] at key
  rw [key]
  have hconst : (Real.pi : ℂ) / (-((Real.pi : ℂ) * Complex.I * (m : ℂ) * τ))
      = ((m⁻¹ : ℝ) : ℂ) * (-Complex.I * τ)⁻¹ := by
    push_cast
    field_simp
  have hexp : (0 : ℂ) - (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ)) ^ 2
        / (4 * ((Real.pi : ℂ) * Complex.I * (m : ℂ) * τ))
      = -((Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ) ^ 2) / τ := by
    have hc2 : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (α : ℂ)) ^ 2
        = -(4 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2 * (α : ℂ) ^ 2) := by
      linear_combination (4 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2 * (α : ℂ) ^ 2) * Complex.I_sq
    rw [hc2]
    field_simp
    linear_combination ((Real.pi : ℂ) * (m : ℂ) * (α : ℂ) ^ 2) * Complex.I_sq
  rw [hconst, hexp, paper2_ofReal_mul_cpow (inv_pos.2 hm) (inv_ne_zero hw),
    paper2_ofReal_cpow_half (le_of_lt (inv_pos.2 hm)), Real.sqrt_inv]
  push_cast
  ring

/-! ## The `r = 2` diagonal case

Zwegers' step 3 changes basis to `(c | C)`, after which `(c|C)ᵀA(c|C)` is block
diagonal; at `r = 2` both blocks are scalars, so the integral is a product of
two one-dimensional Gaussians.  The constant that results is obtained here
without any branch decision: the two factors contribute *the same* square root
`((-iτ)⁻¹)^{1/2}`, and a square root times itself is its argument. -/

/-- **The branch-free `r = 2` constant.**  Two one-dimensional factors multiply
to `(√(m₁m₂))⁻¹ (-iτ)⁻¹` with no choice of branch: the `(-iτ)` parts are the
same square root multiplied by itself, and the `m` parts are positive reals. -/
theorem paper2_gaussian_const_prod {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (_h₂ : 0 < m₂) {τ : ℂ}
    (hτ : 0 < τ.im) :
    (((Real.sqrt m₁ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
        (((Real.sqrt m₂ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ))
      = ((Real.sqrt (m₁ * m₂) : ℝ) : ℂ)⁻¹ * (-Complex.I * τ)⁻¹ := by
  have hw : (-Complex.I * τ)⁻¹ ≠ 0 := inv_ne_zero (paper2_neg_I_mul_ne_zero hτ)
  calc (((Real.sqrt m₁ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
        (((Real.sqrt m₂ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ))
      = (((Real.sqrt m₁ : ℝ) : ℂ)⁻¹ * ((Real.sqrt m₂ : ℝ) : ℂ)⁻¹) *
          (((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ) * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) := by
        ring
    _ = (((Real.sqrt m₁ : ℝ) : ℂ)⁻¹ * ((Real.sqrt m₂ : ℝ) : ℂ)⁻¹) * (-Complex.I * τ)⁻¹ := by
        rw [paper2_cpow_half_mul_self hw]
    _ = ((Real.sqrt (m₁ * m₂) : ℝ) : ℂ)⁻¹ * (-Complex.I * τ)⁻¹ := by
        rw [Real.sqrt_mul h₁.le]
        push_cast
        simp only [mul_inv]

theorem paper2_integrable_gaussian_2d {τ : ℂ} (hτ : 0 < τ.im) {m₁ m₂ : ℝ} (h₁ : 0 < m₁)
    (h₂ : 0 < m₂) (α₁ α₂ : ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * τ * (a.1 : ℂ) ^ 2
          + 2 * (Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * (α₁ : ℂ) * (a.1 : ℂ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * τ * (a.2 : ℂ) ^ 2
          + 2 * (Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * (α₂ : ℂ) * (a.2 : ℂ))) :=
  (paper2_integrable_gaussian_1d hτ h₁ α₁).mul_prod (paper2_integrable_gaussian_1d hτ h₂ α₂)

/-- **The two-dimensional diagonal Gaussian formula.**  This is the `r = 2`,
`M = diag(m₁,m₂)` case of the classical formula Zwegers quotes; the constant is
`(det M)^{-1/2}(-iτ)^{-1}` with `(det M)^{-1/2} = (√(m₁m₂))⁻¹` a positive real
and `(-iτ)^{-1}` unambiguous. -/
theorem paper2_gaussian_2d {τ : ℂ} (hτ : 0 < τ.im) {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (α₁ α₂ : ℝ) :
    (∫ a : ℝ × ℝ,
        Complex.exp ((Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * τ * (a.1 : ℂ) ^ 2
            + 2 * (Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * (α₁ : ℂ) * (a.1 : ℂ)) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * τ * (a.2 : ℂ) ^ 2
            + 2 * (Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * (α₂ : ℂ) * (a.2 : ℂ)))
      = ((Real.sqrt (m₁ * m₂) : ℝ) : ℂ)⁻¹ * (-Complex.I * τ)⁻¹ *
        Complex.exp (-((Real.pi : ℂ) * Complex.I *
          ((m₁ : ℂ) * (α₁ : ℂ) ^ 2 + (m₂ : ℂ) * (α₂ : ℂ) ^ 2)) / τ) := by
  have hτ0 : τ ≠ 0 := fun h => absurd (by rw [h]; simp : τ.im = 0) hτ.ne'
  have hsplit := MeasureTheory.integral_prod_mul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (fun x : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * τ * (x : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * (α₁ : ℂ) * (x : ℂ)))
      (fun x : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * τ * (x : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * (α₂ : ℂ) * (x : ℂ)))
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, hsplit,
    paper2_gaussian_1d hτ h₁, paper2_gaussian_1d hτ h₂]
  rw [show (((Real.sqrt m₁ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * (α₁ : ℂ) ^ 2) / τ)) *
      (((Real.sqrt m₂ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * (α₂ : ℂ) ^ 2) / τ))
      = ((((Real.sqrt m₁ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
          (((Real.sqrt m₂ : ℝ) : ℂ)⁻¹ * ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ))) *
        (Complex.exp (-((Real.pi : ℂ) * Complex.I * (m₁ : ℂ) * (α₁ : ℂ) ^ 2) / τ) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * (m₂ : ℂ) * (α₂ : ℂ) ^ 2) / τ)) from by
    ring]
  rw [paper2_gaussian_const_prod h₁ h₂ hτ, ← Complex.exp_add]
  congr 2
  field_simp
  ring

/-! ## Where Lemma 2.5 enters the convergence

Zwegers' step 2 replaces `∂ρ/∂a_l` by a Gaussian, `E'(z) = 2e^{-πz²}`.  Pairing
that Gaussian with `|e^{2πiQ(a)τ}| = e^{-2πQ(a)y}` gives exactly `e^{-2πy Q_c(a)}`
with `Q_c` the positive-definite form of Lemma 2.5.  The two identities below
are that cancellation, at `c₁` and at `c₂`; together with the lower bounds above
they are what makes the differentiated integrand absolutely integrable. -/

theorem paper2_kernel_exponent_c1 {y : ℝ} (hy : 0 ≤ y) (X Y : ℝ) :
    -Real.pi * (paper2B0 0 1 X Y * Real.sqrt y / Real.sqrt (-paper2Q0 0 1)) ^ 2
        - 2 * Real.pi * paper2Q0 X Y * y
      = -(2 * Real.pi * y * paper2Qc1 X Y) := by
  have hs : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hq : Real.sqrt (-paper2Q0 0 1) ^ 2 = 5 / 2 := by
    rw [paper2Q0_c1_val, show -(-(5 / 2) : ℝ) = 5 / 2 by norm_num]
    exact Real.sq_sqrt (by norm_num)
  rw [div_pow, mul_pow, hs, hq, paper2Qc1_eq, paper2B0, paper2Q0]
  ring

theorem paper2_kernel_exponent_c2 {y : ℝ} (hy : 0 ≤ y) (X Y : ℝ) :
    -Real.pi * (paper2B0 (-5) 3 X Y * Real.sqrt y / Real.sqrt (-paper2Q0 (-5) 3)) ^ 2
        - 2 * Real.pi * paper2Q0 X Y * y
      = -(2 * Real.pi * y * paper2Qc2 X Y) := by
  have hs : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hq : Real.sqrt (-paper2Q0 (-5) 3) ^ 2 = 10 := by
    rw [paper2Q0_c2_val, show -(-10 : ℝ) = 10 by norm_num]
    exact Real.sq_sqrt (by norm_num)
  rw [div_pow, mul_pow, hs, hq, paper2Qc2_eq, paper2B0, paper2Q0]
  ring

/-! ## The two splits along `c` and `⟨c⟩^⊥` at this data

Zwegers' step 3 substitutes `a = (c | C)(a_c, a')`, where the columns of `C`
span `⟨c⟩^⊥ = {a : B(c,a) = 0}`, and uses

  `B(c, C a') = 0`,  `B(c, a) = 2Q(c) a_c`,  `Q(a) = Q(c) a_c² + ½ B(C,C) a'²`,
  `(det (c|C))² · det A = 2Q(c) · B(C,C)`.

At `r = 2` the matrix `C` is the single column `e`, so `CᵀAC = B(e,e)` is a
scalar, and Zwegers' "positive definite on `⟨c⟩^⊥`" is just `B(e,e) > 0`.
Everything below is that data, verified: `e₁ = (1,0)` for `c₁ = (0,1)` and
`e₂ = (3,-1)` for `c₂ = (-5,3)`.  These are the same two vectors the
`(n,T)` coordinate dictionary of the earlier files is built from. -/

-- The orthogonality facts `paper2B0_c1_e1 : B(c₁,e₁) = 0` and
-- `paper2B0_c2_e2 : B(c₂,e₂) = 0` are already proved in
-- `Ch10_Paper2_CompletedTheta` and are reused, not restated.

/-- `B(e₁,e₁) = 1 > 0`: the `⟨c₁⟩^⊥` block is positive definite. -/
theorem paper2B0_e1_e1 : paper2B0 1 0 1 0 = 1 := by rw [paper2B0]; norm_num

/-- `B(e₂,e₂) = 4 > 0`: the `⟨c₂⟩^⊥` block is positive definite. -/
theorem paper2B0_e2_e2 : paper2B0 3 (-1) 3 (-1) = 4 := by rw [paper2B0]; norm_num

theorem paper2B0_e1_e1_pos : 0 < paper2B0 1 0 1 0 := by rw [paper2B0_e1_e1]; norm_num

theorem paper2B0_e2_e2_pos : 0 < paper2B0 3 (-1) 3 (-1) := by rw [paper2B0_e2_e2]; norm_num

/-- `Q` in the `c₁`-adapted coordinates `a = s·c₁ + t·e₁`. -/
theorem paper2Q0_split_c1 (s t : ℝ) :
    paper2Q0 (0 * s + 1 * t) (1 * s + 0 * t)
      = paper2Q0 0 1 * s ^ 2 + paper2B0 1 0 1 0 / 2 * t ^ 2 := by
  rw [paper2Q0, paper2Q0, paper2B0]
  ring

/-- `B(c₁, ·)` in the `c₁`-adapted coordinates: it sees only `s`, with the
factor `2Q(c₁)`. -/
theorem paper2B0_split_c1 (s t : ℝ) :
    paper2B0 0 1 (0 * s + 1 * t) (1 * s + 0 * t) = 2 * paper2Q0 0 1 * s := by
  rw [paper2B0, paper2Q0]
  ring

/-- `Q` in the `c₂`-adapted coordinates `a = s·c₂ + t·e₂`. -/
theorem paper2Q0_split_c2 (s t : ℝ) :
    paper2Q0 (-5 * s + 3 * t) (3 * s + -1 * t)
      = paper2Q0 (-5) 3 * s ^ 2 + paper2B0 3 (-1) 3 (-1) / 2 * t ^ 2 := by
  rw [paper2Q0, paper2Q0, paper2B0]
  ring

/-- `B(c₂, ·)` in the `c₂`-adapted coordinates. -/
theorem paper2B0_split_c2 (s t : ℝ) :
    paper2B0 (-5) 3 (-5 * s + 3 * t) (3 * s + -1 * t) = 2 * paper2Q0 (-5) 3 * s := by
  rw [paper2B0, paper2Q0]
  ring

/-- The determinant bookkeeping `(det(c₁|e₁))² · det A = 2Q(c₁) · B(e₁,e₁)`,
i.e. `(-1)² · (-5) = (-5) · 1`. -/
theorem paper2_det_bookkeeping_c1 :
    (0 * 0 - 1 * 1 : ℝ) ^ 2 * (-5) = 2 * paper2Q0 0 1 * paper2B0 1 0 1 0 := by
  rw [paper2Q0, paper2B0]
  norm_num

/-- The determinant bookkeeping `(det(c₂|e₂))² · det A = 2Q(c₂) · B(e₂,e₂)`,
i.e. `(-4)² · (-5) = (-20) · 4`. -/
theorem paper2_det_bookkeeping_c2 :
    ((-5) * (-1) - 3 * 3 : ℝ) ^ 2 * (-5) = 2 * paper2Q0 (-5) 3 * paper2B0 3 (-1) 3 (-1) := by
  rw [paper2Q0, paper2B0]
  norm_num

/-! ## Zwegers' `ρ`, and the Gaussian majorant that makes Lemma 2.8's
left-hand side a convergent integral

`ρ = ρ^{c₁} - ρ^{c₂}` with `ρ^c(a;τ) = E(B(c,a)·y^{1/2}/√(-Q(c)))`.  The
integrand `ρ(a;τ)e^{2πiQ(a)τ}` is *not* obviously integrable: `Q` is indefinite,
so `|e^{2πiQ(a)τ}| = e^{-2πQ(a)y}` grows in the directions where `Q < 0`.  What
saves it is that `ρ` decays there.  The bound proved here is uniform and
explicit,

  `|ρ(a;τ)| · e^{-2πQ(a)y} ≤ 10 · e^{-2πy(a₁²+a₂²)/100}`,

so the integrand is dominated by a Gaussian and the left-hand side of Lemma 2.8
converges absolutely.

Two mechanisms.  Away from the hyperplanes `B(c_j,a) = 0`, the Mills bound
pairs with `e^{-2πQ(a)y}` to give exactly `e^{-2πy·Q_{c_j}(a)}`; that
cancellation is `paper2_kernel_exponent_c1` / `_c2`, and it is where Lemma 2.5
enters.  On the slab, where the two signs disagree, `|a₁| ≥ 3|a₂|` forces `Q`
itself to be bounded below by a positive multiple of `|a|²`. -/

/-- Zwegers' `ρ = ρ^{c₁} - ρ^{c₂}` at this paper's data. -/
noncomputable def paper2Rho (a : ℝ × ℝ) (τ : ℂ) : ℝ :=
  zwegersErrorKernel (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) -
    zwegersErrorKernel (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))

/-- The Lemma 2.8 integrand `ρ(a;τ)·e^{2πiQ(a)τ + 2πiB(a,α)}`. -/
noncomputable def paper2FourierIntegrand (τ : ℂ) (α a : ℝ × ℝ) : ℂ :=
  ((paper2Rho a τ : ℝ) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 a.2 : ℝ) : ℂ) * τ +
      2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 a.1 a.2 α.1 α.2 : ℝ) : ℂ))

theorem paper2_sqrt_neg_Q0_c1_pos : 0 < Real.sqrt (-paper2Q0 0 1) := by
  rw [paper2Q0_c1_val]
  exact Real.sqrt_pos.2 (by norm_num)

theorem paper2_sqrt_neg_Q0_c2_pos : 0 < Real.sqrt (-paper2Q0 (-5) 3) := by
  rw [paper2Q0_c2_val]
  exact Real.sqrt_pos.2 (by norm_num)

theorem differentiable_zwegersErrorKernel : Differentiable ℝ zwegersErrorKernel :=
  fun z => (hasDerivAt_zwegersErrorKernel z).differentiableAt

theorem continuous_zwegersErrorKernel : Continuous zwegersErrorKernel :=
  differentiable_zwegersErrorKernel.continuous

theorem abs_zwegersErrorKernel_le_one (z : ℝ) : |zwegersErrorKernel z| ≤ 1 :=
  abs_le.2 ⟨neg_one_le_zwegersErrorKernel z, zwegersErrorKernel_le_one z⟩

theorem paper2_abs_real_sign_le_one (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num

theorem paper2_exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h2 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

/-- `|E(z) - sgn z| · e^{πz²} ≤ 4`, uniformly in `z`: the Mills bound above the
threshold `π|z| ≥ 1`, and the crude bound `|E - sgn| ≤ 2` below it, where
`e^{πz²} ≤ e^{1/2} ≤ 2`.  This is the form in which the error kernel cancels
the growth of `e^{-2πQ(a)y}`. -/
theorem paper2_kernel_sub_sign_mul_exp_le (z : ℝ) :
    |zwegersErrorKernel z - Real.sign z| * Real.exp (Real.pi * z ^ 2) ≤ 4 := by
  have hcrude : |zwegersErrorKernel z - Real.sign z| ≤ 2 := by
    have h1 := abs_le.1 (abs_zwegersErrorKernel_le_one z)
    have h2 := abs_le.1 (paper2_abs_real_sign_le_one z)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  by_cases hbig : 1 ≤ Real.pi * |z|
  · have hpi := Real.pi_pos
    have hz : z ≠ 0 := by
      intro h
      rw [h] at hbig
      simp at hbig
      linarith
    have hpz : 0 < Real.pi * |z| := by linarith
    have hmills := abs_zwegersErrorKernel_sub_sign_le hz
    have hstep : |zwegersErrorKernel z - Real.sign z| * Real.exp (Real.pi * z ^ 2) ≤
        Real.exp (-Real.pi * z ^ 2) / (Real.pi * |z|) * Real.exp (Real.pi * z ^ 2) := by
      gcongr
    have hcollapse : Real.exp (-Real.pi * z ^ 2) / (Real.pi * |z|) * Real.exp (Real.pi * z ^ 2) =
        1 / (Real.pi * |z|) := by
      rw [div_mul_eq_mul_div, ← Real.exp_add,
        show -Real.pi * z ^ 2 + Real.pi * z ^ 2 = 0 by ring, Real.exp_zero]
    have hle : 1 / (Real.pi * |z|) ≤ 1 := by
      rw [div_le_one hpz]
      exact hbig
    linarith
  · rw [not_le] at hbig
    have hpi3 := Real.pi_gt_three
    have hpi4 := Real.pi_le_four
    have habs : (0 : ℝ) ≤ |z| := abs_nonneg z
    have hzle : |z| ≤ 1 / 3 := by nlinarith
    have hexp : Real.exp (Real.pi * z ^ 2) ≤ 2 := by
      refine le_trans (Real.exp_le_exp.2 ?_) paper2_exp_half_le_two
      have hsq : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      rw [hsq]
      nlinarith
    have := mul_le_mul hcrude hexp (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 2)
    linarith

theorem paper2_sign_ne_mul_nonpos {u v : ℝ} (h : Real.sign u ≠ Real.sign v) : u * v ≤ 0 := by
  by_contra hc0
  have hc : 0 < u * v := not_le.1 hc0
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hv : v < 0 := by nlinarith
    exact h (by rw [Real.sign_of_neg hu, Real.sign_of_neg hv])
  · rw [hu, zero_mul] at hc
    exact absurd hc (lt_irrefl 0)
  · have hv : 0 < v := by nlinarith
    exact h (by rw [Real.sign_of_pos hu, Real.sign_of_pos hv])

theorem paper2_mul_div_nonpos {b₁ b₂ u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (h : b₁ * u / v * (b₂ * u / w) ≤ 0) : b₁ * b₂ ≤ 0 := by
  by_contra hc0
  have hc : 0 < b₁ * b₂ := not_le.1 hc0
  have hrw : b₁ * u / v * (b₂ * u / w) = b₁ * b₂ * (u * u / (v * w)) := by
    field_simp
  rw [hrw] at h
  have hpos : 0 < b₁ * b₂ * (u * u / (v * w)) := mul_pos hc (by positivity)
  linarith

/-- **The slab bound in real variables.**  Where the two sign functions
disagree, `|a₁| ≥ 3|a₂|`, hence `Q(a) ≥ (a₁²+a₂²)/100`.  This is the
real-variable form of the support bound proved for the lattice sum in
`Ch10_Paper2_SignBridge`. -/
theorem paper2_slab_Q0_lower {a : ℝ × ℝ}
    (h : paper2B0 0 1 a.1 a.2 * paper2B0 (-5) 3 a.1 a.2 ≤ 0) :
    (a.1 ^ 2 + a.2 ^ 2) / 100 ≤ paper2Q0 a.1 a.2 := by
  rw [paper2B0, paper2B0] at h
  rw [paper2Q0]
  have hkey : 9 * a.2 ^ 2 ≤ a.1 ^ 2 := by nlinarith [sq_nonneg (a.1 + 3 * a.2)]
  nlinarith [hkey, sq_nonneg a.2]

/-! ### The majorant, assembled from abstract pieces -/

theorem paper2_exp_le_exp_of_le {y c d : ℝ} (hy : 0 ≤ y) (hcd : c ≤ d) :
    Real.exp (-(2 * Real.pi * y * d)) ≤ Real.exp (-(2 * Real.pi * y * c)) := by
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_nonneg (mul_nonneg (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 2 * Real.pi) hy)
    (sub_nonneg.2 hcd)]

/-- One Mills term: `|E(z) - sgn z| · e^{-2πQy} ≤ 4 e^{-2πy·Q_c}`, given the
exponent cancellation `-πz² - 2πQy = -2πy·Q_c`. -/
theorem paper2_mills_term_bound {z Q y Qc : ℝ}
    (hexp : -Real.pi * z ^ 2 - 2 * Real.pi * Q * y = -(2 * Real.pi * y * Qc)) :
    |zwegersErrorKernel z - Real.sign z| * Real.exp (-(2 * Real.pi * y * Q)) ≤
      4 * Real.exp (-(2 * Real.pi * y * Qc)) := by
  have hsplit : Real.exp (-(2 * Real.pi * y * Q)) =
      Real.exp (-(2 * Real.pi * y * Qc)) * Real.exp (Real.pi * z ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    linarith
  have hk := paper2_kernel_sub_sign_mul_exp_le z
  have hpos : (0 : ℝ) < Real.exp (-(2 * Real.pi * y * Qc)) := Real.exp_pos _
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hk hpos.le]

/-- The three-term triangle estimate, in the abstract. -/
theorem paper2_rho_bound_abstract {e1 e2 s1 s2 EQ EG : ℝ} (hEQ : 0 < EQ)
    (h1 : |e1 - s1| * EQ ≤ 4 * EG) (h2 : |e2 - s2| * EQ ≤ 4 * EG)
    (hs : |s1 - s2| * EQ ≤ 2 * EG) : |e1 - e2| * EQ ≤ 10 * EG := by
  have htri : |e1 - e2| ≤ |e1 - s1| + |e2 - s2| + |s1 - s2| := by
    rw [abs_le]
    constructor <;>
      linarith [neg_abs_le (e1 - s1), le_abs_self (e1 - s1), neg_abs_le (e2 - s2),
        le_abs_self (e2 - s2), neg_abs_le (s1 - s2), le_abs_self (s1 - s2)]
  nlinarith [mul_le_mul_of_nonneg_right htri hEQ.le]

/-- **The uniform Gaussian majorant.** -/
theorem paper2_abs_rho_mul_exp_le {τ : ℂ} (hτ : 0 < τ.im) (a : ℝ × ℝ) :
    |paper2Rho a τ| * Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) ≤
      10 * Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
  have hRnn : (0 : ℝ) ≤ a.1 ^ 2 + a.2 ^ 2 := by positivity
  have hc1 : (a.1 ^ 2 + a.2 ^ 2) / 100 ≤ paper2Qc1 a.1 a.2 := by
    linarith [paper2Qc1_lower a.1 a.2]
  have hc2 : (a.1 ^ 2 + a.2 ^ 2) / 100 ≤ paper2Qc2 a.1 a.2 := by
    linarith [paper2Qc2_lower a.1 a.2]
  have hE1 := paper2_mills_term_bound (paper2_kernel_exponent_c1 hτ.le a.1 a.2)
  have hE2 := paper2_mills_term_bound (paper2_kernel_exponent_c2 hτ.le a.1 a.2)
  have hd1 := paper2_exp_le_exp_of_le hτ.le hc1
  have hd2 := paper2_exp_le_exp_of_le hτ.le hc2
  have hS : |Real.sign (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) -
      Real.sign (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))| *
      Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) ≤
      2 * Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
    by_cases hs : Real.sign (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) =
        Real.sign (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))
    · rw [hs, sub_self, abs_zero, zero_mul]
      positivity
    · have hprod := paper2_mul_div_nonpos (Real.sqrt_pos.2 hτ) paper2_sqrt_neg_Q0_c1_pos
        paper2_sqrt_neg_Q0_c2_pos (paper2_sign_ne_mul_nonpos hs)
      have hde := paper2_exp_le_exp_of_le hτ.le (paper2_slab_Q0_lower hprod)
      have hb : |Real.sign (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) -
          Real.sign (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
            Real.sqrt (-paper2Q0 (-5) 3))| ≤ 2 := by
        have h1 := abs_le.1 (paper2_abs_real_sign_le_one
          (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)))
        have h2 := abs_le.1 (paper2_abs_real_sign_le_one
          (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      exact mul_le_mul hb hde (Real.exp_pos _).le (by norm_num)
  rw [paper2Rho]
  refine paper2_rho_bound_abstract (Real.exp_pos _) ?_ ?_ hS
  · exact le_trans hE1 (by linarith)
  · exact le_trans hE2 (by linarith)

/-! ### Integrability of the Lemma 2.8 integrand

The majorant is a product of two one-dimensional Gaussians, so the integrand of
Lemma 2.8 is absolutely integrable on `ℝ²`.  This is what makes the left-hand
side of Lemma 2.8 a well-defined complex number. -/

theorem continuous_paper2Rho (τ : ℂ) : Continuous (fun a : ℝ × ℝ => paper2Rho a τ) := by
  have hB1 : Continuous (fun a : ℝ × ℝ =>
      paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) := by
    unfold paper2B0
    fun_prop
  have hB2 : Continuous (fun a : ℝ × ℝ =>
      paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by
    unfold paper2B0
    fun_prop
  exact (continuous_zwegersErrorKernel.comp hB1).sub (continuous_zwegersErrorKernel.comp hB2)

theorem continuous_paper2FourierIntegrand (τ : ℂ) (α : ℝ × ℝ) :
    Continuous (fun a : ℝ × ℝ => paper2FourierIntegrand τ α a) := by
  unfold paper2FourierIntegrand
  refine Continuous.mul (Complex.continuous_ofReal.comp (continuous_paper2Rho τ)) ?_
  refine Complex.continuous_exp.comp ?_
  unfold paper2Q0 paper2B0
  fun_prop

theorem paper2_norm_fourierIntegrand (τ : ℂ) (α a : ℝ × ℝ) :
    ‖paper2FourierIntegrand τ α a‖ =
      |paper2Rho a τ| * Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 a.2 : ℝ) : ℂ) * τ +
      2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 a.1 a.2 α.1 α.2 : ℝ) : ℂ)).re =
      -(2 * Real.pi * τ.im * paper2Q0 a.1 a.2) := by
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
    ring
  rw [paper2FourierIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]

theorem paper2_integrable_majorant {τ : ℂ} (hτ : 0 < τ.im) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ =>
      10 * Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100)))) := by
  have hc : 0 < Real.pi * τ.im / 50 := by positivity
  have h1 : MeasureTheory.Integrable
      (fun x : ℝ => Real.exp (-(Real.pi * τ.im / 50) * x ^ 2)) := integrable_exp_neg_mul_sq hc
  have h2 := (h1.mul_prod h1).const_mul (10 : ℝ)
  refine h2.congr (Filter.Eventually.of_forall fun a => ?_)
  show 10 * (Real.exp (-(Real.pi * τ.im / 50) * a.1 ^ 2) *
      Real.exp (-(Real.pi * τ.im / 50) * a.2 ^ 2)) =
    10 * Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100)))
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- **The Lemma 2.8 integrand is absolutely integrable on `ℝ²`.** -/
theorem paper2_integrable_fourierIntegrand {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ => paper2FourierIntegrand τ α a) := by
  refine MeasureTheory.Integrable.mono' (paper2_integrable_majorant hτ)
    (continuous_paper2FourierIntegrand τ α).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [paper2_norm_fourierIntegrand]
  exact paper2_abs_rho_mul_exp_le hτ a

/-! ## `A c₁`, `A c₂`, and Zwegers' (2.23)

`(Ac)_l` is by definition the `a_l`-derivative of `a ↦ B(c,a)`, so rather than
transcribing `Ac₁ = (0,-5)` and `Ac₂ = (-5,-15)` they are *computed* here, as
the four derivative facts below.  Zwegers' (2.23),

  `∂ρ/∂a_l = (Ac₁)_l/√(-Q(c₁))·y^{1/2}·E'(B(c₁,a)y^{1/2}/√(-Q(c₁)))`
          `- (Ac₂)_l/√(-Q(c₂))·y^{1/2}·E'(B(c₂,a)y^{1/2}/√(-Q(c₂)))`,

then follows by the chain rule from `E'(z) = 2e^{-πz²}`, which is
`hasDerivAt_zwegersErrorKernel`.  The coefficients are left in the displayed
`(Ac)_l` form so the shape of (2.23) stays visible. -/

theorem paper2_hasDerivAt_B0_c1_fst (X Y : ℝ) :
    HasDerivAt (fun x : ℝ => paper2B0 0 1 x Y) 0 X := by
  have hfun : (fun x : ℝ => paper2B0 0 1 x Y) = fun _ : ℝ => -(5 * Y) := by
    funext x
    rw [paper2B0]
    ring
  rw [hfun]
  exact hasDerivAt_const X _

theorem paper2_hasDerivAt_B0_c1_snd (X Y : ℝ) :
    HasDerivAt (fun y : ℝ => paper2B0 0 1 X y) (-5) Y := by
  have hfun : (fun y : ℝ => paper2B0 0 1 X y) = fun y : ℝ => -5 * y := by
    funext y
    rw [paper2B0]
    ring
  rw [hfun]
  simpa using (hasDerivAt_id Y).const_mul (-5 : ℝ)

theorem paper2_hasDerivAt_B0_c2_fst (X Y : ℝ) :
    HasDerivAt (fun x : ℝ => paper2B0 (-5) 3 x Y) (-5) X := by
  have hfun : (fun x : ℝ => paper2B0 (-5) 3 x Y) = fun x : ℝ => -5 * x + -(15 * Y) := by
    funext x
    rw [paper2B0]
    ring
  rw [hfun]
  simpa using ((hasDerivAt_id X).const_mul (-5 : ℝ)).add_const (-(15 * Y))

theorem paper2_hasDerivAt_B0_c2_snd (X Y : ℝ) :
    HasDerivAt (fun y : ℝ => paper2B0 (-5) 3 X y) (-15) Y := by
  have hfun : (fun y : ℝ => paper2B0 (-5) 3 X y) = fun y : ℝ => -15 * y + -5 * X := by
    funext y
    rw [paper2B0]
    ring
  rw [hfun]
  simpa using ((hasDerivAt_id Y).const_mul (-15 : ℝ)).add_const (-5 * X)

/-- The scaled `c₁` argument of `E`, as a function of `a₁`, together with its
derivative `(Ac₁)_1 · y^{1/2}/√(-Q(c₁))`. -/
theorem paper2_hasDerivAt_arg_c1_fst (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun x : ℝ => paper2B0 0 1 x a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))
      (0 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) a.1 := by
  have h := ((paper2_hasDerivAt_B0_c1_fst a.1 a.2).mul_const (Real.sqrt τ.im)).div_const
    (Real.sqrt (-paper2Q0 0 1))
  convert h using 1
  ring

theorem paper2_hasDerivAt_arg_c2_fst (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun x : ℝ => paper2B0 (-5) 3 x a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 (-5) 3))
      (-5 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))) a.1 := by
  have h := ((paper2_hasDerivAt_B0_c2_fst a.1 a.2).mul_const (Real.sqrt τ.im)).div_const
    (Real.sqrt (-paper2Q0 (-5) 3))
  convert h using 1
  ring

theorem paper2_hasDerivAt_arg_c1_snd (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => paper2B0 0 1 a.1 y * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))
      (-5 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) a.2 := by
  have h := ((paper2_hasDerivAt_B0_c1_snd a.1 a.2).mul_const (Real.sqrt τ.im)).div_const
    (Real.sqrt (-paper2Q0 0 1))
  convert h using 1
  ring

theorem paper2_hasDerivAt_arg_c2_snd (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => paper2B0 (-5) 3 a.1 y * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 (-5) 3))
      (-15 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))) a.2 := by
  have h := ((paper2_hasDerivAt_B0_c2_snd a.1 a.2).mul_const (Real.sqrt τ.im)).div_const
    (Real.sqrt (-paper2Q0 (-5) 3))
  convert h using 1
  ring

/-- **Zwegers' (2.23) at `l = 1`.**  The `a₁`-partial of `ρ` is a difference of
two Gaussians, with coefficients `(Ac₁)_1 = 0` and `(Ac₂)_1 = -5`. -/
theorem paper2_hasDerivAt_rho_fst (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun x : ℝ => paper2Rho (x, a.2) τ)
      (2 * zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) *
          (0 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) -
        2 * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
            Real.sqrt (-paper2Q0 (-5) 3)) *
          (-5 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))) a.1 := by
  have hfun : (fun x : ℝ => paper2Rho (x, a.2) τ) =
      fun x : ℝ =>
        zwegersErrorKernel (paper2B0 0 1 x a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) -
          zwegersErrorKernel (paper2B0 (-5) 3 x a.2 * Real.sqrt τ.im /
            Real.sqrt (-paper2Q0 (-5) 3)) := rfl
  rw [hfun]
  exact ((hasDerivAt_zwegersErrorKernel _).comp a.1 (paper2_hasDerivAt_arg_c1_fst τ a)).sub
    ((hasDerivAt_zwegersErrorKernel _).comp a.1 (paper2_hasDerivAt_arg_c2_fst τ a))

/-- **Zwegers' (2.23) at `l = 2`**, with `(Ac₁)_2 = -5` and `(Ac₂)_2 = -15`. -/
theorem paper2_hasDerivAt_rho_snd (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => paper2Rho (a.1, y) τ)
      (2 * zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) *
          (-5 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) -
        2 * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
            Real.sqrt (-paper2Q0 (-5) 3)) *
          (-15 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))) a.2 := by
  have hfun : (fun y : ℝ => paper2Rho (a.1, y) τ) =
      fun y : ℝ =>
        zwegersErrorKernel (paper2B0 0 1 a.1 y * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) -
          zwegersErrorKernel (paper2B0 (-5) 3 a.1 y * Real.sqrt τ.im /
            Real.sqrt (-paper2Q0 (-5) 3)) := rfl
  rw [hfun]
  exact ((hasDerivAt_zwegersErrorKernel _).comp a.2 (paper2_hasDerivAt_arg_c1_snd τ a)).sub
    ((hasDerivAt_zwegersErrorKernel _).comp a.2 (paper2_hasDerivAt_arg_c2_snd τ a))

/-! ## The linear change of variables

`(s,t) ↦ s·c + t·e` as a linear map on `ℝ²`, with its determinant and the
resulting `|det|⁻¹` in the integral.  The two instances are the ones §4 needs:
`(c₁|e₁)` with determinant `-1` and `(c₂|e₂)` with determinant `-4`.  The
bookkeeping identity `(det(c|C))²·det A = 2Q(c)·B(e,e)` — `(-1)²(-5) = (-5)(1)`
and `(-4)²(-5) = (-20)(4)` — is `paper2_det_bookkeeping_c1/c2` above, and it is
what makes the `|det|` cancel into `1/√(-det A) = 1/√5` at the end. -/

/-- The linear map with columns `(a,c)` and `(b,d)`. -/
noncomputable def paper2SplitMap (a b c d : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![a, b; c, d]

theorem paper2SplitMap_apply (a b c d : ℝ) (x : ℝ × ℝ) :
    paper2SplitMap a b c d x = (a * x.1 + b * x.2, c * x.1 + d * x.2) :=
  Matrix.toLin_finTwoProd_apply a b c d x

theorem paper2SplitMap_det (a b c d : ℝ) :
    LinearMap.det (paper2SplitMap a b c d) = a * d - b * c := by
  rw [paper2SplitMap, LinearMap.det_toLin, Matrix.det_fin_two_of]

theorem paper2_det_c1_e1 : LinearMap.det (paper2SplitMap 0 1 1 0) = -1 := by
  rw [paper2SplitMap_det]
  norm_num

theorem paper2_det_c2_e2 : LinearMap.det (paper2SplitMap (-5) 3 3 (-1)) = -4 := by
  rw [paper2SplitMap_det]
  norm_num

/-- **The change of variables.**  Composing with an invertible linear map
multiplies the integral by `|det|⁻¹`. -/
theorem paper2_integral_comp_splitMap {a b c d : ℝ} (hdet : a * d - b * c ≠ 0)
    {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    (∫ x : ℝ × ℝ, f (paper2SplitMap a b c d x)) = |a * d - b * c|⁻¹ • ∫ y : ℝ × ℝ, f y := by
  have hdet' : LinearMap.det (paper2SplitMap a b c d) ≠ 0 := by
    rw [paper2SplitMap_det]
    exact hdet
  have hmeas : AEMeasurable (⇑(paper2SplitMap a b c d))
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) :=
    ((paper2SplitMap a b c d).continuous_of_finiteDimensional).measurable.aemeasurable
  have hint := MeasureTheory.integral_map (φ := ⇑(paper2SplitMap a b c d)) hmeas
    (f := f) hf.aestronglyMeasurable
  rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) hdet',
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    paper2SplitMap_det, abs_inv] at hint
  exact hint.symm

/-- The `c₁`-adapted substitution is measure preserving (`|det| = 1`). -/
theorem paper2_integral_comp_c1 {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    (∫ x : ℝ × ℝ, f (0 * x.1 + 1 * x.2, 1 * x.1 + 0 * x.2)) = ∫ y : ℝ × ℝ, f y := by
  have h := paper2_integral_comp_splitMap (a := 0) (b := 1) (c := 1) (d := 0)
    (by norm_num) hf
  simp only [paper2SplitMap_apply] at h
  rw [h]
  norm_num

/-- The `c₂`-adapted substitution contributes `|det|⁻¹ = 1/4`. -/
theorem paper2_integral_comp_c2 {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    (∫ x : ℝ × ℝ, f (-5 * x.1 + 3 * x.2, 3 * x.1 + -1 * x.2)) =
      (4 : ℝ)⁻¹ • ∫ y : ℝ × ℝ, f y := by
  have h := paper2_integral_comp_splitMap (a := -5) (b := 3) (c := 3) (d := -1)
    (by norm_num) hf
  simp only [paper2SplitMap_apply] at h
  rw [h]
  norm_num

/-! ## Oddness of `ρ`, and the weighted majorant

`E` is odd and `B(c,·)` is linear, so `ρ(-a;τ) = -ρ(a;τ)`; this is what makes
the constant in step (v) vanish.  The weighted majorant `(1+|a|)·|ρ|e^{-2πQy}`
is what dominates the `α`-derivative of the pre-integration-by-parts
integrand. -/

theorem paper2Rho_neg (a : ℝ × ℝ) (τ : ℂ) : paper2Rho (-a) τ = -paper2Rho a τ := by
  have h1 : paper2B0 0 1 (-a).1 (-a).2 = -paper2B0 0 1 a.1 a.2 := by
    simp only [Prod.fst_neg, Prod.snd_neg, paper2B0]
    ring
  have h2 : paper2B0 (-5) 3 (-a).1 (-a).2 = -paper2B0 (-5) 3 a.1 a.2 := by
    simp only [Prod.fst_neg, Prod.snd_neg, paper2B0]
    ring
  rw [paper2Rho, paper2Rho, h1, h2, neg_mul, neg_div, zwegersErrorKernel_neg, neg_mul, neg_div,
    zwegersErrorKernel_neg]
  ring

/-! ### `B(a,·)` as a continuous linear functional -/

/-- `B(a, ·) : ℝ² → ℝ`, as a continuous linear map. -/
noncomputable def paper2BCLM (a : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ) - (5 * a.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem paper2BCLM_apply (a v : ℝ × ℝ) : paper2BCLM a v = paper2B0 a.1 a.2 v.1 v.2 := by
  simp only [paper2BCLM, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, paper2B0]
  ring

/-- `B(a, ·) : ℝ² → ℂ`, as a continuous linear map. -/
noncomputable def paper2BCLMc (a : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (paper2BCLM a)

@[simp] theorem paper2BCLMc_apply (a v : ℝ × ℝ) :
    paper2BCLMc a v = ((paper2B0 a.1 a.2 v.1 v.2 : ℝ) : ℂ) := by
  simp [paper2BCLMc]

theorem paper2BCLMc_norm_le (a : ℝ × ℝ) : ‖paper2BCLMc a‖ ≤ |a.1| + 5 * |a.2| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [paper2BCLMc_apply, Complex.norm_real, Real.norm_eq_abs, paper2B0]
  have h1 : |v.1| ≤ ‖v‖ := by
    simpa using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by
    simpa using norm_snd_le v
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hb : |a.1 * v.1 - 5 * (a.2 * v.2)| ≤ |a.1| * |v.1| + 5 * |a.2| * |v.2| := by
    calc |a.1 * v.1 - 5 * (a.2 * v.2)| ≤ |a.1 * v.1| + |5 * (a.2 * v.2)| := abs_sub _ _
      _ = |a.1| * |v.1| + 5 * |a.2| * |v.2| := by
          rw [abs_mul, abs_mul, abs_mul]
          norm_num
          ring
  nlinarith [abs_nonneg a.1, abs_nonneg a.2, abs_nonneg v.1, abs_nonneg v.2]

/-! ### The dominating function -/

noncomputable def paper2FderivBound (τ : ℂ) (a : ℝ × ℝ) : ℝ :=
  20 * Real.pi * (|a.1| + 5 * |a.2|) *
    Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100)))

theorem paper2_integrable_abs_mul_gaussian {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun x : ℝ => |x| * Real.exp (-c * x ^ 2)) := by
  refine ((integrable_mul_exp_neg_mul_sq hc).abs).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show |x * Real.exp (-c * x ^ 2)| = |x| * Real.exp (-c * x ^ 2)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]

theorem paper2_integrable_fderivBound {τ : ℂ} (hτ : 0 < τ.im) :
    MeasureTheory.Integrable (paper2FderivBound τ) := by
  have hc : 0 < Real.pi * τ.im / 50 := by positivity
  have h1 := paper2_integrable_abs_mul_gaussian hc
  have h0 := integrable_exp_neg_mul_sq hc
  have hA := (h1.mul_prod h0).const_mul (20 * Real.pi)
  have hB := (h0.mul_prod h1).const_mul (100 * Real.pi)
  refine (hA.add hB).congr (Filter.Eventually.of_forall fun a => ?_)
  show 20 * Real.pi * (|a.1| * Real.exp (-(Real.pi * τ.im / 50) * a.1 ^ 2) *
        Real.exp (-(Real.pi * τ.im / 50) * a.2 ^ 2)) +
      100 * Real.pi * (Real.exp (-(Real.pi * τ.im / 50) * a.1 ^ 2) *
        (|a.2| * Real.exp (-(Real.pi * τ.im / 50) * a.2 ^ 2))) =
    paper2FderivBound τ a
  have hex : Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) =
      Real.exp (-(Real.pi * τ.im / 50) * a.1 ^ 2) *
        Real.exp (-(Real.pi * τ.im / 50) * a.2 ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [paper2FderivBound, hex]
  ring

/-! ### The `α`-Fréchet derivative of the integrand, and differentiation under
the integral (step (2))

`α ↦ ρ(a;τ)e^{2πi(Q(a)τ + B(a,α))}` is a constant times the exponential of an
`ℝ`-linear functional of `α`, so its Fréchet derivative is
`B(a,·) ↦ 2πi·(integrand)·B(a,·)`.  Crucially `|e^{2πiB(a,α)}| = 1` for real
`α`, so the derivative's norm bound is **independent of `α`**; that lets
`hasFDerivAt_integral_of_dominated_of_fderiv_le` be applied with `s = univ`,
which removes the ball bookkeeping entirely. -/

theorem paper2_norm_two_pi_I : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem paper2B0_abs_le (a v : ℝ × ℝ) :
    |paper2B0 a.1 a.2 v.1 v.2| ≤ (|a.1| + 5 * |a.2|) * ‖v‖ := by
  have h1 : |v.1| ≤ ‖v‖ := by simpa using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa using norm_snd_le v
  have hb : |a.1 * v.1 - 5 * (a.2 * v.2)| ≤ |a.1| * |v.1| + 5 * |a.2| * |v.2| := by
    calc |a.1 * v.1 - 5 * (a.2 * v.2)| ≤ |a.1 * v.1| + |5 * (a.2 * v.2)| := abs_sub _ _
      _ = |a.1| * |v.1| + 5 * |a.2| * |v.2| := by
          rw [abs_mul, abs_mul, abs_mul]
          norm_num
          ring
  rw [paper2B0]
  nlinarith [abs_nonneg a.1, abs_nonneg a.2, abs_nonneg v.1, abs_nonneg v.2]

/-- The `α`-derivative of the integrand, as an explicit continuous linear map. -/
noncomputable def paper2FourierFderiv (τ : ℂ) (α a : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (paper2BCLM a).smulRight (2 * (Real.pi : ℂ) * Complex.I * paper2FourierIntegrand τ α a)

theorem paper2_hasFDerivAt_fourierIntegrand (τ : ℂ) (a α : ℝ × ℝ) :
    HasFDerivAt (fun β : ℝ × ℝ => paper2FourierIntegrand τ β a)
      (paper2FourierFderiv τ α a) α := by
  have h0 : HasFDerivAt (fun β : ℝ × ℝ => ((paper2B0 a.1 a.2 β.1 β.2 : ℝ) : ℂ))
      (paper2BCLMc a) α := by
    have hfun : (fun β : ℝ × ℝ => ((paper2B0 a.1 a.2 β.1 β.2 : ℝ) : ℂ)) =
        ⇑(paper2BCLMc a) := by
      funext β
      rw [paper2BCLMc_apply]
    rw [hfun]
    exact (paper2BCLMc a).hasFDerivAt
  have hL := (h0.const_mul (2 * (Real.pi : ℂ) * Complex.I)).const_add
    (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 a.2 : ℝ) : ℂ) * τ)
  have hE := hL.cexp
  have hF := hE.const_mul ((paper2Rho a τ : ℝ) : ℂ)
  refine hF.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [paper2FourierFderiv, paper2FourierIntegrand, ContinuousLinearMap.smulRight_apply,
    paper2BCLM_apply, ContinuousLinearMap.smul_apply, paper2BCLMc_apply, smul_eq_mul,
    Complex.real_smul]
  ring

theorem paper2_norm_fourierFderiv_le {τ : ℂ} (hτ : 0 < τ.im) (α a : ℝ × ℝ) :
    ‖paper2FourierFderiv τ α a‖ ≤ paper2FderivBound τ a := by
  have hcnst : ‖2 * (Real.pi : ℂ) * Complex.I * paper2FourierIntegrand τ α a‖ ≤
      20 * Real.pi * Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
    rw [norm_mul, paper2_norm_two_pi_I, paper2_norm_fourierIntegrand]
    have := paper2_abs_rho_mul_exp_le hτ a
    nlinarith [Real.pi_pos]
  refine ContinuousLinearMap.opNorm_le_bound _ (by rw [paper2FderivBound]; positivity) fun v => ?_
  rw [paper2FourierFderiv, ContinuousLinearMap.smulRight_apply, norm_smul, paper2BCLM_apply,
    Real.norm_eq_abs, paper2FderivBound]
  have hB := paper2B0_abs_le a v
  have hnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hA : (0 : ℝ) ≤ |a.1| + 5 * |a.2| := by positivity
  have hE : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) :=
    (Real.exp_pos _).le
  nlinarith [abs_nonneg (paper2B0 a.1 a.2 v.1 v.2),
    norm_nonneg (2 * (Real.pi : ℂ) * Complex.I * paper2FourierIntegrand τ α a)]

theorem continuous_paper2BCLM : Continuous paper2BCLM := by
  unfold paper2BCLM
  exact (continuous_fst.smul continuous_const).sub
    ((continuous_const.mul continuous_snd).smul continuous_const)

theorem continuous_paper2FourierFderiv (τ : ℂ) (α : ℝ × ℝ) :
    Continuous (fun a : ℝ × ℝ => paper2FourierFderiv τ α a) := by
  unfold paper2FourierFderiv
  exact (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℂ).continuous₂.comp₂ continuous_paper2BCLM
    (continuous_const.mul (continuous_paper2FourierIntegrand τ α))

/-- **Differentiation under the integral sign (step (2)).**  The parameter is
`α ∈ ℝ²`; the dominating function is `paper2FderivBound`, uniform in `α`, which
is why `s = Set.univ` suffices. -/
theorem paper2_hasFDerivAt_integral {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    HasFDerivAt (fun β : ℝ × ℝ => ∫ a : ℝ × ℝ, paper2FourierIntegrand τ β a)
      (∫ a : ℝ × ℝ, paper2FourierFderiv τ α a) α :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := paper2FderivBound τ)
    (F' := fun β a => paper2FourierFderiv τ β a) Filter.univ_mem
    (Filter.Eventually.of_forall fun β =>
      (continuous_paper2FourierIntegrand τ β).aestronglyMeasurable)
    (paper2_integrable_fourierIntegrand hτ α)
    (continuous_paper2FourierFderiv τ α).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a β _ => paper2_norm_fourierFderiv_le hτ β a)
    (paper2_integrable_fderivBound hτ)
    (Filter.Eventually.of_forall fun a β _ => paper2_hasFDerivAt_fourierIntegrand τ a β)

/-! ### The phase, its `a`-derivative, and the `iτ̄` identity

Two ingredients for steps (3) and (4).  First the `a`-derivative of the phase,
which is what integration by parts moves onto `ρ`.  Second the identity
`2y + iτ = i·conj τ`, which is the reason the `c`-direction of the split
carries `conj τ` rather than `τ`: the Gaussian `E'` contributes a real
`4πQ(c)s²y` that combines with `2πiQ(c)s²τ` into `2πiQ(c)·conj τ·s²`. -/

/-- `2·Im τ + iτ = i·conj τ`. -/
theorem paper2_two_im_add_I_mul (τ : ℂ) :
    2 * ((τ.im : ℝ) : ℂ) + Complex.I * τ = Complex.I * (starRingEnd ℂ) τ := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

theorem paper2_hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 x := by
  simpa using Complex.ofRealCLM.hasDerivAt (x := x)

/-- The phase of the Lemma 2.8 integrand, `e^{2πi(Q(a)τ + B(a,α))}`. -/
noncomputable def paper2PhaseExp (τ : ℂ) (α a : ℝ × ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 a.2 : ℝ) : ℂ) * τ +
    2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 a.1 a.2 α.1 α.2 : ℝ) : ℂ))

theorem paper2FourierIntegrand_eq (τ : ℂ) (α a : ℝ × ℝ) :
    paper2FourierIntegrand τ α a = ((paper2Rho a τ : ℝ) : ℂ) * paper2PhaseExp τ α a := rfl

theorem paper2_hasDerivAt_phase_a_fst (τ : ℂ) (α a : ℝ × ℝ) :
    HasDerivAt (fun u : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 u a.2 : ℝ) : ℂ) * τ +
        2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 u a.2 α.1 α.2 : ℝ) : ℂ))
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ))) a.1 := by
  have hfun : (fun u : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 u a.2 : ℝ) : ℂ) * τ +
      2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 u a.2 α.1 α.2 : ℝ) : ℂ)) =
      fun u : ℝ => 2 * (Real.pi : ℂ) * Complex.I * τ * (((u : ℂ) ^ 2 - 5 * (a.2 : ℂ) ^ 2) / 2) +
        2 * (Real.pi : ℂ) * Complex.I * ((u : ℂ) * (α.1 : ℂ) - 5 * ((a.2 : ℂ) * (α.2 : ℂ))) := by
    funext u
    rw [paper2Q0, paper2B0]
    push_cast
    ring
  rw [hfun]
  have hu := paper2_hasDerivAt_ofReal a.1
  have h1 := (((hu.pow 2).sub_const (5 * (a.2 : ℂ) ^ 2)).div_const 2).const_mul
    (2 * (Real.pi : ℂ) * Complex.I * τ)
  have h2 := ((hu.mul_const (α.1 : ℂ)).sub_const (5 * ((a.2 : ℂ) * (α.2 : ℂ)))).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have h := h1.add h2
  convert h using 1
  ring

theorem paper2_hasDerivAt_phase_a_snd (τ : ℂ) (α a : ℝ × ℝ) :
    HasDerivAt (fun u : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 u : ℝ) : ℂ) * τ +
        2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 a.1 u α.1 α.2 : ℝ) : ℂ))
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ)))) a.2 := by
  have hfun : (fun u : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 u : ℝ) : ℂ) * τ +
      2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 a.1 u α.1 α.2 : ℝ) : ℂ)) =
      fun u : ℝ => 2 * (Real.pi : ℂ) * Complex.I * τ * (((a.1 : ℂ) ^ 2 - 5 * (u : ℂ) ^ 2) / 2) +
        2 * (Real.pi : ℂ) * Complex.I * ((a.1 : ℂ) * (α.1 : ℂ) - 5 * ((u : ℂ) * (α.2 : ℂ))) := by
    funext u
    rw [paper2Q0, paper2B0]
    push_cast
    ring
  rw [hfun]
  have hu := paper2_hasDerivAt_ofReal a.2
  have h1 := ((((hu.pow 2).const_mul (5 : ℂ)).const_sub ((a.1 : ℂ) ^ 2)).div_const 2).const_mul
    (2 * (Real.pi : ℂ) * Complex.I * τ)
  have h2 := (((hu.mul_const (α.2 : ℂ)).const_mul (5 : ℂ)).const_sub
    ((a.1 : ℂ) * (α.1 : ℂ))).const_mul (2 * (Real.pi : ℂ) * Complex.I)
  have h := h1.add h2
  convert h using 1
  ring

/-- The `a₁`-derivative of the phase: `∂/∂a₁ e^{2πi(Q(a)τ+B(a,α))}
= 2πi(τ(Aa)₁ + (Aα)₁)·e^{…}` with `(Aa)₁ = a₁`. -/
theorem paper2_hasDerivAt_phaseExp_a_fst (τ : ℂ) (α a : ℝ × ℝ) :
    HasDerivAt (fun u : ℝ => paper2PhaseExp τ α (u, a.2))
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a) a.1 := by
  have h := (paper2_hasDerivAt_phase_a_fst τ α a).cexp
  convert h using 1
  rw [paper2PhaseExp]
  ring

/-- The `a₂`-derivative of the phase, with `(Aa)₂ = -5a₂`. -/
theorem paper2_hasDerivAt_phaseExp_a_snd (τ : ℂ) (α a : ℝ × ℝ) :
    HasDerivAt (fun u : ℝ => paper2PhaseExp τ α (a.1, u))
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α a) a.2 := by
  have h := (paper2_hasDerivAt_phase_a_snd τ α a).cexp
  convert h using 1
  rw [paper2PhaseExp]
  ring

/-- **Zwegers' step-(1) identity**, at the level of the two exponent
derivatives: `(Aa)_l + (Aα)_l/τ = (1/τ)·(τ(Aa)_l + (Aα)_l)`.  This is why the
`α`-derivative of `e^{2πiQ(aτ+α)/τ}` is `1/τ` times its `a`-derivative. -/
theorem paper2_step1_exponent_rel {τ : ℂ} (hτ : τ ≠ 0) (u w : ℂ) :
    u + w / τ = 1 / τ * (τ * u + w) := by
  field_simp

/-! ### The exponent factorization in the split coordinates (the core of step (4))

After the `c`-adapted substitution, the differentiated integrand factors as a
product of two one-dimensional Gaussians — but at **two different** modular
arguments: `-conj τ` in the `c`-direction and `τ` in the transverse direction.
The `c`-direction argument is `-conj τ` because the real exponent `4πQ(c)s²y`
contributed by `E'` combines with `2πiQ(c)s²τ` through
`paper2_two_im_add_I_mul`.  Both identities below are stated in exactly the
shape `paper2_gaussian_1d` consumes. -/

theorem paper2_sqrt_neg_Q0_c1_sq : Real.sqrt (-paper2Q0 0 1) ^ 2 = 5 / 2 := by
  rw [paper2Q0_c1_val, show -(-(5 / 2) : ℝ) = 5 / 2 by norm_num]
  exact Real.sq_sqrt (by norm_num)

theorem paper2_sqrt_neg_Q0_c2_sq : Real.sqrt (-paper2Q0 (-5) 3) ^ 2 = 10 := by
  rw [paper2Q0_c2_val, show -(-10 : ℝ) = 10 by norm_num]
  exact Real.sq_sqrt (by norm_num)

theorem paper2B0_bilin_c1 (α : ℝ × ℝ) (s t : ℝ) :
    paper2B0 (0 * s + 1 * t) (1 * s + 0 * t) α.1 α.2 =
      s * paper2B0 0 1 α.1 α.2 + t * paper2B0 1 0 α.1 α.2 := by
  rw [paper2B0, paper2B0, paper2B0]
  ring

theorem paper2B0_bilin_c2 (α : ℝ × ℝ) (s t : ℝ) :
    paper2B0 (-5 * s + 3 * t) (3 * s + -1 * t) α.1 α.2 =
      s * paper2B0 (-5) 3 α.1 α.2 + t * paper2B0 3 (-1) α.1 α.2 := by
  rw [paper2B0, paper2B0, paper2B0]
  ring

/-- **The `c₁` factorization.**  `m = 5` at `-conj τ`, and `m = 1` at `τ`. -/
theorem paper2_phase_split_c1 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (s t : ℝ) :
    ((Real.exp (-Real.pi * (paper2B0 0 1 (0 * s + 1 * t) (1 * s + 0 * t) * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) *
        paper2PhaseExp τ α (0 * s + 1 * t, 1 * s + 0 * t) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) * (-(starRingEnd ℂ) τ) *
          ((s : ℝ) : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
            ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) * ((s : ℝ) : ℂ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * τ * ((t : ℝ) : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
            ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) * ((t : ℝ) : ℂ)) := by
  have hgauss : -Real.pi * (paper2B0 0 1 (0 * s + 1 * t) (1 * s + 0 * t) * Real.sqrt τ.im /
      Real.sqrt (-paper2Q0 0 1)) ^ 2 = -10 * Real.pi * s ^ 2 * τ.im := by
    rw [div_pow, mul_pow, Real.sq_sqrt hτ.le, paper2_sqrt_neg_Q0_c1_sq, paper2B0_split_c1,
      paper2Q0_c1_val]
    ring
  have hQ : paper2Q0 (0 * s + 1 * t) (1 * s + 0 * t) = -(5 / 2) * s ^ 2 + 1 / 2 * t ^ 2 := by
    rw [paper2Q0_split_c1, paper2Q0_c1_val, paper2B0_e1_e1]
  rw [Complex.ofReal_exp, paper2PhaseExp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hgauss, hQ, paper2B0_bilin_c1]
  push_cast
  linear_combination (-5 * (Real.pi : ℂ) * (s : ℂ) ^ 2) * paper2_two_im_add_I_mul τ

/-- **The `c₂` factorization.**  `m = 20` at `-conj τ`, and `m = 4` at `τ`. -/
theorem paper2_phase_split_c2 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (s t : ℝ) :
    ((Real.exp (-Real.pi * (paper2B0 (-5) 3 (-5 * s + 3 * t) (3 * s + -1 * t) * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) *
        paper2PhaseExp τ α (-5 * s + 3 * t, 3 * s + -1 * t) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) * (-(starRingEnd ℂ) τ) *
          ((s : ℝ) : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
            ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) * ((s : ℝ) : ℂ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) * τ * ((t : ℝ) : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
            ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) * ((t : ℝ) : ℂ)) := by
  have hgauss : -Real.pi * (paper2B0 (-5) 3 (-5 * s + 3 * t) (3 * s + -1 * t) * Real.sqrt τ.im /
      Real.sqrt (-paper2Q0 (-5) 3)) ^ 2 = -40 * Real.pi * s ^ 2 * τ.im := by
    rw [div_pow, mul_pow, Real.sq_sqrt hτ.le, paper2_sqrt_neg_Q0_c2_sq, paper2B0_split_c2,
      paper2Q0_c2_val]
    ring
  have hQ : paper2Q0 (-5 * s + 3 * t) (3 * s + -1 * t) = -10 * s ^ 2 + 2 * t ^ 2 := by
    rw [paper2Q0_split_c2, paper2Q0_c2_val, paper2B0_e2_e2]
    ring
  rw [Complex.ofReal_exp, paper2PhaseExp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hgauss, hQ, paper2B0_bilin_c2]
  push_cast
  linear_combination (-20 * (Real.pi : ℂ) * (s : ℂ) ^ 2) * paper2_two_im_add_I_mul τ

/-! ## Block 0: two small prerequisites -/

@[simp] theorem paper2_neg_conj_im (τ : ℂ) : (-(starRingEnd ℂ) τ).im = τ.im := by simp

theorem paper2_integrable_fourierFderiv {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ => paper2FourierFderiv τ α a) :=
  MeasureTheory.Integrable.mono' (paper2_integrable_fderivBound hτ)
    (continuous_paper2FourierFderiv τ α).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => paper2_norm_fourierFderiv_le hτ α a)

/-! ## Block 1: the Gaussian evaluation (Zwegers' step 4)

After the `c`-adapted substitution the differentiated integrand factors into two
one-dimensional Gaussians at the two modular arguments `-conj τ` and `τ`; the
two `paper2_gaussian_1d` applications then produce
`|det|·(√(m₁m₂))⁻¹ = 1/√5` for **both** cones.  That is not a coincidence: the
block identity `(det(c|e))²·det A = 2Q(c)·B(e,e)` gives
`m₁m₂ = -(det)²·det A = 5(det)²`, so `|det|/√(m₁m₂) = 1/√5` always.  Concretely
`c₁` contributes `1·(√5)⁻¹(√1)⁻¹` and `c₂` contributes `4·(√20)⁻¹(√4)⁻¹ =
4/(4√5)`. -/

theorem continuous_paper2PhaseExp (τ : ℂ) (α : ℝ × ℝ) :
    Continuous (fun a : ℝ × ℝ => paper2PhaseExp τ α a) := by
  unfold paper2PhaseExp
  refine Complex.continuous_exp.comp ?_
  unfold paper2Q0 paper2B0
  fun_prop

theorem continuous_paper2ConeGauss (c d : ℝ) (τ : ℂ) :
    Continuous (fun a : ℝ × ℝ => ((Real.exp (-Real.pi *
      (paper2B0 c d a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 c d)) ^ 2) : ℝ) : ℂ)) := by
  refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
  unfold paper2B0
  fun_prop

theorem paper2_sqrt_twenty : Real.sqrt 20 = 2 * Real.sqrt 5 := by
  rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

theorem paper2_sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The `c₂` constant: `|det| = 4` against `√(20·4) = √80 = 4√5` gives `1/√5`. -/
theorem paper2_const_c2 :
    ((4 : ℝ) : ℂ) * ((Real.sqrt 20 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 4 : ℝ) : ℂ)⁻¹ =
      ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ := by
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hr : (4 : ℝ) * (Real.sqrt 20)⁻¹ * (Real.sqrt 4)⁻¹ = (Real.sqrt 5)⁻¹ := by
    rw [paper2_sqrt_twenty, paper2_sqrt_four]
    field_simp
    ring
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hr

/-- The `c₁` constant: `|det| = 1` against `√(5·1) = √5`. -/
theorem paper2_const_c1 :
    ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 1 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ := by
  rw [Real.sqrt_one]
  norm_num

/-- **The `c₂` Gaussian evaluation.** -/
theorem paper2_gauss_eval_c2 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, ((Real.exp (-Real.pi * (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ *
        (((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
          ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
        (Complex.exp (-((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
            ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
            ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) ^ 2) / τ)) := by
  have hτ' : 0 < (-(starRingEnd ℂ) τ).im := by rw [paper2_neg_conj_im]; exact hτ
  have hcont : Continuous (fun a : ℝ × ℝ => ((Real.exp (-Real.pi * (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) :=
    (continuous_paper2ConeGauss (-5) 3 τ).mul (continuous_paper2PhaseExp τ α)
  have h1 : (∫ a : ℝ × ℝ, ((Real.exp (-Real.pi * (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      (4 : ℝ) • ∫ x : ℝ × ℝ, ((Real.exp (-Real.pi *
        (paper2B0 (-5) 3 (-5 * x.1 + 3 * x.2) (3 * x.1 + -1 * x.2) * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) *
        paper2PhaseExp τ α (-5 * x.1 + 3 * x.2, 3 * x.1 + -1 * x.2) := by
    rw [paper2_integral_comp_c2 hcont, smul_smul]
    norm_num
  have h2 : (∫ x : ℝ × ℝ, ((Real.exp (-Real.pi *
        (paper2B0 (-5) 3 (-5 * x.1 + 3 * x.2) (3 * x.1 + -1 * x.2) * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) *
        paper2PhaseExp τ α (-5 * x.1 + 3 * x.2, 3 * x.1 + -1 * x.2)) =
      ∫ x : ℝ × ℝ, (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
      (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
        ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) * ((s : ℝ) : ℂ))) x.1 * (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) * τ *
      ((t : ℝ) : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
        ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) * ((t : ℝ) : ℂ))) x.2 :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => paper2_phase_split_c2 hτ α x.1 x.2)
  have h3 : (∫ x : ℝ × ℝ, (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
      (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
        ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) * ((s : ℝ) : ℂ))) x.1 * (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) * τ *
      ((t : ℝ) : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
        ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) * ((t : ℝ) : ℂ))) x.2) =
      (∫ s : ℝ, (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
      (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
        ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) * ((s : ℝ) : ℂ))) s) * ∫ t : ℝ, (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) * τ *
      ((t : ℝ) : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
        ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) * ((t : ℝ) : ℂ))) t := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.integral_prod_mul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
        (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
          ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) * ((s : ℝ) : ℂ)))
      (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) * τ *
        ((t : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
          ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) * ((t : ℝ) : ℂ)))
  rw [h1, h2, h3, paper2_gaussian_1d hτ' (show (0 : ℝ) < 20 by norm_num),
    paper2_gaussian_1d hτ (show (0 : ℝ) < 4 by norm_num), Complex.real_smul]
  linear_combination (((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
      ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ) *
      Complex.exp (-((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
        ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
      Complex.exp (-((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
        ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) ^ 2) / τ)) * paper2_const_c2

/-- **The `c₁` Gaussian evaluation**, with the same `(√5)⁻¹` constant. -/
theorem paper2_gauss_eval_c1 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, ((Real.exp (-Real.pi * (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ *
        (((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
          ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
        (Complex.exp (-((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
            ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
            ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) ^ 2) / τ)) := by
  have hτ' : 0 < (-(starRingEnd ℂ) τ).im := by rw [paper2_neg_conj_im]; exact hτ
  have hcont : Continuous (fun a : ℝ × ℝ => ((Real.exp (-Real.pi * (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) :=
    (continuous_paper2ConeGauss 0 1 τ).mul (continuous_paper2PhaseExp τ α)
  have h1 : (∫ a : ℝ × ℝ, ((Real.exp (-Real.pi * (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      ∫ x : ℝ × ℝ, ((Real.exp (-Real.pi *
        (paper2B0 0 1 (0 * x.1 + 1 * x.2) (1 * x.1 + 0 * x.2) * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) *
        paper2PhaseExp τ α (0 * x.1 + 1 * x.2, 1 * x.1 + 0 * x.2) :=
    (paper2_integral_comp_c1 hcont).symm
  have h2 : (∫ x : ℝ × ℝ, ((Real.exp (-Real.pi *
        (paper2B0 0 1 (0 * x.1 + 1 * x.2) (1 * x.1 + 0 * x.2) * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) *
        paper2PhaseExp τ α (0 * x.1 + 1 * x.2, 1 * x.1 + 0 * x.2)) =
      ∫ x : ℝ × ℝ, (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
        (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
          ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) * ((s : ℝ) : ℂ))) x.1 * (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * τ *
        ((t : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
          ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) * ((t : ℝ) : ℂ))) x.2 :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => paper2_phase_split_c1 hτ α x.1 x.2)
  have h3 : (∫ x : ℝ × ℝ, (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
        (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
          ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) * ((s : ℝ) : ℂ))) x.1 * (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * τ *
        ((t : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
          ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) * ((t : ℝ) : ℂ))) x.2) =
      (∫ s : ℝ, (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
        (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
          ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) * ((s : ℝ) : ℂ))) s) * ∫ t : ℝ, (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * τ *
        ((t : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
          ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) * ((t : ℝ) : ℂ))) t := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.integral_prod_mul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (fun s : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
        (-(starRingEnd ℂ) τ) * ((s : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
          ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) * ((s : ℝ) : ℂ)))
      (fun t : ℝ => Complex.exp ((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * τ *
        ((t : ℝ) : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
          ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) * ((t : ℝ) : ℂ)))
  rw [h1, h2, h3, paper2_gaussian_1d hτ' (show (0 : ℝ) < 5 by norm_num),
    paper2_gaussian_1d hτ (show (0 : ℝ) < 1 by norm_num)]
  linear_combination (((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
      ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ) *
      Complex.exp (-((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
        ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
      Complex.exp (-((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
        ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) ^ 2) / τ)) * paper2_const_c1

/-! ## Block 2: integration by parts (Zwegers' step 3)

The `a_l`-derivative of the phase is moved onto `ρ` by
`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`.  Its `tsupport`
hypotheses are free — both factors are differentiable everywhere — and the
version used needs no limits at infinity, only three integrability facts, each
of which follows from the Gaussian majorants already proved. -/

/-- The `a₁`-partial of `ρ`, named.  Note `(Ac₁)₁ = 0`, so only the `c₂` term
survives. -/
noncomputable def paper2RhoDerivFst (a : ℝ × ℝ) (τ : ℂ) : ℝ :=
  2 * zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) * (0 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) - 2 * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * (-5 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))

/-- The `a₂`-partial of `ρ`, named. -/
noncomputable def paper2RhoDerivSnd (a : ℝ × ℝ) (τ : ℂ) : ℝ :=
  2 * zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) * (-5 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) - 2 * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * (-15 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))

theorem paper2_hasDerivAt_rho_fst' (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun x : ℝ => paper2Rho (x, a.2) τ) (paper2RhoDerivFst a τ) a.1 :=
  paper2_hasDerivAt_rho_fst τ a

theorem paper2_hasDerivAt_rho_snd' (τ : ℂ) (a : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => paper2Rho (a.1, y) τ) (paper2RhoDerivSnd a τ) a.2 :=
  paper2_hasDerivAt_rho_snd τ a

theorem paper2_norm_phaseExp (τ : ℂ) (α a : ℝ × ℝ) :
    ‖paper2PhaseExp τ α a‖ = Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 a.2 : ℝ) : ℂ) * τ +
      2 * (Real.pi : ℂ) * Complex.I * ((paper2B0 a.1 a.2 α.1 α.2 : ℝ) : ℂ)).re =
      -(2 * Real.pi * τ.im * paper2Q0 a.1 a.2) := by
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
    ring
  rw [paper2PhaseExp, Complex.norm_exp, hre]

theorem paper2_norm_rho_mul_phaseExp {τ : ℂ} (hτ : 0 < τ.im) (α a : ℝ × ℝ) :
    ‖((paper2Rho a τ : ℝ) : ℂ) * paper2PhaseExp τ α a‖ ≤
      10 * Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, paper2_norm_phaseExp]
  exact paper2_abs_rho_mul_exp_le hτ a

/-- The `c₂` Gaussian factor paired with the phase collapses to `e^{-2πy Q_{c₂}}`,
hence is bounded by the common Gaussian. -/
theorem paper2_gaussTwo_mul_phase_le {τ : ℂ} (hτ : 0 < τ.im) (_α a : ℝ × ℝ) :
    zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) ≤
      Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
  have hcollapse : zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) *
      Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) =
      Real.exp (-(2 * Real.pi * τ.im * paper2Qc2 a.1 a.2)) := by
    rw [zwegersGaussian, ← Real.exp_add]
    congr 1
    linarith [paper2_kernel_exponent_c2 hτ.le a.1 a.2]
  rw [hcollapse]
  refine paper2_exp_le_exp_of_le hτ.le ?_
  have hlow := paper2Qc2_lower a.1 a.2
  have hs1 := sq_nonneg a.1
  have hs2 := sq_nonneg a.2
  linarith

theorem paper2_gaussOne_mul_phase_le {τ : ℂ} (hτ : 0 < τ.im) (_α a : ℝ × ℝ) :
    zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) * Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) ≤
      Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
  have hcollapse : zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) *
      Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) =
      Real.exp (-(2 * Real.pi * τ.im * paper2Qc1 a.1 a.2)) := by
    rw [zwegersGaussian, ← Real.exp_add]
    congr 1
    linarith [paper2_kernel_exponent_c1 hτ.le a.1 a.2]
  rw [hcollapse]
  refine paper2_exp_le_exp_of_le hτ.le ?_
  have hlow := paper2Qc1_lower a.1 a.2
  have hs1 := sq_nonneg a.1
  have hs2 := sq_nonneg a.2
  linarith

theorem paper2_norm_rhoDerivFst_mul_phaseExp {τ : ℂ} (hτ : 0 < τ.im) (α a : ℝ × ℝ) :
    ‖((paper2RhoDerivFst a τ : ℝ) : ℂ) * paper2PhaseExp τ α a‖ ≤
      10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
  have hk : (0 : ℝ) ≤ (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by
    apply div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hval : paper2RhoDerivFst a τ = 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by
    rw [paper2RhoDerivFst]
    ring
  have hg := paper2_gaussTwo_mul_phase_le hτ α a
  have hgpos : 0 < zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := zwegersGaussian_pos _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, paper2_norm_phaseExp, hval,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))]
  nlinarith [Real.exp_pos (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2))]

theorem paper2_norm_rhoDerivSnd_mul_phaseExp {τ : ℂ} (hτ : 0 < τ.im) (α a : ℝ × ℝ) :
    ‖((paper2RhoDerivSnd a τ : ℝ) : ℂ) * paper2PhaseExp τ α a‖ ≤
      (10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) + 30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))) *
        Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) := by
  have hk1 : (0 : ℝ) ≤ (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hk2 : (0 : ℝ) ≤ (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hg1 := paper2_gaussOne_mul_phase_le hτ α a
  have hg2 := paper2_gaussTwo_mul_phase_le hτ α a
  have hp1 : 0 < zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) := zwegersGaussian_pos _
  have hp2 : 0 < zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := zwegersGaussian_pos _
  have hE : 0 < Real.exp (-(2 * Real.pi * τ.im * paper2Q0 a.1 a.2)) := Real.exp_pos _
  have habs : |paper2RhoDerivSnd a τ| ≤
      10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) * zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) + 30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by
    rw [paper2RhoDerivSnd, abs_le]
    constructor <;> nlinarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, paper2_norm_phaseExp]
  nlinarith [abs_nonneg (paper2RhoDerivSnd a τ)]

/-! ### One-dimensional slice integrability -/

theorem paper2_integrable_of_gaussian_bound {f : ℝ → ℂ} (hf : Continuous f) {C c : ℝ}
    (hc : 0 < c) (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) * Real.exp (-c * x ^ 2)) :
    MeasureTheory.Integrable f := by
  have h0 := integrable_exp_neg_mul_sq hc
  have h1 := paper2_integrable_abs_mul_gaussian hc
  have hmaj : MeasureTheory.Integrable
      (fun x : ℝ => C * (1 + |x|) * Real.exp (-c * x ^ 2)) := by
    refine ((h0.const_mul C).add (h1.const_mul C)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    show C * Real.exp (-c * x ^ 2) + C * (|x| * Real.exp (-c * x ^ 2)) =
      C * (1 + |x|) * Real.exp (-c * x ^ 2)
    ring
  exact hmaj.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem paper2_gaussian_slice_split {τ : ℂ} (a₂ t : ℝ) :
    Real.exp (-(2 * Real.pi * τ.im * ((t ^ 2 + a₂ ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im * (a₂ ^ 2 / 100))) *
        Real.exp (-(2 * Real.pi * τ.im / 100) * t ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem continuous_paper2Rho_slice_fst (τ : ℂ) (a₂ : ℝ) :
    Continuous (fun t : ℝ => ((paper2Rho (t, a₂) τ : ℝ) : ℂ)) := by
  refine Complex.continuous_ofReal.comp ((continuous_paper2Rho τ).comp ?_)
  fun_prop

theorem continuous_paper2PhaseExp_slice_fst (τ : ℂ) (α : ℝ × ℝ) (a₂ : ℝ) :
    Continuous (fun t : ℝ => paper2PhaseExp τ α (t, a₂)) := by
  refine (continuous_paper2PhaseExp τ α).comp ?_
  fun_prop

theorem continuous_paper2RhoDerivFst_slice (τ : ℂ) (a₂ : ℝ) :
    Continuous (fun t : ℝ => ((paper2RhoDerivFst (t, a₂) τ : ℝ) : ℂ)) := by
  refine Complex.continuous_ofReal.comp ?_
  unfold paper2RhoDerivFst zwegersGaussian paper2B0
  fun_prop

theorem paper2_integrable_slice_uv_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₂ : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => ((paper2Rho (t, a₂) τ : ℝ) : ℂ) * paper2PhaseExp τ α (t, a₂)) := by
  refine paper2_integrable_of_gaussian_bound
    ((continuous_paper2Rho_slice_fst τ a₂).mul (continuous_paper2PhaseExp_slice_fst τ α a₂))
    (C := 10 * Real.exp (-(2 * Real.pi * τ.im * (a₂ ^ 2 / 100))))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun t => ?_
  have h := paper2_norm_rho_mul_phaseExp hτ α (t, a₂)
  rw [paper2_gaussian_slice_split a₂ t] at h
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100) * t ^ 2) := Real.exp_pos _
  have hC : (0 : ℝ) ≤ 10 * Real.exp (-(2 * Real.pi * τ.im * (a₂ ^ 2 / 100))) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hC (abs_nonneg t)) hE.le]

theorem paper2_integrable_slice_uv'_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₂ : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => ((paper2Rho (t, a₂) τ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ * (t : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α (t, a₂))) := by
  refine paper2_integrable_of_gaussian_bound
    ((continuous_paper2Rho_slice_fst τ a₂).mul (by
      refine Continuous.mul ?_ (continuous_paper2PhaseExp_slice_fst τ α a₂)
      fun_prop))
    (C := 20 * Real.pi * (‖τ‖ + |α.1|) *
      Real.exp (-(2 * Real.pi * τ.im * (a₂ ^ 2 / 100))))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun t => ?_
  have h := paper2_norm_rho_mul_phaseExp hτ α (t, a₂)
  rw [paper2_gaussian_slice_split a₂ t] at h
  have hlin : ‖2 * (Real.pi : ℂ) * Complex.I * (τ * (t : ℂ) + (α.1 : ℂ))‖ ≤
      2 * Real.pi * ((‖τ‖ + |α.1|) * (1 + |t|)) := by
    rw [norm_mul, paper2_norm_two_pi_I]
    have h1 : ‖τ * (t : ℂ) + (α.1 : ℂ)‖ ≤ ‖τ‖ * |t| + |α.1| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖τ‖ * |t| + |α.1| ≤ (‖τ‖ + |α.1|) * (1 + |t|) := by
      nlinarith [norm_nonneg τ, abs_nonneg α.1, abs_nonneg t]
    nlinarith [Real.pi_pos, norm_nonneg (τ * (t : ℂ) + (α.1 : ℂ))]
  have hrw : ((paper2Rho (t, a₂) τ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ * (t : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α (t, a₂)) =
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (t : ℂ) + (α.1 : ℂ))) * (((paper2Rho (t, a₂) τ : ℝ) : ℂ) * paper2PhaseExp τ α (t, a₂)) := by ring
  rw [hrw, norm_mul]
  have hstep := mul_le_mul hlin h (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ((‖τ‖ + |α.1|) * (1 + |t|)))
  linarith [hstep]

theorem paper2_integrable_slice_u'v_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₂ : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => ((paper2RhoDerivFst (t, a₂) τ : ℝ) : ℂ) * paper2PhaseExp τ α (t, a₂)) := by
  refine paper2_integrable_of_gaussian_bound
    ((continuous_paper2RhoDerivFst_slice τ a₂).mul
      (continuous_paper2PhaseExp_slice_fst τ α a₂))
    (C := 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * Real.exp (-(2 * Real.pi * τ.im * (a₂ ^ 2 / 100))))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun t => ?_
  have h := paper2_norm_rhoDerivFst_mul_phaseExp hτ α (t, a₂)
  rw [paper2_gaussian_slice_split a₂ t] at h
  have hk : (0 : ℝ) ≤ (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100) * t ^ 2) := Real.exp_pos _
  have hC : (0 : ℝ) ≤ 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) *
      Real.exp (-(2 * Real.pi * τ.im * (a₂ ^ 2 / 100))) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hC (abs_nonneg t)) hE.le]

/-- **Integration by parts in the `a₁` direction.** -/
theorem paper2_ibp_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₂ : ℝ) :
    (∫ t : ℝ, ((paper2Rho (t, a₂) τ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ * (t : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α (t, a₂))) = -∫ t : ℝ, ((paper2RhoDerivFst (t, a₂) τ : ℝ) : ℂ) * paper2PhaseExp τ α (t, a₂) := by
  have hu : ∀ x ∈ tsupport (fun t : ℝ => paper2PhaseExp τ α (t, a₂)),
      HasDerivAt (fun t : ℝ => ((paper2Rho (t, a₂) τ : ℝ) : ℂ))
        (((paper2RhoDerivFst (x, a₂) τ : ℝ) : ℂ)) x :=
    fun x _ => (paper2_hasDerivAt_rho_fst' τ (x, a₂)).ofReal_comp
  have hv : ∀ x ∈ tsupport (fun t : ℝ => ((paper2Rho (t, a₂) τ : ℝ) : ℂ)),
      HasDerivAt (fun t : ℝ => paper2PhaseExp τ α (t, a₂))
        (2 * (Real.pi : ℂ) * Complex.I * (τ * (x : ℂ) + (α.1 : ℂ)) *
          paper2PhaseExp τ α (x, a₂)) x :=
    fun x _ => paper2_hasDerivAt_phaseExp_a_fst τ α (x, a₂)
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv
    (paper2_integrable_slice_uv'_fst hτ α a₂) (paper2_integrable_slice_u'v_fst hτ α a₂)
    (paper2_integrable_slice_uv_fst hτ α a₂)

/-! ### The `a₂` direction -/

theorem paper2_gaussian_slice_split' {τ : ℂ} (a₁ u : ℝ) :
    Real.exp (-(2 * Real.pi * τ.im * ((a₁ ^ 2 + u ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im * (a₁ ^ 2 / 100))) *
        Real.exp (-(2 * Real.pi * τ.im / 100) * u ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem continuous_paper2Rho_slice_snd (τ : ℂ) (a₁ : ℝ) :
    Continuous (fun u : ℝ => ((paper2Rho (a₁, u) τ : ℝ) : ℂ)) := by
  refine Complex.continuous_ofReal.comp ((continuous_paper2Rho τ).comp ?_)
  fun_prop

theorem continuous_paper2PhaseExp_slice_snd (τ : ℂ) (α : ℝ × ℝ) (a₁ : ℝ) :
    Continuous (fun u : ℝ => paper2PhaseExp τ α (a₁, u)) := by
  refine (continuous_paper2PhaseExp τ α).comp ?_
  fun_prop

theorem continuous_paper2RhoDerivSnd_slice (τ : ℂ) (a₁ : ℝ) :
    Continuous (fun u : ℝ => ((paper2RhoDerivSnd (a₁, u) τ : ℝ) : ℂ)) := by
  refine Complex.continuous_ofReal.comp ?_
  unfold paper2RhoDerivSnd zwegersGaussian paper2B0
  fun_prop

theorem paper2_integrable_slice_uv_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₁ : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ => ((paper2Rho (a₁, u) τ : ℝ) : ℂ) * paper2PhaseExp τ α (a₁, u)) := by
  refine paper2_integrable_of_gaussian_bound
    ((continuous_paper2Rho_slice_snd τ a₁).mul (continuous_paper2PhaseExp_slice_snd τ α a₁))
    (C := 10 * Real.exp (-(2 * Real.pi * τ.im * (a₁ ^ 2 / 100))))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun u => ?_
  have h := paper2_norm_rho_mul_phaseExp hτ α (a₁, u)
  rw [paper2_gaussian_slice_split' a₁ u] at h
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100) * u ^ 2) := Real.exp_pos _
  have hC : (0 : ℝ) ≤ 10 * Real.exp (-(2 * Real.pi * τ.im * (a₁ ^ 2 / 100))) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hC (abs_nonneg u)) hE.le]

theorem paper2_integrable_slice_uv'_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₁ : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ => ((paper2Rho (a₁, u) τ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (u : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α (a₁, u))) := by
  refine paper2_integrable_of_gaussian_bound
    ((continuous_paper2Rho_slice_snd τ a₁).mul (by
      refine Continuous.mul ?_ (continuous_paper2PhaseExp_slice_snd τ α a₁)
      fun_prop))
    (C := 100 * Real.pi * (‖τ‖ + |α.2|) *
      Real.exp (-(2 * Real.pi * τ.im * (a₁ ^ 2 / 100))))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun u => ?_
  have h := paper2_norm_rho_mul_phaseExp hτ α (a₁, u)
  rw [paper2_gaussian_slice_split' a₁ u] at h
  have hlin : ‖2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (u : ℂ)) + (-5 * (α.2 : ℂ)))‖ ≤
      10 * Real.pi * ((‖τ‖ + |α.2|) * (1 + |u|)) := by
    rw [norm_mul, paper2_norm_two_pi_I,
      show τ * (-5 * (u : ℂ)) + (-5 * (α.2 : ℂ)) = (-5 : ℂ) * (τ * (u : ℂ) + (α.2 : ℂ)) by ring,
      norm_mul]
    have h1 : ‖τ * (u : ℂ) + (α.2 : ℂ)‖ ≤ ‖τ‖ * |u| + |α.2| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖τ‖ * |u| + |α.2| ≤ (‖τ‖ + |α.2|) * (1 + |u|) := by
      nlinarith [norm_nonneg τ, abs_nonneg α.2, abs_nonneg u]
    have h5 : ‖(-5 : ℂ)‖ = 5 := by norm_num
    rw [h5]
    nlinarith [Real.pi_pos, norm_nonneg (τ * (u : ℂ) + (α.2 : ℂ))]
  have hrw : ((paper2Rho (a₁, u) τ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (u : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α (a₁, u)) =
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (u : ℂ)) + (-5 * (α.2 : ℂ)))) * (((paper2Rho (a₁, u) τ : ℝ) : ℂ) * paper2PhaseExp τ α (a₁, u)) := by
    ring
  rw [hrw, norm_mul]
  have hstep := mul_le_mul hlin h (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ 10 * Real.pi * ((‖τ‖ + |α.2|) * (1 + |u|)))
  linarith [hstep]

theorem paper2_integrable_slice_u'v_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₁ : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ => ((paper2RhoDerivSnd (a₁, u) τ : ℝ) : ℂ) * paper2PhaseExp τ α (a₁, u)) := by
  refine paper2_integrable_of_gaussian_bound
    ((continuous_paper2RhoDerivSnd_slice τ a₁).mul
      (continuous_paper2PhaseExp_slice_snd τ α a₁))
    (C := (10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) + 30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))) *
      Real.exp (-(2 * Real.pi * τ.im * (a₁ ^ 2 / 100))))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun u => ?_
  have h := paper2_norm_rhoDerivSnd_mul_phaseExp hτ α (a₁, u)
  rw [paper2_gaussian_slice_split' a₁ u] at h
  have hk1 : (0 : ℝ) ≤ (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hk2 : (0 : ℝ) ≤ (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100) * u ^ 2) := Real.exp_pos _
  have hC : (0 : ℝ) ≤ (10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) + 30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))) *
      Real.exp (-(2 * Real.pi * τ.im * (a₁ ^ 2 / 100))) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hC (abs_nonneg u)) hE.le]

/-- **Integration by parts in the `a₂` direction.** -/
theorem paper2_ibp_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) (a₁ : ℝ) :
    (∫ u : ℝ, ((paper2Rho (a₁, u) τ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (u : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α (a₁, u))) = -∫ u : ℝ, ((paper2RhoDerivSnd (a₁, u) τ : ℝ) : ℂ) * paper2PhaseExp τ α (a₁, u) := by
  have hu : ∀ x ∈ tsupport (fun u : ℝ => paper2PhaseExp τ α (a₁, u)),
      HasDerivAt (fun u : ℝ => ((paper2Rho (a₁, u) τ : ℝ) : ℂ))
        (((paper2RhoDerivSnd (a₁, x) τ : ℝ) : ℂ)) x :=
    fun x _ => (paper2_hasDerivAt_rho_snd' τ (a₁, x)).ofReal_comp
  have hv : ∀ x ∈ tsupport (fun u : ℝ => ((paper2Rho (a₁, u) τ : ℝ) : ℂ)),
      HasDerivAt (fun u : ℝ => paper2PhaseExp τ α (a₁, u))
        (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (x : ℂ)) + (-5 * (α.2 : ℂ))) *
          paper2PhaseExp τ α (a₁, x)) x :=
    fun x _ => paper2_hasDerivAt_phaseExp_a_snd τ α (a₁, x)
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable hu hv
    (paper2_integrable_slice_uv'_snd hτ α a₁) (paper2_integrable_slice_u'v_snd hτ α a₁)
    (paper2_integrable_slice_uv_snd hτ α a₁)

/-! ## Block 3: lifting the integration by parts to `ℝ²` (Fubini)

`MeasureTheory.integral_prod_symm` turns the `ℝ²` integral into an iterated one
with the differentiated coordinate innermost; Block 2 acts on the inner
integral; the same lemma turns it back. -/

theorem paper2_integrable2d_of_gaussian_bound {f : ℝ × ℝ → ℂ} (hf : Continuous f) {C c : ℝ}
    (hc : 0 < c) (hb : ∀ x : ℝ × ℝ, ‖f x‖ ≤ C * (1 + |x.1| + |x.2|) *
      Real.exp (-(c * (x.1 ^ 2 + x.2 ^ 2)))) : MeasureTheory.Integrable f := by
  have h0 := integrable_exp_neg_mul_sq hc
  have h1 := paper2_integrable_abs_mul_gaussian hc
  have hmaj : MeasureTheory.Integrable (fun x : ℝ × ℝ => C * (1 + |x.1| + |x.2|) *
      Real.exp (-(c * (x.1 ^ 2 + x.2 ^ 2)))) := by
    have hA := (h0.mul_prod h0).const_mul C
    have hB := (h1.mul_prod h0).const_mul C
    have hC := (h0.mul_prod h1).const_mul C
    refine ((hA.add hB).add hC).congr (Filter.Eventually.of_forall fun x => ?_)
    show C * (Real.exp (-c * x.1 ^ 2) * Real.exp (-c * x.2 ^ 2)) +
        C * (|x.1| * Real.exp (-c * x.1 ^ 2) * Real.exp (-c * x.2 ^ 2)) +
        C * (Real.exp (-c * x.1 ^ 2) * (|x.2| * Real.exp (-c * x.2 ^ 2))) =
      C * (1 + |x.1| + |x.2|) * Real.exp (-(c * (x.1 ^ 2 + x.2 ^ 2)))
    rw [show -(c * (x.1 ^ 2 + x.2 ^ 2)) = -c * x.1 ^ 2 + -c * x.2 ^ 2 by ring, Real.exp_add]
    ring
  exact hmaj.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem paper2_integrable2d_uv'_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ => ((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a)) := by
  refine paper2_integrable2d_of_gaussian_bound (by
      refine Continuous.mul ?_ (Continuous.mul ?_ (continuous_paper2PhaseExp τ α))
      · exact Complex.continuous_ofReal.comp (continuous_paper2Rho τ)
      · fun_prop)
    (C := 20 * Real.pi * (‖τ‖ + |α.1|)) (c := 2 * Real.pi * τ.im / 100)
    (by positivity) fun a => ?_
  have h := paper2_norm_rho_mul_phaseExp hτ α a
  have hexp : Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) := by
    congr 1
    ring
  rw [hexp] at h
  have hlin : ‖2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ))‖ ≤
      2 * Real.pi * ((‖τ‖ + |α.1|) * (1 + |a.1| + |a.2|)) := by
    rw [norm_mul, paper2_norm_two_pi_I]
    have h1 : ‖τ * (a.1 : ℂ) + (α.1 : ℂ)‖ ≤ ‖τ‖ * |a.1| + |α.1| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖τ‖ * |a.1| + |α.1| ≤ (‖τ‖ + |α.1|) * (1 + |a.1| + |a.2|) := by
      nlinarith [norm_nonneg τ, abs_nonneg α.1, abs_nonneg a.1, abs_nonneg a.2]
    nlinarith [Real.pi_pos, norm_nonneg (τ * (a.1 : ℂ) + (α.1 : ℂ))]
  have hrw : ((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a) =
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ))) *
        (((paper2Rho a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) := by ring
  rw [hrw, norm_mul]
  have hstep := mul_le_mul hlin h (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ((‖τ‖ + |α.1|) * (1 + |a.1| + |a.2|)))
  linarith [hstep]

theorem paper2_integrable2d_u'v_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ =>
      ((paper2RhoDerivFst a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) := by
  refine paper2_integrable2d_of_gaussian_bound (by
      refine Continuous.mul (Complex.continuous_ofReal.comp ?_) (continuous_paper2PhaseExp τ α)
      unfold paper2RhoDerivFst zwegersGaussian paper2B0
      fun_prop)
    (C := 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun a => ?_
  have h := paper2_norm_rhoDerivFst_mul_phaseExp hτ α a
  have hexp : Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) := by
    congr 1
    ring
  rw [hexp] at h
  have hk : (0 : ℝ) ≤ 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by positivity
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) :=
    Real.exp_pos _
  nlinarith [mul_nonneg (mul_nonneg hk (abs_nonneg a.1)) hE.le,
    mul_nonneg (mul_nonneg hk (abs_nonneg a.2)) hE.le]

/-- **Integration by parts on `ℝ²`, `a₁` direction.** -/
theorem paper2_ibp2d_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, ((paper2Rho a τ : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a))
      = -∫ a : ℝ × ℝ, ((paper2RhoDerivFst a τ : ℝ) : ℂ) * paper2PhaseExp τ α a := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.integral_prod_symm _ (by
        rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact paper2_integrable2d_uv'_fst hτ α),
    MeasureTheory.integral_prod_symm _ (by
        rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact paper2_integrable2d_u'v_fst hτ α)]
  rw [← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a₂ => ?_)
  exact paper2_ibp_fst hτ α a₂

theorem paper2_integrable2d_uv'_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ => ((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α a)) := by
  refine paper2_integrable2d_of_gaussian_bound (by
      refine Continuous.mul ?_ (Continuous.mul ?_ (continuous_paper2PhaseExp τ α))
      · exact Complex.continuous_ofReal.comp (continuous_paper2Rho τ)
      · fun_prop)
    (C := 100 * Real.pi * (‖τ‖ + |α.2|)) (c := 2 * Real.pi * τ.im / 100)
    (by positivity) fun a => ?_
  have h := paper2_norm_rho_mul_phaseExp hτ α a
  have hexp : Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) := by
    congr 1
    ring
  rw [hexp] at h
  have hlin : ‖2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ)))‖ ≤
      10 * Real.pi * ((‖τ‖ + |α.2|) * (1 + |a.1| + |a.2|)) := by
    rw [norm_mul, paper2_norm_two_pi_I,
      show τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ)) = (-5 : ℂ) * (τ * (a.2 : ℂ) + (α.2 : ℂ)) by
        ring,
      norm_mul, show ‖(-5 : ℂ)‖ = 5 by norm_num]
    have h1 : ‖τ * (a.2 : ℂ) + (α.2 : ℂ)‖ ≤ ‖τ‖ * |a.2| + |α.2| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖τ‖ * |a.2| + |α.2| ≤ (‖τ‖ + |α.2|) * (1 + |a.1| + |a.2|) := by
      nlinarith [norm_nonneg τ, abs_nonneg α.2, abs_nonneg a.1, abs_nonneg a.2]
    nlinarith [Real.pi_pos, norm_nonneg (τ * (a.2 : ℂ) + (α.2 : ℂ))]
  have hrw : ((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α a) =
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ)))) *
        (((paper2Rho a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) := by ring
  rw [hrw, norm_mul]
  have hstep := mul_le_mul hlin h (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ 10 * Real.pi * ((‖τ‖ + |α.2|) * (1 + |a.1| + |a.2|)))
  linarith [hstep]

theorem paper2_integrable2d_u'v_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ =>
      ((paper2RhoDerivSnd a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) := by
  refine paper2_integrable2d_of_gaussian_bound (by
      refine Continuous.mul (Complex.continuous_ofReal.comp ?_) (continuous_paper2PhaseExp τ α)
      unfold paper2RhoDerivSnd zwegersGaussian paper2B0
      fun_prop)
    (C := 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) + 30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)))
    (c := 2 * Real.pi * τ.im / 100) (by positivity) fun a => ?_
  have h := paper2_norm_rhoDerivSnd_mul_phaseExp hτ α a
  have hexp : Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) := by
    congr 1
    ring
  rw [hexp] at h
  have hk : (0 : ℝ) ≤ 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) + 30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by positivity
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) :=
    Real.exp_pos _
  nlinarith [mul_nonneg (mul_nonneg hk (abs_nonneg a.1)) hE.le,
    mul_nonneg (mul_nonneg hk (abs_nonneg a.2)) hE.le]

/-- **Integration by parts on `ℝ²`, `a₂` direction.** -/
theorem paper2_ibp2d_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, ((paper2Rho a τ : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
          paper2PhaseExp τ α a))
      = -∫ a : ℝ × ℝ, ((paper2RhoDerivSnd a τ : ℝ) : ℂ) * paper2PhaseExp τ α a := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.integral_prod _ (by
        rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact paper2_integrable2d_uv'_snd hτ α),
    MeasureTheory.integral_prod _ (by
        rw [← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact paper2_integrable2d_u'v_snd hτ α)]
  rw [← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a₁ => ?_)
  exact paper2_ibp_snd hτ α a₁

/-! ## Block 4 (partial): the Fréchet derivative of `ρ`, and the two
differentiated integrals in closed form

`ρ(·;τ)` is `E` composed with a *linear* functional of `α`, so its Fréchet
derivative comes straight from the chain rule — no assembly of partial
derivatives is needed, which is what point 17 of the previous report was
about. -/

noncomputable def paper2RhoFderiv (τ : ℂ) (α : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (2 * zwegersGaussian (paper2B0 0 1 α.1 α.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) *
      (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) • paper2BCLM ((0 : ℝ), (1 : ℝ)) -
    (2 * zwegersGaussian (paper2B0 (-5) 3 α.1 α.2 * Real.sqrt τ.im /
          Real.sqrt (-paper2Q0 (-5) 3)) *
        (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))) • paper2BCLM ((-5 : ℝ), (3 : ℝ))

theorem paper2_hasFDerivAt_rho (τ : ℂ) (α : ℝ × ℝ) :
    HasFDerivAt (fun β : ℝ × ℝ => paper2Rho β τ) (paper2RhoFderiv τ α) α := by
  have h1 : HasFDerivAt (fun β : ℝ × ℝ =>
      paper2B0 0 1 β.1 β.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))
      ((Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) • paper2BCLM ((0 : ℝ), (1 : ℝ))) α := by
    have hfun : (fun β : ℝ × ℝ =>
        paper2B0 0 1 β.1 β.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) =
        ⇑((Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) • paper2BCLM ((0 : ℝ), (1 : ℝ))) := by
      funext β
      simp only [ContinuousLinearMap.smul_apply, paper2BCLM_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact ((Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) •
      paper2BCLM ((0 : ℝ), (1 : ℝ))).hasFDerivAt
  have h2 : HasFDerivAt (fun β : ℝ × ℝ =>
      paper2B0 (-5) 3 β.1 β.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))
      ((Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) •
        paper2BCLM ((-5 : ℝ), (3 : ℝ))) α := by
    have hfun : (fun β : ℝ × ℝ =>
        paper2B0 (-5) 3 β.1 β.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) =
        ⇑((Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) •
          paper2BCLM ((-5 : ℝ), (3 : ℝ))) := by
      funext β
      simp only [ContinuousLinearMap.smul_apply, paper2BCLM_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact ((Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) •
      paper2BCLM ((-5 : ℝ), (3 : ℝ))).hasFDerivAt
  have hE1 := (hasDerivAt_zwegersErrorKernel _).comp_hasFDerivAt α h1
  have hE2 := (hasDerivAt_zwegersErrorKernel _).comp_hasFDerivAt α h2
  refine (hE1.sub hE2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [paper2RhoFderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem paper2RhoFderiv_fst (τ : ℂ) (α : ℝ × ℝ) :
    paper2RhoFderiv τ α (1, 0) = paper2RhoDerivFst α τ := by
  simp only [paper2RhoFderiv, paper2RhoDerivFst, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, paper2BCLM_apply, paper2B0, smul_eq_mul]
  ring

theorem paper2RhoFderiv_snd (τ : ℂ) (α : ℝ × ℝ) :
    paper2RhoFderiv τ α (0, 1) = paper2RhoDerivSnd α τ := by
  simp only [paper2RhoFderiv, paper2RhoDerivSnd, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, paper2BCLM_apply, paper2B0, smul_eq_mul]
  ring

/-! ### The two differentiated integrals, evaluated -/

theorem paper2RhoDerivFst_eq (τ : ℂ) (a : ℝ × ℝ) :
    paper2RhoDerivFst a τ = 10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by
  rw [paper2RhoDerivFst]
  ring

theorem paper2RhoDerivSnd_eq (τ : ℂ) (a : ℝ × ℝ) :
    paper2RhoDerivSnd a τ =
      -(10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) * zwegersGaussian (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) + 30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) * zwegersGaussian (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) := by
  rw [paper2RhoDerivSnd]
  ring

/-- The `a₁`-differentiated integral, in closed form: only the `c₂` cone
survives, since `(Ac₁)₁ = 0`. -/
theorem paper2_integral_rhoDerivFst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, ((paper2RhoDerivFst a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      ((10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) : ℝ) : ℂ) *
        (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ *
          (((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
            ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
          (Complex.exp (-((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
              ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
            Complex.exp (-((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
              ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) ^ 2) / τ))) := by
  rw [← paper2_gauss_eval_c2 hτ α, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  show ((paper2RhoDerivFst a τ : ℝ) : ℂ) * paper2PhaseExp τ α a =
    ((10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) : ℝ) : ℂ) *
      (((Real.exp (-Real.pi * (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a)
  rw [paper2RhoDerivFst_eq, zwegersGaussian]
  push_cast
  ring

theorem paper2_integrable2d_coneGaussOne {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ => ((Real.exp (-Real.pi * (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) := by
  refine paper2_integrable2d_of_gaussian_bound
    ((continuous_paper2ConeGauss 0 1 τ).mul (continuous_paper2PhaseExp τ α))
    (C := 1) (c := 2 * Real.pi * τ.im / 100) (by positivity) fun a => ?_
  have h := paper2_gaussOne_mul_phase_le hτ α a
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, paper2_norm_phaseExp,
    abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) := by
    congr 1
    ring
  rw [hexp] at h
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) :=
    Real.exp_pos _
  rw [zwegersGaussian] at h
  nlinarith [abs_nonneg a.1, abs_nonneg a.2]

theorem paper2_integrable2d_coneGaussTwo {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    MeasureTheory.Integrable (fun a : ℝ × ℝ => ((Real.exp (-Real.pi * (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) := by
  refine paper2_integrable2d_of_gaussian_bound
    ((continuous_paper2ConeGauss (-5) 3 τ).mul (continuous_paper2PhaseExp τ α))
    (C := 1) (c := 2 * Real.pi * τ.im / 100) (by positivity) fun a => ?_
  have h := paper2_gaussTwo_mul_phase_le hτ α a
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, paper2_norm_phaseExp,
    abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-(2 * Real.pi * τ.im * ((a.1 ^ 2 + a.2 ^ 2) / 100))) =
      Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) := by
    congr 1
    ring
  rw [hexp] at h
  have hE : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im / 100 * (a.1 ^ 2 + a.2 ^ 2))) :=
    Real.exp_pos _
  rw [zwegersGaussian] at h
  nlinarith [abs_nonneg a.1, abs_nonneg a.2]

/-- The `a₂`-differentiated integral, in closed form: both cones contribute. -/
theorem paper2_integral_rhoDerivSnd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, ((paper2RhoDerivSnd a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      ((-(10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) : ℝ) : ℂ) * (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ *
        (((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
          ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
        (Complex.exp (-((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
            ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
            ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) ^ 2) / τ))) + ((30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) : ℝ) : ℂ) * (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ *
        (((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
          ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ)) *
        (Complex.exp (-((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
            ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
            ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) ^ 2) / τ))) := by
  have hsplit : (∫ a : ℝ × ℝ, ((paper2RhoDerivSnd a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      ∫ a : ℝ × ℝ, (((-(10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) : ℝ) : ℂ) * (((Real.exp (-Real.pi * (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) +
        ((30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) : ℝ) : ℂ) * (((Real.exp (-Real.pi * (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show ((paper2RhoDerivSnd a τ : ℝ) : ℂ) * paper2PhaseExp τ α a =
      ((-(10 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1))) : ℝ) : ℂ) * (((Real.exp (-Real.pi * (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 0 1)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a) +
        ((30 * (Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3)) : ℝ) : ℂ) * (((Real.exp (-Real.pi * (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im /
        Real.sqrt (-paper2Q0 (-5) 3)) ^ 2) : ℝ) : ℂ) * paper2PhaseExp τ α a)
    rw [paper2RhoDerivSnd_eq, zwegersGaussian, zwegersGaussian]
    push_cast
    ring
  rw [hsplit, MeasureTheory.integral_add
      ((paper2_integrable2d_coneGaussOne hτ α).const_mul _)
      ((paper2_integrable2d_coneGaussTwo hτ α).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    paper2_gauss_eval_c1 hτ α, paper2_gauss_eval_c2 hτ α]

/-! ### Oddness of the Lemma 2.8 integral

`Q` is even and `B` is bilinear, so the reflection `a ↦ -a` — which is
`paper2_integral_comp_splitMap` at `(-1,0,0,-1)`, determinant `1` — turns
`α ↦ -α` into `ρ(-a) = -ρ(a)`.  No `IsNegInvariant` or `measurePreserving_neg`
is needed. -/

theorem paper2_fourierIntegral_neg {τ : ℂ} (α : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, paper2FourierIntegrand τ (-α) a) =
      -∫ a : ℝ × ℝ, paper2FourierIntegrand τ α a := by
  have hrefl := paper2_integral_comp_splitMap (a := -1) (b := 0) (c := 0) (d := -1)
    (by norm_num) (continuous_paper2FourierIntegrand τ (-α))
  simp only [paper2SplitMap_apply] at hrefl
  rw [show |(-1 : ℝ) * -1 - 0 * 0|⁻¹ = 1 by norm_num, one_smul] at hrefl
  rw [← hrefl, ← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show paper2FourierIntegrand τ (-α) (-1 * x.1 + 0 * x.2, 0 * x.1 + -1 * x.2) =
    -paper2FourierIntegrand τ α x
  rw [paper2FourierIntegrand, paper2FourierIntegrand]
  have hQ : paper2Q0 (-1 * x.1 + 0 * x.2) (0 * x.1 + -1 * x.2) = paper2Q0 x.1 x.2 := by
    rw [paper2Q0, paper2Q0]
    ring
  have hB : paper2B0 (-1 * x.1 + 0 * x.2) (0 * x.1 + -1 * x.2) (-α).1 (-α).2 =
      paper2B0 x.1 x.2 α.1 α.2 := by
    simp only [Prod.fst_neg, Prod.snd_neg, paper2B0]
    ring
  have hR : paper2Rho (-1 * x.1 + 0 * x.2, 0 * x.1 + -1 * x.2) τ = -paper2Rho x τ := by
    rw [← paper2Rho_neg]
    congr 1
    refine Prod.ext ?_ ?_
    · show -1 * x.1 + 0 * x.2 = -x.1
      ring
    · show 0 * x.1 + -1 * x.2 = -x.2
      ring
  rw [hQ, hB, hR]
  push_cast
  ring

/-! ## The two remaining identities of Lemma 2.8

The Gaussian evaluations of Block 1 produce the constant
`(√5)⁻¹ · A₁ · A₂` with `A₁ = ((iτ̄)⁻¹)^{1/2}` and `A₂ = ((-iτ)⁻¹)^{1/2}`.
Since `iτ̄ = conj(-iτ)` and `Re(-iτ) = Im τ > 0`, the principal branch commutes
with conjugation there, so `A₁ = conj A₂` and the product is the positive real
`1/|τ|`.  The second identity says the two Gaussian exponentials, multiplied by
`e^{2πiQ(α)/τ}`, collapse to the single real Gaussian of `ρ` at `-1/τ`. -/

theorem paper2_conj_cpow_half {z : ℂ} (hz : 0 < z.re) :
    ((starRingEnd ℂ) z) ^ (1 / 2 : ℂ) = (starRingEnd ℂ) (z ^ (1 / 2 : ℂ)) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hcz0 : (starRingEnd ℂ) z ≠ 0 := by
    simpa using hz0
  have harg : z.arg ≠ Real.pi := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith [h.1]
  rw [Complex.cpow_def_of_ne_zero hcz0, Complex.log_conj z harg,
    Complex.cpow_def_of_ne_zero hz0, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_div₀, map_one, map_ofNat]

theorem paper2_neg_I_mul_ne_zero' {τ : ℂ} (hτ : 0 < τ.im) : -Complex.I * τ ≠ 0 :=
  paper2_neg_I_mul_ne_zero hτ

/-- **`A₁·A₂ = 1/|τ|`.** -/
theorem paper2_A1_mul_A2 {τ : ℂ} (hτ : 0 < τ.im) :
    ((-Complex.I * (-(starRingEnd ℂ) τ))⁻¹) ^ (1 / 2 : ℂ) *
        ((-Complex.I * τ)⁻¹) ^ (1 / 2 : ℂ) = ((‖τ‖⁻¹ : ℝ) : ℂ) := by
  have hw : (0 : ℝ) < (-Complex.I * τ).re := by
    rw [paper2_neg_I_mul_re]
    exact hτ
  have hw0 : -Complex.I * τ ≠ 0 := paper2_neg_I_mul_ne_zero hτ
  have hwinv0 : (-Complex.I * τ)⁻¹ ≠ 0 := inv_ne_zero hw0
  have hwinvre : (0 : ℝ) < ((-Complex.I * τ)⁻¹).re := by
    rw [Complex.inv_re]
    have hns : 0 < Complex.normSq (-Complex.I * τ) := Complex.normSq_pos.2 hw0
    positivity
  have hcw : -Complex.I * (-(starRingEnd ℂ) τ) = (starRingEnd ℂ) (-Complex.I * τ) := by
    simp [map_mul]
  rw [hcw, ← map_inv₀, paper2_conj_cpow_half hwinvre, ← Complex.normSq_eq_conj_mul_self]
  congr 1
  rw [← Complex.norm_mul_self_eq_normSq, ← norm_mul, paper2_cpow_half_mul_self hwinv0,
    norm_inv, norm_mul, norm_neg, Complex.norm_I, one_mul]

/-! ### The `-1/τ` collapse -/

theorem paper2_neg_inv_im (τ : ℂ) : (-1 / τ).im = τ.im / Complex.normSq τ := by
  rw [neg_div, one_div, Complex.neg_im, Complex.inv_im]
  ring

theorem paper2Q0_in_c1_coords (α : ℝ × ℝ) :
    paper2Q0 α.1 α.2 =
      -(paper2B0 0 1 α.1 α.2) ^ 2 / 10 + (paper2B0 1 0 α.1 α.2) ^ 2 / 2 := by
  rw [paper2Q0, paper2B0, paper2B0]
  ring

theorem paper2Q0_in_c2_coords (α : ℝ × ℝ) :
    paper2Q0 α.1 α.2 =
      -(paper2B0 (-5) 3 α.1 α.2) ^ 2 / 40 + (paper2B0 3 (-1) α.1 α.2) ^ 2 / 8 := by
  rw [paper2Q0, paper2B0, paper2B0]
  ring

theorem paper2_im_eq (τ : ℂ) :
    ((τ.im : ℝ) : ℂ) = -(τ - (starRingEnd ℂ) τ) * Complex.I / 2 := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- **The `c₂` collapse.**  The two Gaussian exponentials from the split, times
`e^{2πiQ(α)/τ}`, equal the single real Gaussian of `ρ^{c₂}` at `-1/τ`.  The
`B(e₂,α)` terms cancel identically; what is left is
`(πiP²/20)(1/τ̄ - 1/τ) = -πP²·Im τ/(10|τ|²)`. -/
theorem paper2_match_c2 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ) *
        (Complex.exp (-((Real.pi : ℂ) * Complex.I * ((20 : ℝ) : ℂ) *
            ((paper2B0 (-5) 3 α.1 α.2 / 20 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * ((4 : ℝ) : ℂ) *
            ((paper2B0 3 (-1) α.1 α.2 / 4 : ℝ) : ℂ) ^ 2) / τ)) =
      ((zwegersGaussian (paper2B0 (-5) 3 α.1 α.2 * Real.sqrt ((-1 / τ).im) /
        Real.sqrt (-paper2Q0 (-5) 3)) : ℝ) : ℂ) := by
  have hτ0 : τ ≠ 0 := fun h => absurd (by rw [h]; simp : τ.im = 0) hτ.ne'
  have hcτ0 : (starRingEnd ℂ) τ ≠ 0 := by simpa using hτ0
  have hns : (0 : ℝ) < Complex.normSq τ := Complex.normSq_pos.2 hτ0
  have hsq : Real.sqrt ((-1 / τ).im) ^ 2 = τ.im / Complex.normSq τ := by
    rw [paper2_neg_inv_im]
    exact Real.sq_sqrt (by positivity)
  have hrhs : -Real.pi * (paper2B0 (-5) 3 α.1 α.2 * Real.sqrt ((-1 / τ).im) /
      Real.sqrt (-paper2Q0 (-5) 3)) ^ 2 =
      -Real.pi * (paper2B0 (-5) 3 α.1 α.2) ^ 2 * (τ.im / Complex.normSq τ) / 10 := by
    rw [div_pow, mul_pow, hsq, paper2_sqrt_neg_Q0_c2_sq]
    ring
  rw [zwegersGaussian, hrhs, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [paper2Q0_in_c2_coords]
  push_cast
  rw [paper2_im_eq τ, ← Complex.mul_conj τ]
  field_simp
  ring_nf

/-- **The `c₁` collapse.** -/
theorem paper2_match_c1 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ) *
        (Complex.exp (-((Real.pi : ℂ) * Complex.I * ((5 : ℝ) : ℂ) *
            ((paper2B0 0 1 α.1 α.2 / 5 : ℝ) : ℂ) ^ 2) / (-(starRingEnd ℂ) τ)) *
          Complex.exp (-((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ) *
            ((paper2B0 1 0 α.1 α.2 / 1 : ℝ) : ℂ) ^ 2) / τ)) =
      ((zwegersGaussian (paper2B0 0 1 α.1 α.2 * Real.sqrt ((-1 / τ).im) /
        Real.sqrt (-paper2Q0 0 1)) : ℝ) : ℂ) := by
  have hτ0 : τ ≠ 0 := fun h => absurd (by rw [h]; simp : τ.im = 0) hτ.ne'
  have hcτ0 : (starRingEnd ℂ) τ ≠ 0 := by simpa using hτ0
  have hns : (0 : ℝ) < Complex.normSq τ := Complex.normSq_pos.2 hτ0
  have hsq : Real.sqrt ((-1 / τ).im) ^ 2 = τ.im / Complex.normSq τ := by
    rw [paper2_neg_inv_im]
    exact Real.sq_sqrt (by positivity)
  have hrhs : -Real.pi * (paper2B0 0 1 α.1 α.2 * Real.sqrt ((-1 / τ).im) /
      Real.sqrt (-paper2Q0 0 1)) ^ 2 =
      -Real.pi * (paper2B0 0 1 α.1 α.2) ^ 2 * (τ.im / Complex.normSq τ) * 2 / 5 := by
    rw [div_pow, mul_pow, hsq, paper2_sqrt_neg_Q0_c1_sq]
    ring
  rw [zwegersGaussian, hrhs, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [paper2Q0_in_c1_coords]
  push_cast
  rw [paper2_im_eq τ, ← Complex.mul_conj τ]
  field_simp
  ring_nf

/-! ## The assembly

`G(α) = e^{2πiQ(α)/τ}·H(α) − (1/√5)(i/(−iτ))·ρ(α;−1/τ)` has vanishing Fréchet
derivative and is odd, hence identically zero. -/

theorem paper2_hasFDerivAt_Q0 (α : ℝ × ℝ) :
    HasFDerivAt (fun β : ℝ × ℝ => paper2Q0 β.1 β.2) (paper2BCLM α) α := by
  have hfun : (fun β : ℝ × ℝ => paper2Q0 β.1 β.2) =
      fun β : ℝ × ℝ => (1 / 2 : ℝ) * β.1 ^ 2 - (5 / 2 : ℝ) * β.2 ^ 2 := by
    funext β
    rw [paper2Q0]
    ring
  rw [hfun]
  have h1 : HasFDerivAt (fun β : ℝ × ℝ => β.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) α :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun β : ℝ × ℝ => β.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) α :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have h := ((h1.pow 2).const_mul (1 / 2 : ℝ)).sub ((h2.pow 2).const_mul (5 / 2 : ℝ))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [paper2BCLM_apply, paper2B0, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  push_cast
  ring

theorem paper2_hasFDerivAt_Q0c (α : ℝ × ℝ) :
    HasFDerivAt (fun β : ℝ × ℝ => ((paper2Q0 β.1 β.2 : ℝ) : ℂ)) (paper2BCLMc α) α := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp α (paper2_hasFDerivAt_Q0 α)
  exact h

theorem paper2_hasFDerivAt_expQ (τ : ℂ) (α : ℝ × ℝ) :
    HasFDerivAt (fun β : ℝ × ℝ =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 β.1 β.2 : ℝ) : ℂ) / τ))
      ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ) *
        (2 * (Real.pi : ℂ) * Complex.I / τ)) • paper2BCLMc α) α := by
  have hinner : HasFDerivAt (fun β : ℝ × ℝ =>
      2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 β.1 β.2 : ℝ) : ℂ) / τ)
      ((2 * (Real.pi : ℂ) * Complex.I / τ) • paper2BCLMc α) α := by
    have h := (paper2_hasFDerivAt_Q0c α).const_mul (2 * (Real.pi : ℂ) * Complex.I / τ)
    have hfun : (fun β : ℝ × ℝ =>
        2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 β.1 β.2 : ℝ) : ℂ) / τ) =
        fun β : ℝ × ℝ => 2 * (Real.pi : ℂ) * Complex.I / τ * ((paper2Q0 β.1 β.2 : ℝ) : ℂ) := by
      funext β
      ring
    rw [hfun]
    exact h
  have h := hinner.cexp
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem paper2_hasFDerivAt_rhoNegInv {τ : ℂ} (α : ℝ × ℝ) :
    HasFDerivAt (fun β : ℝ × ℝ => ((paper2Rho β (-1 / τ) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (paper2RhoFderiv (-1 / τ) α)) α :=
  Complex.ofRealCLM.hasFDerivAt.comp α (paper2_hasFDerivAt_rho (-1 / τ) α)

/-- The constant of Lemma 2.8, `(1/√5)·i/(-iτ)`. -/
noncomputable def paper2LemmaConst (τ : ℂ) : ℂ :=
  ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (Complex.I / (-Complex.I * τ))

theorem paper2LemmaConst_eq {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LemmaConst τ = ((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (-1 / τ) := by
  have hτ0 : τ ≠ 0 := fun h => absurd (by rw [h]; simp : τ.im = 0) hτ.ne'
  rw [paper2LemmaConst]
  congr 1
  field_simp

theorem paper2_norm_pos {τ : ℂ} (hτ : 0 < τ.im) : (0 : ℝ) < ‖τ‖ := by
  refine norm_pos_iff.2 (fun h => ?_)
  rw [h] at hτ
  simp at hτ

theorem paper2_sqrt_neg_inv_im {τ : ℂ} (hτ : 0 < τ.im) :
    Real.sqrt ((-1 / τ).im) = Real.sqrt τ.im / ‖τ‖ := by
  have hτ0 : τ ≠ 0 := fun h => absurd (by rw [h]; simp : τ.im = 0) hτ.ne'
  rw [paper2_neg_inv_im, Real.sqrt_div hτ.le, Complex.norm_def]

/-- The `c₂` cone match: this is the `v = (1,0)` component of the final
identity, in exactly the form the assembly consumes. -/
theorem paper2_cone_match_fst {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    -(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ) * (1 / τ)) *
        (∫ a : ℝ × ℝ, ((paper2RhoDerivFst a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      paper2LemmaConst τ * ((paper2RhoDerivFst α (-1 / τ) : ℝ) : ℂ) := by
  have hnorm := paper2_norm_pos hτ
  have hk : (Real.sqrt ((-1 / τ).im) / Real.sqrt (-paper2Q0 (-5) 3) : ℝ) =
      Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3) * ‖τ‖⁻¹ := by
    rw [paper2_sqrt_neg_inv_im hτ]
    field_simp
  have hM := paper2_match_c2 hτ α
  rw [paper2_integral_rhoDerivFst hτ α, paper2RhoDerivFst_eq, paper2LemmaConst_eq hτ,
    paper2_A1_mul_A2 hτ, hk]
  push_cast
  push_cast at hM
  linear_combination (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (-1 / τ) *
      (10 * (((Real.sqrt τ.im : ℝ) : ℂ) / ((Real.sqrt (-paper2Q0 (-5) 3) : ℝ) : ℂ)) *
        ((‖τ‖ : ℝ) : ℂ)⁻¹)) * hM

/-- The `a₂` cone match: the `v = (0,1)` component. -/
theorem paper2_cone_match_snd {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    -(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ) * (1 / τ)) *
        (∫ a : ℝ × ℝ, ((paper2RhoDerivSnd a τ : ℝ) : ℂ) * paper2PhaseExp τ α a) =
      paper2LemmaConst τ * ((paper2RhoDerivSnd α (-1 / τ) : ℝ) : ℂ) := by
  have hnorm := paper2_norm_pos hτ
  have hk1 : (Real.sqrt ((-1 / τ).im) / Real.sqrt (-paper2Q0 0 1) : ℝ) =
      Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1) * ‖τ‖⁻¹ := by
    rw [paper2_sqrt_neg_inv_im hτ]
    field_simp
  have hk2 : (Real.sqrt ((-1 / τ).im) / Real.sqrt (-paper2Q0 (-5) 3) : ℝ) =
      Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3) * ‖τ‖⁻¹ := by
    rw [paper2_sqrt_neg_inv_im hτ]
    field_simp
  have hM1 := paper2_match_c1 hτ α
  have hM2 := paper2_match_c2 hτ α
  rw [paper2_integral_rhoDerivSnd hτ α, paper2RhoDerivSnd_eq, paper2LemmaConst_eq hτ,
    paper2_A1_mul_A2 hτ, hk1, hk2]
  push_cast
  push_cast at hM1 hM2
  linear_combination (-(((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (-1 / τ) *
      (10 * (((Real.sqrt τ.im : ℝ) : ℂ) / ((Real.sqrt (-paper2Q0 0 1) : ℝ) : ℂ)) *
        ((‖τ‖ : ℝ) : ℂ)⁻¹))) * hM1 +
    (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (-1 / τ) *
      (30 * (((Real.sqrt τ.im : ℝ) : ℂ) / ((Real.sqrt (-paper2Q0 (-5) 3) : ℝ) : ℂ)) *
        ((‖τ‖ : ℝ) : ℂ)⁻¹)) * hM2

noncomputable def paper2H (τ : ℂ) (α : ℝ × ℝ) : ℂ := ∫ a : ℝ × ℝ, paper2FourierIntegrand τ α a

noncomputable def paper2G (τ : ℂ) (α : ℝ × ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ) * paper2H τ α -
    paper2LemmaConst τ * ((paper2Rho α (-1 / τ) : ℝ) : ℂ)

/-- The directional split: `τB(a,v) + B(α,v) = v₁(τa₁+α₁) + v₂(τ(-5a₂)+(-5α₂))`,
turned into an identity between integrals. -/
theorem paper2_dir_split {τ : ℂ} (hτ : 0 < τ.im) (α v : ℝ × ℝ) :
    (∫ a : ℝ × ℝ, ((paper2B0 a.1 a.2 v.1 v.2 : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * paper2FourierIntegrand τ α a)) =
      1 / τ * (((v.1 : ℝ) : ℂ) * (∫ a : ℝ × ℝ, ((paper2Rho a τ : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a)) +
          ((v.2 : ℝ) : ℂ) * (∫ a : ℝ × ℝ, ((paper2Rho a τ : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
          paper2PhaseExp τ α a)) -
          ((paper2B0 α.1 α.2 v.1 v.2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
            paper2H τ α) := by
  have hτ0 : τ ≠ 0 := fun h => absurd (by rw [h]; simp : τ.im = 0) hτ.ne'
  have i1 : MeasureTheory.Integrable (fun a : ℝ × ℝ => ((v.1 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a))) :=
    (paper2_integrable2d_uv'_fst hτ α).const_mul _
  have i2 : MeasureTheory.Integrable (fun a : ℝ × ℝ => ((v.2 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α a))) :=
    (paper2_integrable2d_uv'_snd hτ α).const_mul _
  have i0 : MeasureTheory.Integrable (fun a : ℝ × ℝ => ((paper2B0 α.1 α.2 v.1 v.2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
      paper2FourierIntegrand τ α a) :=
    (paper2_integrable_fourierIntegrand hτ α).const_mul _
  have isum : MeasureTheory.Integrable (fun a : ℝ × ℝ => ((v.1 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a)) + ((v.2 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α a))) := i1.add i2
  have key : (∫ a : ℝ × ℝ, ((paper2B0 a.1 a.2 v.1 v.2 : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * paper2FourierIntegrand τ α a)) =
      ∫ a : ℝ × ℝ, 1 / τ * (((v.1 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a)) + ((v.2 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α a)) - (((paper2B0 α.1 α.2 v.1 v.2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
      paper2FourierIntegrand τ α a)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show ((paper2B0 a.1 a.2 v.1 v.2 : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * paper2FourierIntegrand τ α a) =
      1 / τ * (((v.1 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (a.1 : ℂ) + (α.1 : ℂ)) * paper2PhaseExp τ α a)) + ((v.2 : ℝ) : ℂ) * (((paper2Rho a τ : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (τ * (-5 * (a.2 : ℂ)) + (-5 * (α.2 : ℂ))) *
        paper2PhaseExp τ α a)) - (((paper2B0 α.1 α.2 v.1 v.2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) *
      paper2FourierIntegrand τ α a))
    rw [paper2FourierIntegrand_eq, paper2B0, paper2B0]
    push_cast
    field_simp
    ring
  rw [key, MeasureTheory.integral_const_mul, MeasureTheory.integral_sub isum i0,
    MeasureTheory.integral_add i1 i2]
  simp only [MeasureTheory.integral_const_mul]
  rw [← paper2H]

/-! ### Constancy, oddness, and Lemma 2.8 -/

theorem paper2_integral_fourierFderiv_apply
    {τ : ℂ} (hτ : 0 < τ.im) (α v : ℝ × ℝ) :
    (∫ a, paper2FourierFderiv τ α a) v =
      ∫ a, ((paper2B0 a.1 a.2 v.1 v.2 : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I * paper2FourierIntegrand τ α a) := by
  rw [ContinuousLinearMap.integral_apply
    (paper2_integrable_fourierFderiv hτ α) v]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun a => ?_)
  simp only [paper2FourierFderiv, ContinuousLinearMap.smulRight_apply,
    paper2BCLM_apply, Complex.real_smul]

theorem paper2RhoFderiv_apply (τ : ℂ) (α v : ℝ × ℝ) :
    (Complex.ofRealCLM.comp (paper2RhoFderiv τ α)) v =
      ((v.1 : ℝ) : ℂ) * ((paper2RhoDerivFst α τ : ℝ) : ℂ) +
      ((v.2 : ℝ) : ℂ) * ((paper2RhoDerivSnd α τ : ℝ) : ℂ) := by
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    paper2RhoFderiv, paper2RhoDerivFst, paper2RhoDerivSnd,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    paper2BCLM_apply, paper2B0, smul_eq_mul]
  push_cast
  ring

theorem paper2_hasFDerivAt_H {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    HasFDerivAt (paper2H τ) (∫ a, paper2FourierFderiv τ α a) α := by
  simpa only [paper2H] using paper2_hasFDerivAt_integral hτ α

/-- The difference between the two sides of Lemma 2.8 has zero Fréchet
derivative everywhere.  Keeping the `HasFDerivAt` witness is essential:
Mathlib's totalized `fderiv` is also zero at nondifferentiable points. -/
theorem paper2_hasFDerivAt_G {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    HasFDerivAt (paper2G τ) (0 : (ℝ × ℝ) →L[ℝ] ℂ) α := by
  have hraw :=
    ((paper2_hasFDerivAt_expQ τ α).mul (paper2_hasFDerivAt_H hτ α)).sub
      ((paper2_hasFDerivAt_rhoNegInv (τ := τ) α).const_mul (paper2LemmaConst τ))
  unfold paper2G
  refine hraw.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
    paper2BCLMc_apply, smul_eq_mul]
  rw [paper2_integral_fourierFderiv_apply hτ α v,
    paper2RhoFderiv_apply (-1 / τ) α v]
  have hd := paper2_dir_split hτ α v
  have hi₁ := paper2_ibp2d_fst hτ α
  have hi₂ := paper2_ibp2d_snd hτ α
  rw [hd, hi₁, hi₂]
  have hc₁ := paper2_cone_match_fst hτ α
  have hc₂ := paper2_cone_match_snd hτ α
  linear_combination (((v.1 : ℝ) : ℂ)) * hc₁ + (((v.2 : ℝ) : ℂ)) * hc₂

theorem paper2G_differentiable {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℝ (paper2G τ) :=
  fun α => (paper2_hasFDerivAt_G hτ α).differentiableAt

theorem paper2G_fderiv_eq_zero {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ α, fderiv ℝ (paper2G τ) α = 0 :=
  fun α => (paper2_hasFDerivAt_G hτ α).fderiv

theorem paper2G_const {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ × ℝ) :
    paper2G τ α = paper2G τ β :=
  is_const_of_fderiv_eq_zero (𝕜 := ℝ)
    (paper2G_differentiable hτ) (paper2G_fderiv_eq_zero hτ) α β

theorem paper2H_neg (τ : ℂ) (α : ℝ × ℝ) :
    paper2H τ (-α) = -paper2H τ α := by
  simpa only [paper2H] using paper2_fourierIntegral_neg (τ := τ) α

theorem paper2G_neg (τ : ℂ) (α : ℝ × ℝ) :
    paper2G τ (-α) = -paper2G τ α := by
  have hQ : paper2Q0 (-α).1 (-α).2 = paper2Q0 α.1 α.2 := by
    simp only [Prod.fst_neg, Prod.snd_neg, paper2Q0]
    ring
  unfold paper2G
  rw [hQ, paper2H_neg, paper2Rho_neg]
  push_cast
  ring

theorem paper2G_eq_zero {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    paper2G τ α = 0 := by
  have h0 : paper2G τ (0 : ℝ × ℝ) = 0 := by
    rw [← CharZero.eq_neg_self_iff]
    simpa only [neg_zero] using paper2G_neg τ (0 : ℝ × ℝ)
  exact (paper2G_const hτ α 0).trans h0

/-- **Zwegers' Lemma 2.8 at the quadratic datum of Paper 2**, in a form that
keeps the nonzero exponential on the left. -/
theorem paper2_zwegers_lemma28_cleared {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ) * paper2H τ α =
      paper2LemmaConst τ * ((paper2Rho α (-1 / τ) : ℝ) : ℂ) :=
  sub_eq_zero.mp (by simpa only [paper2G] using paper2G_eq_zero hτ α)

/-- **Zwegers' Lemma 2.8 at the quadratic datum of Paper 2**, with the source's
constant `(1/√5)·i/(-iτ)` and the inverse exponential displayed explicitly. -/
theorem paper2_zwegers_lemma28 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    paper2H τ α =
      (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (Complex.I / (-Complex.I * τ))) *
        ((paper2Rho α (-1 / τ) : ℝ) : ℂ) *
        Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I *
            ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ)) := by
  let z : ℂ :=
    2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ
  have hc : Complex.exp z * paper2H τ α =
      paper2LemmaConst τ * ((paper2Rho α (-1 / τ) : ℝ) : ℂ) := by
    simpa only [z] using paper2_zwegers_lemma28_cleared hτ α
  have he : Complex.exp (-z) * Complex.exp z = 1 := by
    rw [← Complex.exp_add]
    simp
  change paper2H τ α =
    paper2LemmaConst τ * ((paper2Rho α (-1 / τ) : ℝ) : ℂ) * Complex.exp (-z)
  calc
    paper2H τ α = 1 * paper2H τ α := by simp
    _ = (Complex.exp (-z) * Complex.exp z) * paper2H τ α := by rw [he]
    _ = Complex.exp (-z) * (Complex.exp z * paper2H τ α) := by ring
    _ = Complex.exp (-z) *
        (paper2LemmaConst τ * ((paper2Rho α (-1 / τ) : ℝ) : ℂ)) := by rw [hc]
    _ = paper2LemmaConst τ * ((paper2Rho α (-1 / τ) : ℝ) : ℂ) *
        Complex.exp (-z) := by ring

end Ch10
end QseriesFormalization
