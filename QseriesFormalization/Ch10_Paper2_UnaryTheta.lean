import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Paper 2: unary theta components

The mixed boundary derivative in Paper 2 is expressed through four residue
components of weights `1/2` and `3/2`.  This file defines those components as
absolutely convergent series on the upper half-plane.  Their summability is
reduced to Mathlib's two-variable Jacobi theta series and its first
`z`-derivative; the residue conditions only delete terms.
-/

namespace QseriesFormalization
namespace Ch10

open Complex Filter

noncomputable section

/-! ## Residue-filtered summands -/

/-- The transverse residue class `T ≡ 3j+2 (mod 4)` from the index-four
orthogonal decomposition at the boundary vector `c₂`. -/
def paper2ThetaResidue (j T : ℤ) : Prop :=
  T % 4 = (3 * j + 2) % 4

/-- The longitudinal residue class `n ≡ 5j+4 (mod 20)` from the same
decomposition. -/
def paper2GResidue (j n : ℤ) : Prop :=
  n % 20 = (5 * j + 4) % 20

instance (j T : ℤ) : Decidable (paper2ThetaResidue j T) := by
  unfold paper2ThetaResidue
  infer_instance

instance (j n : ℤ) : Decidable (paper2GResidue j n) := by
  unfold paper2GResidue
  infer_instance

/-- Summand of the transverse component
`theta_j(τ) = Σ_{T≡3j+2 (4)} exp(2πiτ T²/8)`.  It is written as a Jacobi
theta term at modulus `τ/4`. -/
def paper2ThetaTerm (j T : ℤ) (τ : ℂ) : ℂ :=
  if paper2ThetaResidue j T then jacobiTheta₂_term T 0 (τ / 4) else 0

/-- Summand of the longitudinal component
`g_j(τ) = Σ_{n≡5j+4 (20)} n exp(2πiτ n²/40)`.  The extra factor `n` is the
weight-`3/2` derivative factor. -/
def paper2GTerm (j n : ℤ) (τ : ℂ) : ℂ :=
  if paper2GResidue j n then (n : ℂ) * jacobiTheta₂_term n 0 (τ / 20) else 0

/-! ## Absolute convergence on the upper half-plane -/

/-- The transverse residue component is absolutely summable whenever
`Im τ > 0`. -/
theorem summable_paper2ThetaTerm (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun T : ℤ => paper2ThetaTerm j T τ) := by
  have hquarter : 0 < (τ / 4).im := by
    simp only [div_im]
    norm_num
    positivity
  have hbase : Summable (fun T : ℤ => jacobiTheta₂_term T 0 (τ / 4)) :=
    (summable_jacobiTheta₂_term_iff 0 (τ / 4)).2 hquarter
  refine hbase.norm.of_norm_bounded ?_
  intro T
  by_cases hres : paper2ThetaResidue j T
  · simp [paper2ThetaTerm, hres]
  · simp [paper2ThetaTerm, hres]

/-- The longitudinal residue component is absolutely summable whenever
`Im τ > 0`; the linear factor is absorbed by the standard polynomial-Gaussian
majorant for the Jacobi theta derivative. -/
theorem summable_paper2GTerm (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => paper2GTerm j n τ) := by
  let T0 : ℝ := τ.im / 20
  have hT0 : 0 < T0 := by
    dsimp [T0]
    positivity
  have hmajor : Summable (fun n : ℤ =>
      (|n| ^ (1 : ℕ) : ℝ) * Real.exp (-Real.pi * (T0 * n ^ 2 - 2 * 0 * |n|))) :=
    summable_pow_mul_jacobiTheta₂_term_bound 0 hT0 1
  refine hmajor.of_norm_bounded ?_
  intro n
  by_cases hres : paper2GResidue j n
  · rw [paper2GTerm, if_pos hres, norm_mul]
    have htheta :
        ‖jacobiTheta₂_term n 0 (τ / 20)‖ ≤
          Real.exp (-Real.pi * (T0 * n ^ 2 - 2 * 0 * |n|)) := by
      apply norm_jacobiTheta₂_term_le hT0
      · simp
      · dsimp [T0]
        simp only [div_im]
        norm_num
        ring_nf
        exact le_rfl
    calc
      ‖(n : ℂ)‖ * ‖jacobiTheta₂_term n 0 (τ / 20)‖ ≤
          (|n| : ℝ) * Real.exp (-Real.pi * (T0 * n ^ 2 - 2 * 0 * |n|)) := by
            have hmul := mul_le_mul_of_nonneg_left htheta (norm_nonneg (n : ℂ))
            simpa using hmul
      _ = (|n| ^ (1 : ℕ) : ℝ) *
          Real.exp (-Real.pi * (T0 * n ^ 2 - 2 * 0 * |n|)) := by simp
  · rw [paper2GTerm, if_neg hres, norm_zero]
    positivity

/-! ## The four analytic components -/

/-- The transverse weight-`1/2` component in residue class `j`. -/
def paper2ThetaComponent (j : ℤ) (τ : ℂ) : ℂ :=
  ∑' T : ℤ, paper2ThetaTerm j T τ

/-- The longitudinal weight-`3/2` component in residue class `j`. -/
def paper2GComponent (j : ℤ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, paper2GTerm j n τ

/-- The components depend only on `j mod 4`, as required by the four-coset
decomposition. -/
theorem paper2ThetaComponent_add_four (j : ℤ) (τ : ℂ) :
    paper2ThetaComponent (j + 4) τ = paper2ThetaComponent j τ := by
  apply tsum_congr
  intro T
  have hmod : (3 * (j + 4) + 2) % 4 = (3 * j + 2) % 4 := by omega
  simp [paper2ThetaTerm, paper2ThetaResidue, hmod]

/-- The longitudinal components likewise depend only on `j mod 4`. -/
theorem paper2GComponent_add_four (j : ℤ) (τ : ℂ) :
    paper2GComponent (j + 4) τ = paper2GComponent j τ := by
  apply tsum_congr
  intro n
  have hmod : (5 * (j + 4) + 4) % 20 = (5 * j + 4) % 20 := by omega
  simp [paper2GTerm, paper2GResidue, hmod]

/-! ## The odd transverse theta at the `c₁` boundary -/

/-- The sign `(-1)^n` written as a complex exponential. -/
theorem neg_one_zpow_eq_exp_pi_I (n : ℤ) :
    ((-1 : ℂ) ^ n) = Complex.exp ((n : ℂ) * (Real.pi * Complex.I)) := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]

/-- The direct summand in the odd-theta cancellation used at the `c₁`
boundary. -/
def paper2OddThetaTerm (a : ℝ) (τ : ℂ) (n : ℤ) : ℂ :=
  ((-1 : ℂ) ^ n) *
    Complex.exp (2 * Real.pi * Complex.I * τ * (a : ℂ) *
      ((n : ℂ) + 1 / 2) ^ 2)

/-- After completing the square, the odd-theta summand is a constant multiple
of a standard Jacobi theta summand at the half-period. -/
theorem paper2OddThetaTerm_eq_jacobi (a : ℝ) (τ : ℂ) (n : ℤ) :
    paper2OddThetaTerm a τ n =
      Complex.exp (Real.pi * Complex.I * (a : ℂ) * τ / 2) *
        jacobiTheta₂_term n ((a : ℂ) * τ + 1 / 2) (2 * (a : ℂ) * τ) := by
  rw [paper2OddThetaTerm, neg_one_zpow_eq_exp_pi_I, jacobiTheta₂_term]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- Absolute convergence of the odd transverse series for `a>0` and
`Im τ>0`, inherited from the ordinary Jacobi theta series. -/
theorem summable_paper2OddThetaTerm {a : ℝ} (ha : 0 < a) {τ : ℂ}
    (hτ : 0 < τ.im) :
    Summable (paper2OddThetaTerm a τ) := by
  have hmod : 0 < (2 * (a : ℂ) * τ).im := by
    simpa [Complex.mul_im, Complex.mul_re] using
      mul_pos (mul_pos two_pos ha) hτ
  have hbase : Summable (fun n : ℤ =>
      jacobiTheta₂_term n ((a : ℂ) * τ + 1 / 2) (2 * (a : ℂ) * τ)) :=
    (summable_jacobiTheta₂_term_iff ((a : ℂ) * τ + 1 / 2)
      (2 * (a : ℂ) * τ)).2 hmod
  have hscaled := hbase.mul_left
    (Complex.exp (Real.pi * Complex.I * (a : ℂ) * τ / 2))
  exact hscaled.congr (fun n => (paper2OddThetaTerm_eq_jacobi a τ n).symm)

/-- Jacobi's theta series vanishes at the odd half-period
`z=(τ+1)/2`.  This is the analytic form of the fixed-point-free pairing
`n ↦ -1-n`. -/
theorem jacobiTheta₂_half_period_zero (τ : ℂ) :
    jacobiTheta₂ ((τ + 1) / 2) τ = 0 := by
  let w : ℂ := (τ + 1) / 2
  have hself : jacobiTheta₂ w τ = -jacobiTheta₂ w τ := by
    calc
      jacobiTheta₂ w τ = jacobiTheta₂ ((-w + τ) + 1) τ := by
        congr 2
        dsimp [w]
        ring
      _ = jacobiTheta₂ (-w + τ) τ := jacobiTheta₂_add_left (-w + τ) τ
      _ = Complex.exp (-Real.pi * Complex.I * (τ + 2 * (-w))) *
          jacobiTheta₂ (-w) τ := jacobiTheta₂_add_left' (-w) τ
      _ = -jacobiTheta₂ w τ := by
        rw [jacobiTheta₂_neg_left]
        have hphase : -Real.pi * Complex.I * (τ + 2 * (-w)) =
            Real.pi * Complex.I := by
          dsimp [w]
          ring
        rw [hphase, Complex.exp_pi_mul_I]
        ring
  change jacobiTheta₂ w τ = 0
  have htwo : (2 : ℂ) * jacobiTheta₂ w τ = 0 := by
    linear_combination hself
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Analytic odd-theta cancellation from Paper 2, Lemma `Odd-theta
cancellation`. -/
theorem paper2OddTheta_tsum_eq_zero {a : ℝ} (ha : 0 < a) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ∑' n : ℤ, paper2OddThetaTerm a τ n = 0 := by
  have hmod : 0 < (2 * (a : ℂ) * τ).im := by
    simpa [Complex.mul_im, Complex.mul_re] using
      mul_pos (mul_pos two_pos ha) hτ
  have hbase : Summable (fun n : ℤ =>
      jacobiTheta₂_term n ((a : ℂ) * τ + 1 / 2) (2 * (a : ℂ) * τ)) :=
    (summable_jacobiTheta₂_term_iff ((a : ℂ) * τ + 1 / 2)
      (2 * (a : ℂ) * τ)).2 hmod
  calc
    (∑' n : ℤ, paper2OddThetaTerm a τ n) =
        Complex.exp (Real.pi * Complex.I * (a : ℂ) * τ / 2) *
          jacobiTheta₂ ((2 * (a : ℂ) * τ + 1) / 2) (2 * (a : ℂ) * τ) := by
            rw [show ((2 * (a : ℂ) * τ + 1) / 2) =
              (a : ℂ) * τ + 1 / 2 by ring]
            rw [jacobiTheta₂, ← hbase.tsum_mul_left]
            apply tsum_congr
            intro n
            rw [paper2OddThetaTerm_eq_jacobi]
    _ = 0 := by
      rw [jacobiTheta₂_half_period_zero, mul_zero]

end

end Ch10
end QseriesFormalization
