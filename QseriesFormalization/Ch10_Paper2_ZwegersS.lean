import QseriesFormalization.Ch10_Paper2_EllipticLaws
import QseriesFormalization.Ch10_Paper2_PoissonLattice
import QseriesFormalization.Ch10_Paper2_ZwegersFourier

/-!
# Ch10 / Paper 2: Zwegers' inversion law and the manuscript's `S`-law

This file specializes the kernel-checked Lemma 2.8 and genuine square-lattice
Poisson summation to prove Zwegers' Corollary 2.9(5) for
`A = diag(1,-5)`, then carries it through the already-proved bridge to the
manuscript's completed theta.

The theorem is a transformation law for the explicit convergent lattice sum.
It does not assert that this sum is the canonical completion of its holomorphic
part.
-/

namespace QseriesFormalization
namespace Ch10

open MeasureTheory
open scoped Real

noncomputable section

/-- Convert a two-coordinate vector into the pair convention used by the
quadratic form. -/
def paper2FinTwoPair : C(Fin 2 → ℝ, ℝ × ℝ) where
  toFun x := (x 0, x 1)
  continuous_toFun := (continuous_apply 0).prodMk (continuous_apply 1)

@[simp]
theorem paper2FinTwoPair_apply (x : Fin 2 → ℝ) :
    paper2FinTwoPair x = (x 0, x 1) := rfl

/-- The continuous function whose lattice periodization is
`θ_{a,b}(-1/τ)`. -/
def paper2SFunction (a b : ℝ × ℝ) (τ : ℂ) : C(Fin 2 → ℝ, ℂ) where
  toFun x := paper2FourierIntegrand (-1 / τ) b
    (a.1 + x 0, a.2 + x 1)
  continuous_toFun :=
    (continuous_paper2FourierIntegrand (-1 / τ) b).comp
      ((continuous_const.add (continuous_apply 0)).prodMk
        (continuous_const.add (continuous_apply 1)))

@[simp]
theorem paper2SFunction_apply (a b : ℝ × ℝ) (τ : ℂ) (x : Fin 2 → ℝ) :
    paper2SFunction a b τ x = paper2FourierIntegrand (-1 / τ) b
      (a.1 + x 0, a.2 + x 1) := rfl

theorem paper2_neg_inv_im_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  rw [paper2_neg_inv_im]
  have hτ0 : τ ≠ 0 := fun h => by simpa [h] using hτ.ne'
  exact div_pos hτ (Complex.normSq_pos.mpr hτ0)

theorem paper2_shifted_sq_lower {u v D : ℝ} (hu : u ^ 2 ≤ D ^ 2) :
    v ^ 2 / 2 - D ^ 2 ≤ (u + v) ^ 2 := by
  nlinarith only [sq_nonneg (v + 2 * u), hu]

theorem paper2_exp_two_shift_bound {u0 u1 v0 v1 D0 D1 c : ℝ} (hc : 0 < c)
    (h0 : v0 ^ 2 / 2 - D0 ^ 2 ≤ (u0 + v0) ^ 2)
    (h1 : v1 ^ 2 / 2 - D1 ^ 2 ≤ (u1 + v1) ^ 2) :
    Real.exp (-c * ((u0 + v0) ^ 2 + (u1 + v1) ^ 2)) ≤
      Real.exp (c * (D0 ^ 2 + D1 ^ 2)) *
        (Real.exp (-(c / 2) * v0 ^ 2) * Real.exp (-(c / 2) * v1 ^ 2)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [h0, h1, hc]

/-- A shifted isotropic Gaussian bound implies local normal summability of all
integer translates on `ℝ²`. -/
theorem paper2LocallySummable2_of_shifted_gaussian
    (f : C(Fin 2 → ℝ, ℂ)) (s : Fin 2 → ℝ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hf : ∀ x, ‖f x‖ ≤ C * Real.exp
      (-c * ((s 0 + x 0) ^ 2 + (s 1 + x 1) ^ 2))) :
    Paper2LocallySummable2 f := by
  intro K
  let p0 : C(Fin 2 → ℝ, ℝ) := ⟨fun x => x 0, continuous_apply 0⟩
  let p1 : C(Fin 2 → ℝ, ℝ) := ⟨fun x => x 1, continuous_apply 1⟩
  let R0 : ℝ := ‖p0.restrict K‖
  let R1 : ℝ := ‖p1.restrict K‖
  let D0 : ℝ := |s 0| + R0
  let D1 : ℝ := |s 1| + R1
  have hR0 : 0 ≤ R0 := norm_nonneg _
  have hR1 : 0 ≤ R1 := norm_nonneg _
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD1 : 0 ≤ D1 := by dsimp only [D1]; positivity
  have hg : Summable fun z : ℤ => Real.exp (-(c / 2) * ((z : ℝ) ^ 2)) := by
    have hcp : 0 < c / (2 * Real.pi) := by positivity
    refine (summable_exp_neg_pi_mul_sq hcp).congr fun z => ?_
    congr 1
    field_simp [Real.pi_ne_zero]
  have hprod : Summable fun z : ℤ × ℤ =>
      Real.exp (-(c / 2) * ((z.1 : ℝ) ^ 2)) *
        Real.exp (-(c / 2) * ((z.2 : ℝ) ^ 2)) :=
    Summable.mul_of_nonneg hg hg (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  have hvec : Summable fun n : Fin 2 → ℤ =>
      Real.exp (-(c / 2) * ((n 0 : ℝ) ^ 2)) *
        Real.exp (-(c / 2) * ((n 1 : ℝ) ^ 2)) := by
    exact (finTwoArrowEquiv ℤ).summable_iff.mpr hprod
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((hvec.mul_left (C * Real.exp (c * (D0 ^ 2 + D1 ^ 2)))))
  rw [ContinuousMap.norm_le _ (by positivity)]
  rintro ⟨x, hx⟩
  have hx0 : |x 0| ≤ R0 := by
    have h := ContinuousMap.norm_coe_le_norm
      (p0.restrict (K : Set (Fin 2 → ℝ))) ⟨x, hx⟩
    simpa only [p0, R0, ContinuousMap.restrict_apply, Real.norm_eq_abs] using h
  have hx1 : |x 1| ≤ R1 := by
    have h := ContinuousMap.norm_coe_le_norm
      (p1.restrict (K : Set (Fin 2 → ℝ))) ⟨x, hx⟩
    simpa only [p1, R1, ContinuousMap.restrict_apply, Real.norm_eq_abs] using h
  have ht0 : |s 0 + x 0| ≤ D0 := by
    dsimp only [D0]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) hx0)
  have ht1 : |s 1 + x 1| ≤ D1 := by
    dsimp only [D1]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) hx1)
  have ht0sq : (s 0 + x 0) ^ 2 ≤ D0 ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hD0]
    exact ht0
  have ht1sq : (s 1 + x 1) ^ 2 ≤ D1 ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hD1]
    exact ht1
  have hlower0 : ((n 0 : ℝ) + (s 0 + x 0)) ^ 2 ≥
      ((n 0 : ℝ) ^ 2) / 2 - D0 ^ 2 := by
    simpa only [add_comm] using
      (paper2_shifted_sq_lower (u := s 0 + x 0) (v := (n 0 : ℝ)) ht0sq)
  have hlower1 : ((n 1 : ℝ) + (s 1 + x 1)) ^ 2 ≥
      ((n 1 : ℝ) ^ 2) / 2 - D1 ^ 2 := by
    simpa only [add_comm] using
      (paper2_shifted_sq_lower (u := s 1 + x 1) (v := (n 1 : ℝ)) ht1sq)
  have hexp' : Real.exp (-c *
      (((s 0 + x 0) + (n 0 : ℝ)) ^ 2 +
        ((s 1 + x 1) + (n 1 : ℝ)) ^ 2)) ≤
      Real.exp (c * (D0 ^ 2 + D1 ^ 2)) *
        (Real.exp (-(c / 2) * ((n 0 : ℝ) ^ 2)) *
          Real.exp (-(c / 2) * ((n 1 : ℝ) ^ 2))) := by
    exact paper2_exp_two_shift_bound hc
      (by simpa only [add_comm] using hlower0)
      (by simpa only [add_comm] using hlower1)
  have hexp : Real.exp (-c *
      ((s 0 + (x + paper2LatticeVec n) 0) ^ 2 +
        (s 1 + (x + paper2LatticeVec n) 1) ^ 2)) ≤
      Real.exp (c * (D0 ^ 2 + D1 ^ 2)) *
        (Real.exp (-(c / 2) * ((n 0 : ℝ) ^ 2)) *
          Real.exp (-(c / 2) * ((n 1 : ℝ) ^ 2))) := by
    simpa only [Pi.add_apply, paper2LatticeVec_apply, add_assoc] using hexp'
  calc
    ‖(f.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict
        (K : Set (Fin 2 → ℝ)) ⟨x, hx⟩‖
        = ‖f (x + paper2LatticeVec n)‖ := rfl
    _ ≤ C * Real.exp (-c *
        ((s 0 + (x + paper2LatticeVec n) 0) ^ 2 +
          (s 1 + (x + paper2LatticeVec n) 1) ^ 2)) := hf _
    _ ≤ C * (Real.exp (c * (D0 ^ 2 + D1 ^ 2)) *
        (Real.exp (-(c / 2) * ((n 0 : ℝ) ^ 2)) *
          Real.exp (-(c / 2) * ((n 1 : ℝ) ^ 2)))) :=
      mul_le_mul_of_nonneg_left hexp hC
    _ = C * Real.exp (c * (D0 ^ 2 + D1 ^ 2)) *
        (Real.exp (-(c / 2) * ((n 0 : ℝ) ^ 2)) *
          Real.exp (-(c / 2) * ((n 1 : ℝ) ^ 2))) := by ring

theorem paper2SFunction_locallySummable (a b : ℝ × ℝ) {τ : ℂ}
    (hτ : 0 < τ.im) : Paper2LocallySummable2 (paper2SFunction a b τ) := by
  have hS := paper2_neg_inv_im_pos hτ
  refine paper2LocallySummable2_of_shifted_gaussian
    (paper2SFunction a b τ) ![a.1, a.2] (C := 10)
    (c := 2 * Real.pi * (-1 / τ).im / 100) (by norm_num) (by positivity) ?_
  intro x
  rw [paper2SFunction_apply, paper2_norm_fourierIntegrand]
  convert paper2_abs_rho_mul_exp_le hS (a.1 + x 0, a.2 + x 1) using 1
  all_goals
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring_nf

theorem paper2_tsum_SFunction_eq_theta (a b : ℝ × ℝ) (τ : ℂ) :
    (∑' n : Fin 2 → ℤ, paper2SFunction a b τ (paper2LatticeVec n)) =
      paper2ThetaAB a b (-1 / τ) := by
  rw [paper2ThetaAB, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [paper2SFunction_apply, paper2ThetaABTerm, paper2FourierIntegrand,
    paper2Shift]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, paper2LatticeVec_apply]
  ring_nf

/-- The dual-lattice characteristic selected by the standard Fourier index
`m`: `B(u, paper2SAlpha b m) = B(u,b) - m·u`. -/
def paper2SAlpha (b : ℝ × ℝ) (m : Fin 2 → ℤ) : ℝ × ℝ :=
  (b.1 - (m 0 : ℝ), b.2 + (m 1 : ℝ) / 5)

/-- The phase introduced when the Fourier integral is shifted by the first
characteristic `a`. -/
def paper2SPhase (a : ℝ × ℝ) (m : Fin 2 → ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    (((m 0 : ℝ) : ℂ) * (a.1 : ℂ) + ((m 1 : ℝ) : ℂ) * (a.2 : ℂ)))

theorem paper2Char_mul_phaseExp (a b u : ℝ × ℝ) (τ : ℂ)
    (m : Fin 2 → ℤ) (x : Fin 2 → ℝ)
    (hu0 : u.1 = a.1 + x 0) (hu1 : u.2 = a.2 + x 1) :
    paper2Char m x * paper2PhaseExp (-1 / τ) b u =
      paper2SPhase a m * paper2PhaseExp (-1 / τ) (paper2SAlpha b m) u := by
  rw [paper2Char_apply, paper2PhaseExp, paper2PhaseExp, paper2SPhase, paper2SAlpha,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [Fin.sum_univ_two]
  rw [paper2B0, paper2B0, hu0, hu1]
  push_cast
  ring

theorem paper2Char_mul_SFunction (a b : ℝ × ℝ) (τ : ℂ)
    (m : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    paper2Char m x * paper2SFunction a b τ x =
      paper2SPhase a m * paper2FourierIntegrand (-1 / τ)
        (paper2SAlpha b m) (a.1 + x 0, a.2 + x 1) := by
  rw [paper2SFunction_apply, paper2FourierIntegrand_eq,
    paper2FourierIntegrand_eq]
  calc
    paper2Char m x * (((paper2Rho (a.1 + x 0, a.2 + x 1) (-1 / τ) : ℝ) : ℂ) *
        paper2PhaseExp (-1 / τ) b (a.1 + x 0, a.2 + x 1)) =
      (((paper2Rho (a.1 + x 0, a.2 + x 1) (-1 / τ) : ℝ) : ℂ) *
        (paper2Char m x * paper2PhaseExp (-1 / τ) b
          (a.1 + x 0, a.2 + x 1))) := by ring
    _ = (((paper2Rho (a.1 + x 0, a.2 + x 1) (-1 / τ) : ℝ) : ℂ) *
        (paper2SPhase a m * paper2PhaseExp (-1 / τ) (paper2SAlpha b m)
          (a.1 + x 0, a.2 + x 1))) := by
      rw [paper2Char_mul_phaseExp a b (a.1 + x 0, a.2 + x 1) τ m x rfl rfl]
    _ = paper2SPhase a m *
        (((paper2Rho (a.1 + x 0, a.2 + x 1) (-1 / τ) : ℝ) : ℂ) *
          paper2PhaseExp (-1 / τ) (paper2SAlpha b m)
            (a.1 + x 0, a.2 + x 1)) := by ring

theorem paper2_integral_char_mul_SFunction_eq_phase_H
    (a b : ℝ × ℝ) (τ : ℂ) (m : Fin 2 → ℤ) :
    (∫ x : Fin 2 → ℝ, paper2Char m x * paper2SFunction a b τ x) =
      paper2SPhase a m * paper2H (-1 / τ) (paper2SAlpha b m) := by
  simp_rw [paper2Char_mul_SFunction a b τ m]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  let av : Fin 2 → ℝ := ![a.1, a.2]
  have htrans := (measurePreserving_add_right volume av).integral_comp
    (MeasurableEquiv.addRight av).measurableEmbedding
    (fun x : Fin 2 → ℝ => paper2FourierIntegrand (-1 / τ)
      (paper2SAlpha b m) (paper2FinTwoPair x))
  have hpair := (volume_preserving_finTwoArrow ℝ).integral_comp'
    (fun p : ℝ × ℝ => paper2FourierIntegrand (-1 / τ) (paper2SAlpha b m) p)
  rw [paper2H]
  calc
    (∫ x : Fin 2 → ℝ, paper2FourierIntegrand (-1 / τ)
        (paper2SAlpha b m) (a.1 + x 0, a.2 + x 1)) =
      ∫ x : Fin 2 → ℝ, paper2FourierIntegrand (-1 / τ)
        (paper2SAlpha b m) (paper2FinTwoPair (x + av)) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [paper2FinTwoPair_apply, av, Pi.add_apply,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
            congr 2 <;> ring
    _ = ∫ x : Fin 2 → ℝ, paper2FourierIntegrand (-1 / τ)
        (paper2SAlpha b m) (paper2FinTwoPair x) := htrans
    _ = ∫ p : ℝ × ℝ, paper2FourierIntegrand (-1 / τ)
        (paper2SAlpha b m) p := by
          simpa only [paper2FinTwoPair, MeasurableEquiv.finTwoArrow_apply] using hpair

theorem paper2_neg_inv_involutive {τ : ℂ} (hτ : 0 < τ.im) :
    -1 / (-1 / τ) = τ := by
  have hτ0 : τ ≠ 0 := fun h => by simpa [h] using hτ.ne'
  field_simp

theorem paper2_I_div_neg_I_mul_neg_inv {τ : ℂ} (hτ : 0 < τ.im) :
    Complex.I / (-Complex.I * (-1 / τ)) = τ := by
  have hτ0 : τ ≠ 0 := fun h => by simpa [h] using hτ.ne'
  field_simp

theorem paper2_H_neg_inv_eq_fourierIntegrand {τ : ℂ} (hτ : 0 < τ.im)
    (α : ℝ × ℝ) :
    paper2H (-1 / τ) α =
      (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        paper2FourierIntegrand τ (0, 0) α := by
  have hS := paper2_neg_inv_im_pos hτ
  rw [paper2_zwegers_lemma28 hS α, paper2FourierIntegrand]
  rw [paper2_neg_inv_involutive hτ, paper2_I_div_neg_I_mul_neg_inv hτ]
  have hτ0 : τ ≠ 0 := fun h => by simpa [h] using hτ.ne'
  have hexp : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
      ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / (-1 / τ))) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((paper2Q0 α.1 α.2 : ℝ) : ℂ) * τ) := by
    congr 1
    field_simp
  simp only [paper2B0, Complex.ofReal_zero, mul_zero, sub_self, add_zero]
  rw [hexp]
  ring

theorem paper2_integral_char_mul_SFunction
    (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) (m : Fin 2 → ℤ) :
    (∫ x : Fin 2 → ℝ, paper2Char m x * paper2SFunction a b τ x) =
      paper2SPhase a m * (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        paper2FourierIntegrand τ (0, 0) (paper2SAlpha b m) := by
  rw [paper2_integral_char_mul_SFunction_eq_phase_H,
    paper2_H_neg_inv_eq_fourierIntegrand hτ]
  ring

theorem norm_paper2SPhase (a : ℝ × ℝ) (m : Fin 2 → ℤ) :
    ‖paper2SPhase a m‖ = 1 := by
  simp [paper2SPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem summable_paper2SFourierCore (b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun m : Fin 2 → ℤ =>
      paper2FourierIntegrand τ (0, 0) (paper2SAlpha b m) := by
  have h0 : Summable fun z : ℤ =>
      Real.exp (-(2 * Real.pi * τ.im * ((b.1 - (z : ℝ)) ^ 2 / 100))) := by
    refine (summable_paper2GaussianShift (-b.1) hτ).congr fun z => ?_
    congr 1
    ring
  have hy25 : 0 < τ.im / 25 := by positivity
  have h1 : Summable fun z : ℤ =>
      Real.exp (-(2 * Real.pi * τ.im * ((b.2 + (z : ℝ) / 5) ^ 2 / 100))) := by
    refine (summable_paper2GaussianShift (5 * b.2) hy25).congr fun z => ?_
    congr 1
    ring
  have hprod : Summable fun z : ℤ × ℤ =>
      Real.exp (-(2 * Real.pi * τ.im * ((b.1 - (z.1 : ℝ)) ^ 2 / 100))) *
        Real.exp (-(2 * Real.pi * τ.im * ((b.2 + (z.2 : ℝ) / 5) ^ 2 / 100))) :=
    Summable.mul_of_nonneg h0 h1 (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  have hvec : Summable fun m : Fin 2 → ℤ =>
      Real.exp (-(2 * Real.pi * τ.im * ((b.1 - (m 0 : ℝ)) ^ 2 / 100))) *
        Real.exp (-(2 * Real.pi * τ.im * ((b.2 + (m 1 : ℝ) / 5) ^ 2 / 100))) := by
    exact (finTwoArrowEquiv ℤ).summable_iff.mpr hprod
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => ?_) (hvec.mul_left 10)
  rw [paper2_norm_fourierIntegrand]
  calc
    |paper2Rho (paper2SAlpha b m) τ| *
        Real.exp (-(2 * Real.pi * τ.im *
          paper2Q0 (paper2SAlpha b m).1 (paper2SAlpha b m).2)) ≤
      10 * Real.exp (-(2 * Real.pi * τ.im *
        (((paper2SAlpha b m).1 ^ 2 + (paper2SAlpha b m).2 ^ 2) / 100))) :=
      paper2_abs_rho_mul_exp_le hτ (paper2SAlpha b m)
    _ = 10 *
        (Real.exp (-(2 * Real.pi * τ.im * ((b.1 - (m 0 : ℝ)) ^ 2 / 100))) *
          Real.exp (-(2 * Real.pi * τ.im *
            ((b.2 + (m 1 : ℝ) / 5) ^ 2 / 100)))) := by
      rw [← Real.exp_add]
      congr 2
      rw [paper2SAlpha]
      ring

theorem summable_paper2SFunction_fourierCoeff
    (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun m : Fin 2 → ℤ =>
      ∫ x : Fin 2 → ℝ, paper2Char m x * paper2SFunction a b τ x := by
  refine Summable.of_norm ?_
  have hcore := (summable_paper2SFourierCore b hτ).norm.mul_left
    ‖(((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ)‖
  refine hcore.congr fun m => ?_
  rw [paper2_integral_char_mul_SFunction a b hτ m]
  simp only [norm_mul, norm_paper2SPhase, one_mul]

/-- Euclidean quotient and remainder in the second dual coordinate, together
with the sign change in the first, identify the Fourier lattice with five
cosets of `ℤ²`. -/
def paper2DualIndexEquiv : (Fin 2 → ℤ) ≃ Fin 5 × (ℤ × ℤ) where
  toFun m :=
    (((Int.divModEquiv 5) (m 1)).2,
      (-(m 0), ((Int.divModEquiv 5) (m 1)).1))
  invFun z := ![-z.2.1, (Int.divModEquiv 5).symm (z.2.2, z.1)]
  left_inv m := by
    funext i
    fin_cases i
    · simp
    · change (Int.divModEquiv 5).symm ((Int.divModEquiv 5) (m 1)) = m 1
      exact (Int.divModEquiv 5).symm_apply_apply _
  right_inv z := by
    rcases z with ⟨r, n1, n2⟩
    apply Prod.ext
    · change ((Int.divModEquiv 5) ((Int.divModEquiv 5).symm (n2, r))).2 = r
      rw [(Int.divModEquiv 5).apply_symm_apply]
    · apply Prod.ext
      · simp
      · change ((Int.divModEquiv 5) ((Int.divModEquiv 5).symm (n2, r))).1 = n2
        rw [(Int.divModEquiv 5).apply_symm_apply]

theorem paper2SAlpha_dualIndexEquiv_symm (b : ℝ × ℝ)
    (z : Fin 5 × (ℤ × ℤ)) :
    paper2SAlpha b (paper2DualIndexEquiv.symm z) =
      paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2 := by
  rcases z with ⟨r, n1, n2⟩
  rw [paper2SAlpha, paper2DualIndexEquiv, Equiv.coe_fn_symm_mk,
    Int.divModEquiv_symm_apply, paper2Shift]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Prod.mk.injEq]
  constructor <;> push_cast <;> ring

/-- The Fourier shift phase is the outer Corollary 2.9 phase times the theta
character with second characteristic `-a`. -/
theorem paper2SPhase_eq_ABPhase_mul (a b : ℝ × ℝ) (m : Fin 2 → ℤ) :
    paper2SPhase a m =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((paper2B0 (paper2SAlpha b m).1 (paper2SAlpha b m).2
          (-a.1) (-a.2) : ℝ) : ℂ)) := by
  rw [paper2SPhase, ← Complex.exp_add]
  congr 1
  rw [paper2B0, paper2B0, paper2SAlpha]
  push_cast
  ring

theorem paper2ThetaABTerm_eq_fourierIntegrand
    (c d : ℝ × ℝ) (τ : ℂ) (n : ℤ × ℤ) :
    paper2ThetaABTerm c d τ n =
      paper2FourierIntegrand τ d (paper2Shift c n) := by
  rw [paper2ThetaABTerm, paper2FourierIntegrand]
  congr 2
  ring

theorem paper2_exp_B_neg_mul_phaseExp_zero (a u : ℝ × ℝ) (τ : ℂ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((paper2B0 u.1 u.2 (-a.1) (-a.2) : ℝ) : ℂ)) *
      paper2PhaseExp τ (0, 0) u = paper2PhaseExp τ (-a.1, -a.2) u := by
  rw [paper2PhaseExp, paper2PhaseExp, ← Complex.exp_add]
  congr 1
  rw [paper2B0, paper2B0]
  push_cast
  ring

theorem paper2S_fourierTerm_eq_thetaTerm (a b : ℝ × ℝ) (τ : ℂ)
    (z : Fin 5 × (ℤ × ℤ)) :
    paper2SPhase a (paper2DualIndexEquiv.symm z) *
        paper2FourierIntegrand τ (0, 0)
          (paper2SAlpha b (paper2DualIndexEquiv.symm z)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        paper2ThetaABTerm (b.1, b.2 + (z.1 : ℝ) / 5)
          (-a.1, -a.2) τ z.2 := by
  rw [paper2SPhase_eq_ABPhase_mul, paper2ThetaABTerm_eq_fourierIntegrand,
    paper2SAlpha_dualIndexEquiv_symm, paper2FourierIntegrand_eq,
    paper2FourierIntegrand_eq]
  calc
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2).1
            (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2).2
            (-a.1) (-a.2) : ℝ) : ℂ))) *
        (((paper2Rho (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2) τ : ℝ) : ℂ) *
          paper2PhaseExp τ (0, 0)
            (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        (((paper2Rho (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2) τ : ℝ) : ℂ) *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((paper2B0 (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2).1
              (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2).2
              (-a.1) (-a.2) : ℝ) : ℂ)) *
            paper2PhaseExp τ (0, 0)
              (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2))) := by ring
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        (((paper2Rho (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2) τ : ℝ) : ℂ) *
          paper2PhaseExp τ (-a.1, -a.2)
            (paper2Shift (b.1, b.2 + (z.1 : ℝ) / 5) z.2)) := by
      rw [paper2_exp_B_neg_mul_phaseExp_zero]

theorem summable_paper2SPhase_mul_core
    (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun m : Fin 2 → ℤ =>
      paper2SPhase a m * paper2FourierIntegrand τ (0, 0) (paper2SAlpha b m) := by
  refine Summable.of_norm ?_
  refine (summable_paper2SFourierCore b hτ).norm.congr fun m => ?_
  rw [norm_mul, norm_paper2SPhase, one_mul]

theorem paper2_tsum_SPhase_mul_core_eq_five_theta
    (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' m : Fin 2 → ℤ,
      paper2SPhase a m * paper2FourierIntegrand τ (0, 0) (paper2SAlpha b m)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        ∑ r : Fin 5, paper2ThetaAB (b.1, b.2 + (r : ℝ) / 5)
          (-a.1, -a.2) τ := by
  rw [← paper2DualIndexEquiv.symm.tsum_eq, Summable.tsum_prod, tsum_fintype]
  · simp_rw [paper2S_fourierTerm_eq_thetaTerm]
    have hinner : ∀ r : Fin 5,
        (∑' n : ℤ × ℤ,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
            paper2ThetaABTerm (b.1, b.2 + (r : ℝ) / 5)
              (-a.1, -a.2) τ n) =
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
            paper2ThetaAB (b.1, b.2 + (r : ℝ) / 5)
              (-a.1, -a.2) τ := by
      intro r
      rw [(summable_paper2ThetaABTerm (b.1, b.2 + (r : ℝ) / 5)
        (-a.1, -a.2) hτ).tsum_mul_left, paper2ThetaAB]
    simp_rw [hinner]
    rw [Finset.mul_sum]
  · exact (summable_paper2SPhase_mul_core a b hτ).comp_injective
      paper2DualIndexEquiv.symm.injective

theorem paper2_mFourier_torusProj_zero (m : Fin 2 → ℤ) :
    UnitAddTorus.mFourier m (paper2TorusProj (Fin 2) 0) = 1 := by
  simp [UnitAddTorus.mFourier, paper2TorusProj]

/-- **Zwegers Corollary 2.9(5)** for the quadratic datum of Paper 2. -/
theorem paper2ThetaAB_neg_inv (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    paper2ThetaAB a b (-1 / τ) =
      (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        ∑ r : Fin 5, paper2ThetaAB (b.1, b.2 + (r : ℝ) / 5)
          (-a.1, -a.2) τ := by
  have hP := paper2_tsum_lattice_eq_tsum_fourier
    (paper2SFunction_locallySummable a b hτ)
    (summable_paper2SFunction_fourierCoeff a b hτ)
    (0 : Fin 2 → ℝ)
  have hpoisson : paper2ThetaAB a b (-1 / τ) =
      ∑' m : Fin 2 → ℤ,
        ∫ x : Fin 2 → ℝ, paper2Char m x * paper2SFunction a b τ x := by
    rw [← paper2_tsum_SFunction_eq_theta a b τ]
    simpa only [zero_add, paper2_mFourier_torusProj_zero, mul_one] using hP
  rw [hpoisson]
  calc
    (∑' m : Fin 2 → ℤ,
        ∫ x : Fin 2 → ℝ, paper2Char m x * paper2SFunction a b τ x) =
      ∑' m : Fin 2 → ℤ, (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        (paper2SPhase a m * paper2FourierIntegrand τ (0, 0) (paper2SAlpha b m)) := by
          refine tsum_congr fun m => ?_
          rw [paper2_integral_char_mul_SFunction a b hτ m]
          ring
    _ = (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        ∑' m : Fin 2 → ℤ,
          paper2SPhase a m * paper2FourierIntegrand τ (0, 0) (paper2SAlpha b m) := by
      rw [tsum_mul_left]
    _ = (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        ∑ r : Fin 5, paper2ThetaAB (b.1, b.2 + (r : ℝ) / 5)
          (-a.1, -a.2) τ) := by
      rw [paper2_tsum_SPhase_mul_core_eq_five_theta a b hτ]
    _ = (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 a.1 a.2 b.1 b.2 : ℝ) : ℂ)) *
        ∑ r : Fin 5, paper2ThetaAB (b.1, b.2 + (r : ℝ) / 5)
          (-a.1, -a.2) τ := by ring

theorem paper2_fixed_S_phase_cancel :
    Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((paper2B0 (1 / 2) (1 / 10) (1 / 2) (-(1 / 10)) : ℝ) : ℂ)) = 1 := by
  rw [← Complex.exp_add]
  rw [paper2B0]
  norm_num
  ring_nf
  exact Complex.exp_zero

/-- **The manuscript's `S`-transformation law.**  The sign is the cone-order
conversion: `paper2ThetaAB` uses `ρ^{c₁}-ρ^{c₂}`, while the manuscript's
assembled object uses the opposite order. -/
theorem paper2LatticeTheta_neg_inv {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta (-1 / τ) =
      -(((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
        ∑ r : Fin 5, paper2ThetaAB
          (1 / 2, -(1 / 10) + (r : ℝ) / 5)
          (-(1 / 2), -(1 / 10)) τ) := by
  rw [paper2LatticeTheta_eq_thetaAB,
    paper2ThetaAB_neg_inv (1 / 2, 1 / 10) (1 / 2, -(1 / 10)) hτ]
  let S : ℂ := ∑ r : Fin 5, paper2ThetaAB
    (1 / 2, -(1 / 10) + (r : ℝ) / 5) (-(1 / 2), -(1 / 10)) τ
  change -(1 / 2 * Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5)) *
      ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((paper2B0 (1 / 2) (1 / 10) (1 / 2) (-(1 / 10)) : ℝ) : ℂ)) * S) =
    -(((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) * S)
  calc
    -(1 / 2 * Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5)) *
        ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((paper2B0 (1 / 2) (1 / 10) (1 / 2) (-(1 / 10)) : ℝ) : ℂ)) * S) =
      -(((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
        (Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((paper2B0 (1 / 2) (1 / 10) (1 / 2) (-(1 / 10)) : ℝ) : ℂ))) * S) := by ring
    _ = -(((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) * S) := by
      rw [paper2_fixed_S_phase_cancel]
      ring

/-- The general-characteristic theta with the manuscript's cone order
`(c₂,c₁)`.  Swapping the two error kernels negates `paper2ThetaAB`. -/
def paper2ThetaAB_c2c1 (a b : ℝ × ℝ) (τ : ℂ) : ℂ :=
  -paper2ThetaAB a b τ

/-- The manuscript's displayed five-term `S`-law, now stated with its own cone
order and therefore with the positive prefactor printed in the paper. -/
theorem paper2LatticeTheta_S {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta (-1 / τ) =
      ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
        ∑ r : Fin 5, paper2ThetaAB_c2c1
          (1 / 2, -(1 / 10) + (r : ℝ) / 5)
          (-(1 / 2), -(1 / 10)) τ := by
  rw [paper2LatticeTheta_neg_inv hτ]
  simp only [paper2ThetaAB_c2c1, Finset.sum_neg_distrib]
  ring

theorem paper2_five_theta_eq_two {τ : ℂ} (hτ : 0 < τ.im) :
    (∑ r : Fin 5, paper2ThetaAB
      (1 / 2, -(1 / 10) + (r : ℝ) / 5)
      (-(1 / 2), -(1 / 10)) τ) =
      (1 + Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5)) *
          paper2ThetaAB (1 / 2, 1 / 10) (-(1 / 2), -(1 / 10)) τ +
        (1 + Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5)) *
          paper2ThetaAB (1 / 2, 7 / 10) (-(1 / 2), -(1 / 10)) τ := by
  have hsum : (∑ r : Fin 5, paper2ThetaAB
      (1 / 2, -(1 / 10) + (r : ℝ) / 5)
      (-(1 / 2), -(1 / 10)) τ) =
      paper2ThetaAB (1 / 2, -(1 / 10)) (-(1 / 2), -(1 / 10)) τ +
      paper2ThetaAB (1 / 2, 1 / 10) (-(1 / 2), -(1 / 10)) τ +
      paper2ThetaAB (1 / 2, 3 / 10) (-(1 / 2), -(1 / 10)) τ +
      paper2ThetaAB (1 / 2, 1 / 2) (-(1 / 2), -(1 / 10)) τ +
      paper2ThetaAB (1 / 2, 7 / 10) (-(1 / 2), -(1 / 10)) τ := by
    simp [Fin.sum_univ_succ]
    norm_num
    ring
  rw [hsum, paper2ThetaAB_coset_zero hτ, paper2ThetaAB_coset_two hτ,
    paper2ThetaAB_half_half_eq_zero hτ]
  ring

theorem paper2_five_theta_c2c1_eq_two {τ : ℂ} (hτ : 0 < τ.im) :
    (∑ r : Fin 5, paper2ThetaAB_c2c1
      (1 / 2, -(1 / 10) + (r : ℝ) / 5)
      (-(1 / 2), -(1 / 10)) τ) =
      (1 + Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5)) *
          paper2ThetaAB_c2c1 (1 / 2, 1 / 10) (-(1 / 2), -(1 / 10)) τ +
        (1 + Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5)) *
          paper2ThetaAB_c2c1 (1 / 2, 7 / 10) (-(1 / 2), -(1 / 10)) τ := by
  simp only [paper2ThetaAB_c2c1, Finset.sum_neg_distrib]
  rw [paper2_five_theta_eq_two hτ]
  ring

/-- The five printed components reduce algebraically to the two displayed
components isolated by the elliptic laws. -/
theorem paper2LatticeTheta_S_two_term {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta (-1 / τ) =
      ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
        ((1 + Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5)) *
            paper2ThetaAB_c2c1 (1 / 2, 1 / 10)
              (-(1 / 2), -(1 / 10)) τ +
          (1 + Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5)) *
            paper2ThetaAB_c2c1 (1 / 2, 7 / 10)
              (-(1 / 2), -(1 / 10)) τ) := by
  rw [paper2LatticeTheta_S hτ, paper2_five_theta_c2c1_eq_two hτ]

end

end Ch10
end QseriesFormalization
