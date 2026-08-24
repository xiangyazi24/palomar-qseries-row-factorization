import PalomarQseriesRowFactorization.Public
import QseriesFormalization.Ch10_Paper2_EvenCompression
import QseriesFormalization.Ch10_Paper2_SignBridge
import QseriesFormalization.Ch10_Paper2_ZwegersS

/-!
# Complete Paper 2 solution

The public definitions are transported to the exact 39-file closure extracted
from the canonical internal development. No historical Q-series certificate
route is imported by this package.
-/

namespace PalomarQseriesRowFactorization

noncomputable section

private theorem completedTheta_eq_internal (τ : ℂ) :
    paper2CompletedTheta τ =
      QseriesFormalization.Ch10.paper2LatticeTheta τ := by
  unfold paper2CompletedTheta
  exact (QseriesFormalization.Ch10.paper2LatticeTheta_eq_thetaAB τ).symm

private theorem dbar_eq_internal (f : ℂ → ℂ) (τ : ℂ) :
    dbar f τ = QseriesFormalization.Ch10.dbar f τ := by
  rw [QseriesFormalization.Ch10.dbar_eq]
  rfl

private theorem xi1_eq_internal (f : ℂ → ℂ) (τ : ℂ) :
    xi1 f τ = QseriesFormalization.Ch10.xi1 f τ := by
  unfold xi1 QseriesFormalization.Ch10.xi1
  rw [dbar_eq_internal]

private theorem Delta1_eq_internal (f : ℂ → ℂ) (τ : ℂ) :
    Delta1 f τ = QseriesFormalization.Ch10.Delta1 f τ := by
  unfold Delta1 QseriesFormalization.Ch10.Delta1
  rw [xi1_eq_internal]
  have hxi : xi1 f = QseriesFormalization.Ch10.xi1 f := by
    funext z
    exact xi1_eq_internal f z
  rw [hxi]

private theorem completedTheta_fun_eq_internal :
    paper2CompletedTheta = QseriesFormalization.Ch10.paper2LatticeTheta := by
  funext τ
  exact completedTheta_eq_internal τ

private theorem completedTheta_dbar_fun_eq_internal :
    (fun τ => dbar paper2CompletedTheta τ) =
      (fun τ => QseriesFormalization.Ch10.dbar
        QseriesFormalization.Ch10.paper2LatticeTheta τ) := by
  funext τ
  rw [dbar_eq_internal, completedTheta_fun_eq_internal]

private theorem completedTheta_xi1_fun_eq_internal :
    xi1 paper2CompletedTheta =
      QseriesFormalization.Ch10.xi1
        QseriesFormalization.Ch10.paper2LatticeTheta := by
  funext τ
  rw [xi1_eq_internal, completedTheta_fun_eq_internal]

/-! ## Registered proofs -/

theorem mk_factorization (T : Int) :
    MKcoeff T =
      ∑ a ∈ Finset.Icc (-2) T,
        QoutCoeff a * coneDiffH (T - a) := by
  change QseriesFormalization.Ch10.MKcoeff T =
    ∑ a ∈ Finset.Icc (-2) T,
      QseriesFormalization.Ch10.QoutCoeff a *
        QseriesFormalization.Ch10.coneDiffH (T - a)
  exact QseriesFormalization.Ch10.mk_factorization T

theorem coneDiffH_two_mul (N : Nat) :
    coneDiffH (2 * (N : Int)) = BCoeff N := by
  change QseriesFormalization.Ch10.coneDiffH (2 * (N : Int)) =
    QseriesFormalization.Ch10.BCoeff N
  exact QseriesFormalization.Ch10.coneDiffH_two_mul N

theorem coneDiffH_odd {m : Int} (hm : ¬ 2 ∣ m) :
    coneDiffH m = 0 := by
  change QseriesFormalization.Ch10.coneDiffH m = 0
  exact QseriesFormalization.Ch10.coneDiffH_odd hm

theorem exact_completion_bridge {τ : ℂ} (hτ : 0 < τ.im) :
    paper2CompletedTheta τ =
      paper2NomeTenth τ * paper2BSeries (paper2Nome τ) +
        paper2LatticeCorrection τ := by
  rw [completedTheta_eq_internal]
  change QseriesFormalization.Ch10.paper2LatticeTheta τ =
    QseriesFormalization.Ch10.paper2NomeTenth τ *
        QseriesFormalization.Ch10.paper2BSeries
          (QseriesFormalization.Ch10.paper2Nome τ) +
      QseriesFormalization.Ch10.paper2LatticeCorrection τ
  exact QseriesFormalization.Ch10.paper2LatticeTheta_eq_bridge hτ

theorem zwegers_lemma28 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    paper2H τ α =
      (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (Complex.I / (-Complex.I * τ))) *
        (paper2Rho α (-1 / τ) : ℂ) *
          Complex.exp
            (-(2 * (Real.pi : ℂ) * Complex.I *
              ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ)) := by
  change QseriesFormalization.Ch10.paper2H τ α =
    (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (Complex.I / (-Complex.I * τ))) *
      (QseriesFormalization.Ch10.paper2Rho α (-1 / τ) : ℂ) *
        Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I *
            ((QseriesFormalization.Ch10.paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ))
  exact QseriesFormalization.Ch10.paper2_zwegers_lemma28 hτ α

theorem completedTheta_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    paper2CompletedTheta (τ + 1) =
      Complex.exp (Real.pi * Complex.I / 5) * paper2CompletedTheta τ := by
  rw [completedTheta_eq_internal, completedTheta_eq_internal]
  exact QseriesFormalization.Ch10.paper2LatticeTheta_add_one hτ

theorem completedTheta_S {τ : ℂ} (hτ : 0 < τ.im) :
    paper2CompletedTheta (-1 / τ) =
        ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
          ∑ r : Fin 5, paper2ThetaAB_c2c1
            (1 / 2, -(1 / 10) + (r : ℝ) / 5)
            (-(1 / 2), -(1 / 10)) τ ∧
    paper2CompletedTheta (-1 / τ) =
        ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
          ((1 + Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5)) *
              paper2ThetaAB_c2c1
                (1 / 2, 1 / 10) (-(1 / 2), -(1 / 10)) τ +
            (1 + Complex.exp (3 * Real.pi * Complex.I / 5)) *
              paper2ThetaAB_c2c1
                (1 / 2, 7 / 10) (-(1 / 2), -(1 / 10)) τ) := by
  constructor
  · rw [completedTheta_eq_internal]
    change QseriesFormalization.Ch10.paper2LatticeTheta (-1 / τ) =
      ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
        ∑ r : Fin 5, QseriesFormalization.Ch10.paper2ThetaAB_c2c1
          (1 / 2, -(1 / 10) + (r : ℝ) / 5)
          (-(1 / 2), -(1 / 10)) τ
    exact QseriesFormalization.Ch10.paper2LatticeTheta_S hτ
  · rw [completedTheta_eq_internal]
    change QseriesFormalization.Ch10.paper2LatticeTheta (-1 / τ) =
      ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
        ((1 + Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5)) *
            QseriesFormalization.Ch10.paper2ThetaAB_c2c1
              (1 / 2, 1 / 10) (-(1 / 2), -(1 / 10)) τ +
          (1 + Complex.exp (3 * Real.pi * Complex.I / 5)) *
            QseriesFormalization.Ch10.paper2ThetaAB_c2c1
              (1 / 2, 7 / 10) (-(1 / 2), -(1 / 10)) τ)
    exact QseriesFormalization.Ch10.paper2LatticeTheta_S_two_term hτ

theorem exact_differential_image {τ : ℂ} (hτ : 0 < τ.im) :
    dbar paper2CompletedTheta τ =
        -(Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            paper2ThetaComponent (j : ℤ) τ *
              (starRingEnd ℂ) (paper2GComponent (j : ℤ) τ) ∧
    xi1 paper2CompletedTheta τ =
        -(((Real.sqrt τ.im / (2 * Real.sqrt 10) : ℝ)) : ℂ) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) τ) *
              paper2GComponent (j : ℤ) τ := by
  constructor
  · rw [dbar_eq_internal, completedTheta_fun_eq_internal]
    change QseriesFormalization.Ch10.dbar
        QseriesFormalization.Ch10.paper2LatticeTheta τ =
      -(Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
        ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
          QseriesFormalization.Ch10.paper2ThetaComponent (j : ℤ) τ *
            (starRingEnd ℂ)
              (QseriesFormalization.Ch10.paper2GComponent (j : ℤ) τ)
    exact QseriesFormalization.Ch10.paper2_dbar_latticeTheta_exact hτ
  · rw [xi1_eq_internal, completedTheta_fun_eq_internal]
    change QseriesFormalization.Ch10.xi1
        QseriesFormalization.Ch10.paper2LatticeTheta τ =
      -(((Real.sqrt τ.im / (2 * Real.sqrt 10) : ℝ)) : ℂ) *
        ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
          (starRingEnd ℂ)
              (QseriesFormalization.Ch10.paper2ThetaComponent (j : ℤ) τ) *
            QseriesFormalization.Ch10.paper2GComponent (j : ℤ) τ
    exact QseriesFormalization.Ch10.paper2_xi1_latticeTheta_exact hτ

theorem completedTheta_not_harmonic :
    Delta1 paper2CompletedTheta (2 * Complex.I) ≠ 0 ∧
    dbar (xi1 paper2CompletedTheta) (2 * Complex.I) ≠ 0 ∧
    (fun τ => dbar paper2CompletedTheta τ) ≠ 0 ∧
    xi1 paper2CompletedTheta ≠ 0 := by
  have hxi : xi1 paper2CompletedTheta =
      QseriesFormalization.Ch10.xi1
        QseriesFormalization.Ch10.paper2LatticeTheta :=
    completedTheta_xi1_fun_eq_internal
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Delta1_eq_internal, completedTheta_fun_eq_internal]
    exact QseriesFormalization.Ch10.paper2_delta1_latticeTheta_two_I_ne_zero
  · rw [dbar_eq_internal, hxi]
    exact QseriesFormalization.Ch10.paper2_dbar_xi1_latticeTheta_two_I_ne_zero
  · rw [completedTheta_dbar_fun_eq_internal]
    exact QseriesFormalization.Ch10.paper2_dbar_latticeTheta_ne_zero
  · rw [hxi]
    exact QseriesFormalization.Ch10.paper2_xi1_latticeTheta_ne_zero

end

end PalomarQseriesRowFactorization
