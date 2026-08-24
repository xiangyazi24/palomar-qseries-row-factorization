import QseriesFormalization.Ch10_MK_Main
import QseriesFormalization.Pending.Chapter10_HM

/-!
# Paper 2: formal Laurent row-model factorization

This file upgrades the finite coefficient theorem `Ch10.mk_factorization` to
the formal Laurent-series identity in the row-model section of Paper 2.  The
Jacobi triple product is not reproved: the two theta legs are identified with
the reusable `jLaurent` object from the Chapter 10 Hickerson--Mortenson
development, and `jLaurent_eq_tripleProductInf` supplies the product side.

The exponent variable here is the paper's `H`-level variable `x`.  The later
even-support compression to the `E`-level variable `q = x^2` is kept separate
so the normalization cannot be mixed accidentally.
-/

namespace QseriesFormalization
namespace Ch10

open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.JTPFormalPSPentagonal

noncomputable section

/-! ## Coefficient windows for the two Jacobi legs -/

/-- Enlarging the explicit coefficient window does not change the
`5u^2-3u` theta coefficient, because every root lies in `thetaUBound`. -/
theorem thetaUCoeff_eq_sum_Icc_of_bound (a W : ℤ)
    (hW : thetaUBound a ≤ W) :
    thetaUCoeff a =
      ∑ u ∈ Finset.Icc (-W) W,
        if 5 * u ^ 2 - 3 * u = a then mkSign u else 0 := by
  unfold thetaUCoeff
  refine Finset.sum_subset ?_ ?_
  · intro u hu
    rw [Finset.mem_Icc] at hu ⊢
    constructor <;> omega
  · intro u hu hnot
    by_cases hroot : 5 * u ^ 2 - 3 * u = a
    · exact absurd (thetaU_solution_mem_window u a hroot) hnot
    · simp [hroot]

/-- Enlarging the explicit coefficient window does not change the
`5v^2-7v` theta coefficient, because every root lies in `thetaVBound`. -/
theorem thetaVCoeff_eq_sum_Icc_of_bound (a W : ℤ)
    (hW : thetaVBound a ≤ W) :
    thetaVCoeff a =
      ∑ v ∈ Finset.Icc (-W) W,
        if 5 * v ^ 2 - 7 * v = a then mkSign v else 0 := by
  unfold thetaVCoeff
  refine Finset.sum_subset ?_ ?_
  · intro v hv
    rw [Finset.mem_Icc] at hv ⊢
    constructor <;> omega
  · intro v hv hnot
    by_cases hroot : 5 * v ^ 2 - 7 * v = a
    · exact absurd (thetaV_solution_mem_window v a hroot) hnot
    · simp [hroot]

/-- The Jacobi exponent at `(a,b)=(2,10)` is the first theta-leg exponent. -/
theorem jExp_two_ten (n : ℤ) :
    jExp 2 10 n = 5 * n ^ 2 - 3 * n := by
  have h := two_mul_jExp 2 10 n
  unfold jExpTwice at h
  nlinarith

/-- The Jacobi exponent at `(a,b)=(-2,10)` is the second theta-leg exponent. -/
theorem jExp_neg_two_ten (n : ℤ) :
    jExp (-2) 10 n = 5 * n ^ 2 - 7 * n := by
  have h := two_mul_jExp (-2) 10 n
  unfold jExpTwice at h
  nlinarith

/-- The rational sign in `jLaurent` is the cast of the integer row sign. -/
theorem negOnePowIntQ_eq_cast_mkSign (n : ℤ) :
    negOnePowIntQ n = (mkSign n : ℚ) := by
  rw [negOnePowIntQ_eq_negOnePow]
  rfl

/-- The concrete first-leg coefficient is exactly the coefficient of
`j(Q^2;Q^10)` in the reusable formal Laurent model. -/
theorem cast_thetaUCoeff_eq_jCoeff (e : ℤ) :
    (thetaUCoeff e : ℚ) = jCoeff 2 10 e := by
  let W : ℤ := max (thetaUBound e) (jCoeffWindow 2 10 e)
  have htheta : thetaUCoeff e =
      ∑ n ∈ Finset.Icc (-W) W,
        if 5 * n ^ 2 - 3 * n = e then mkSign n else 0 :=
    thetaUCoeff_eq_sum_Icc_of_bound e W (le_max_left _ _)
  have hj : jCoeff 2 10 e =
      ∑ n ∈ Finset.Icc (-W) W,
        if jExp 2 10 n = e then negOnePowIntQ n else 0 :=
    jCoeff_eq_sum_Icc_of_window_le 2 10 e W (by norm_num) (le_max_right _ _)
  rw [htheta, hj]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [jExp_two_ten, negOnePowIntQ_eq_cast_mkSign]

/-- The concrete second-leg coefficient is exactly the coefficient of
`j(Q^-2;Q^10)` in the reusable formal Laurent model. -/
theorem cast_thetaVCoeff_eq_jCoeff (e : ℤ) :
    (thetaVCoeff e : ℚ) = jCoeff (-2) 10 e := by
  let W : ℤ := max (thetaVBound e) (jCoeffWindow (-2) 10 e)
  have htheta : thetaVCoeff e =
      ∑ n ∈ Finset.Icc (-W) W,
        if 5 * n ^ 2 - 7 * n = e then mkSign n else 0 :=
    thetaVCoeff_eq_sum_Icc_of_bound e W (le_max_left _ _)
  have hj : jCoeff (-2) 10 e =
      ∑ n ∈ Finset.Icc (-W) W,
        if jExp (-2) 10 n = e then negOnePowIntQ n else 0 :=
    jCoeff_eq_sum_Icc_of_window_le (-2) 10 e W (by norm_num) (le_max_right _ _)
  rw [htheta, hj]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [jExp_neg_two_ten, negOnePowIntQ_eq_cast_mkSign]

/-! ## Laurent-series objects and their coefficient specifications -/

/-- The first positive-definite theta leg
`sum_u (-1)^u Q^(5u^2-3u)`, represented by `j(Q^2;Q^10)`. -/
def paper2ThetaU : QLaurent := jLaurent 2 10

/-- The second positive-definite theta leg
`sum_v (-1)^v Q^(5v^2-7v)`, represented by `j(Q^-2;Q^10)`. -/
def paper2ThetaV : QLaurent := jLaurent (-2) 10

@[simp] theorem lcoeff_paper2ThetaU (e : ℤ) :
    lcoeff paper2ThetaU e = (thetaUCoeff e : ℚ) := by
  rw [paper2ThetaU, coeff_jLaurent, cast_thetaUCoeff_eq_jCoeff]

@[simp] theorem lcoeff_paper2ThetaV (e : ℤ) :
    lcoeff paper2ThetaV e = (thetaVCoeff e : ℚ) := by
  rw [paper2ThetaV, coeff_jLaurent, cast_thetaVCoeff_eq_jCoeff]

/-- The paper's reindex `u=1-v`: the second theta leg is the shifted negative
of the first leg. -/
theorem paper2ThetaV_eq_neg_shift_thetaU :
    paper2ThetaV = -Qpow (-2) * paper2ThetaU := by
  have hshift := jLaurent_shift 8 10 (-1) (by norm_num)
  have hsymm := jLaurent_symm 2 10 (by norm_num)
  have hsymm' : jLaurent 8 10 = jLaurent 2 10 := by
    simpa using hsymm.symm
  rw [paper2ThetaV, paper2ThetaU]
  calc
    jLaurent (-2) 10 = -Qpow (-2) * jLaurent 8 10 := by
      simpa [jShiftExp, negOnePowIntQ] using hshift
    _ = -Qpow (-2) * jLaurent 2 10 := by rw [hsymm']

/-- Jacobi's triple product for the first Paper 2 theta leg, obtained by the
`(a,b)=(2,10)` specialization of the existing formal Laurent theorem. -/
theorem paper2ThetaU_eq_tripleProduct :
    paper2ThetaU =
      ((qPochAPPS ℚ 10 10 : PowerSeries ℚ) : QLaurent) *
        ((qPochAPPS ℚ 2 10 : PowerSeries ℚ) : QLaurent) *
          ((qPochAPPS ℚ 8 10 : PowerSeries ℚ) : QLaurent) := by
  simpa [paper2ThetaU] using jLaurent_eq_tripleProductInf 2 10 (by norm_num) (by norm_num)

/-- Laurent series whose coefficient is the finite convolution `QoutCoeff`. -/
def paper2QoutLaurent : QLaurent := paper2ThetaU * paper2ThetaV

/-- Laurent series of the same-sign cone difference at the `H`-level. -/
def paper2ConeLaurent : QLaurent :=
  HahnSeries.ofSuppBddBelow (fun e : ℤ => (coneDiffH e : ℚ)) <| by
    refine ⟨0, ?_⟩
    intro e he
    by_contra hnonneg
    have hz : coneDiffH e = 0 := coneDiffH_vanish_below_zero (by omega)
    exact he (by simp [hz])

/-- Laurent series of the row-model kernel, with coefficient `MKcoeff`. -/
def paper2MKLaurent : QLaurent :=
  HahnSeries.ofSuppBddBelow (fun e : ℤ => (MKcoeff e : ℚ)) <| by
    refine ⟨-2, ?_⟩
    intro e he
    by_contra hlow
    have hz : MKcoeff e = 0 := by
      rw [mk_factorization, Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]
    exact he (by simp [hz])

@[simp] theorem lcoeff_paper2ConeLaurent (e : ℤ) :
    lcoeff paper2ConeLaurent e = (coneDiffH e : ℚ) := by
  simp [lcoeff, paper2ConeLaurent]

@[simp] theorem lcoeff_paper2MKLaurent (e : ℤ) :
    lcoeff paper2MKLaurent e = (MKcoeff e : ℚ) := by
  simp [lcoeff, paper2MKLaurent]

/-- Multiplying the two theta legs gives exactly the finite coefficient
convolution `QoutCoeff`; the lower supports are `0` and `-2`. -/
theorem lcoeff_paper2QoutLaurent (e : ℤ) :
    lcoeff paper2QoutLaurent e = (QoutCoeff e : ℚ) := by
  rw [paper2QoutLaurent]
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt paper2ThetaU paper2ThetaV 0 (-2) e]
  · rw [show e - (-2) = e + 2 by ring]
    rw [QoutCoeff]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [lcoeff_paper2ThetaU, lcoeff_paper2ThetaV]
  · intro n hn
    rw [lcoeff_paper2ThetaU]
    simp [thetaUCoeff_vanish_below hn]
  · intro n hn
    rw [lcoeff_paper2ThetaV]
    simp [thetaVCoeff_vanish_below hn]

/-- Coefficientwise row transport assembles to the Paper 2 Laurent identity
`MK = Theta_u * Theta_v * (D-A)`. -/
theorem paper2MKLaurent_eq_theta_mul_cone :
    paper2MKLaurent = paper2ThetaU * paper2ThetaV * paper2ConeLaurent := by
  ext e
  change lcoeff paper2MKLaurent e =
    lcoeff (paper2ThetaU * paper2ThetaV * paper2ConeLaurent) e
  rw [lcoeff_paper2MKLaurent]
  rw [show paper2ThetaU * paper2ThetaV = paper2QoutLaurent by rfl]
  rw [lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt paper2QoutLaurent paper2ConeLaurent
    (-2) 0 e]
  · rw [show e - 0 = e by ring]
    rw [mk_factorization]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [lcoeff_paper2QoutLaurent, lcoeff_paper2ConeLaurent]
  · intro n hn
    rw [lcoeff_paper2QoutLaurent]
    simp [QoutCoeff_vanish_below hn]
  · intro n hn
    rw [lcoeff_paper2ConeLaurent]
    simp [coneDiffH_vanish_below_zero hn]

/-- Product form of the Paper 2 row-model kernel at the `H`-level.  This is
the manuscript's first boxed factorization before even-support compression. -/
theorem paper2MKLaurent_eq_jacobi_sq_mul_cone :
    paper2MKLaurent =
      (-Qpow (-2) * paper2ThetaU ^ 2) * paper2ConeLaurent := by
  rw [paper2MKLaurent_eq_theta_mul_cone, paper2ThetaV_eq_neg_shift_thetaU]
  ring

end

end Ch10
end QseriesFormalization
