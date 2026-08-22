import QseriesFormalization.Ch10_MockModular_Sigma
import QseriesFormalization.Ch10_MockModular_Involution

/-!
# Ch10: coefficientwise definitions for the missing kernel

There are no infinite-series objects in this file.  Every coefficient is a
finite `Finset` sum, with an explicit window and a completeness lemma for that
window.
-/

namespace QseriesFormalization
namespace Ch10

noncomputable section

set_option maxHeartbeats 400000

/-! ## Exponents and signs -/

/-- The paper's `H`; this is exactly the already formalized quadratic `Q`. -/
abbrev Hq (k r : ℤ) : ℤ := Q k r

def Qout (u v : ℤ) : ℤ :=
  5 * u ^ 2 - 3 * u + 5 * v ^ 2 - 7 * v

/-- The integer value of Mathlib's unit-valued `Int.negOnePow`. -/
def mkSign (n : ℤ) : ℤ := (Int.negOnePow n : ℤ)

theorem mkSign_eq_negOnePowInt (n : ℤ) :
    mkSign n = negOnePowInt n := by
  rcases Int.even_or_odd n with hn | hn
  · have hmod : n % 2 = 0 :=
      Int.not_odd_iff.mp (Int.not_odd_iff_even.mpr hn)
    simp [mkSign, negOnePowInt, hmod, Int.negOnePow_even n hn]
  · have hmod : n % 2 = 1 := Int.odd_iff.mp hn
    have hne : n % 2 ≠ 0 := by omega
    simp [mkSign, negOnePowInt, hne, Int.negOnePow_odd n hn]

/-! ## The two positive-definite theta legs -/

theorem abs_u_le_of_thetaU (u a : ℤ)
    (h : 5 * u ^ 2 - 3 * u = a) : u ^ 2 ≤ a + 2 := by
  rw [← h]
  nlinarith [sq_nonneg (8 * u - 3)]

theorem abs_v_le_of_thetaV (v a : ℤ)
    (h : 5 * v ^ 2 - 7 * v = a) : v ^ 2 ≤ a + 3 := by
  rw [← h]
  by_cases hv : v ≤ 0
  · nlinarith [sq_nonneg v]
  · have hv1 : 1 ≤ v := by omega
    have hp : 0 ≤ (v - 1) * (4 * v - 3) :=
      mul_nonneg (by omega) (by omega)
    nlinarith

def thetaUBound (a : ℤ) : ℤ := |a| + 3

def thetaVBound (a : ℤ) : ℤ := |a| + 4

theorem thetaU_solution_mem_window (u a : ℤ)
    (h : 5 * u ^ 2 - 3 * u = a) :
    u ∈ Finset.Icc (-thetaUBound a) (thetaUBound a) := by
  rw [Finset.mem_Icc]
  have hu := abs_u_le_of_thetaU u a h
  have ha : a ≤ |a| := le_abs_self a
  constructor <;> unfold thetaUBound <;>
    nlinarith [sq_nonneg (2 * u - 1), sq_nonneg (2 * u + 1)]

theorem thetaV_solution_mem_window (v a : ℤ)
    (h : 5 * v ^ 2 - 7 * v = a) :
    v ∈ Finset.Icc (-thetaVBound a) (thetaVBound a) := by
  rw [Finset.mem_Icc]
  have hv := abs_v_le_of_thetaV v a h
  have ha : a ≤ |a| := le_abs_self a
  constructor <;> unfold thetaVBound <;>
    nlinarith [sq_nonneg (2 * v - 1), sq_nonneg (2 * v + 1)]

def thetaUCoeff (a : ℤ) : ℤ :=
  ∑ u ∈ Finset.Icc (-thetaUBound a) (thetaUBound a),
    if 5 * u ^ 2 - 3 * u = a then mkSign u else 0

def thetaVCoeff (a : ℤ) : ℤ :=
  ∑ v ∈ Finset.Icc (-thetaVBound a) (thetaVBound a),
    if 5 * v ^ 2 - 7 * v = a then mkSign v else 0

theorem thetaU_exponent_nonneg (u : ℤ) :
    0 ≤ 5 * u ^ 2 - 3 * u := by
  by_cases hu : u ≤ 0
  · nlinarith [sq_nonneg u]
  · have hu1 : 1 ≤ u := by omega
    have hp : 0 ≤ u * (5 * u - 3) :=
      mul_nonneg (by omega) (by omega)
    nlinarith

theorem thetaV_exponent_ge_neg_two (v : ℤ) :
    -2 ≤ 5 * v ^ 2 - 7 * v := by
  by_cases hv : v ≤ 0
  · nlinarith [sq_nonneg v]
  · by_cases hv1 : v = 1
    · subst v
      norm_num
    · have hv2 : 2 ≤ v := by omega
      have hp : 0 ≤ (v - 1) * (5 * v - 2) :=
        mul_nonneg (by omega) (by omega)
      nlinarith

theorem thetaUCoeff_vanish_below {a : ℤ} (ha : a < 0) :
    thetaUCoeff a = 0 := by
  unfold thetaUCoeff
  apply Finset.sum_eq_zero
  intro u _hu
  split_ifs with h
  · have := thetaU_exponent_nonneg u
    omega
  · rfl

theorem thetaVCoeff_vanish_below {a : ℤ} (ha : a < -2) :
    thetaVCoeff a = 0 := by
  unfold thetaVCoeff
  apply Finset.sum_eq_zero
  intro v _hv
  split_ifs with h
  · have := thetaV_exponent_ge_neg_two v
    omega
  · rfl

/-- Coefficient of the product of the two theta legs. -/
def QoutCoeff (a : ℤ) : ℤ :=
  ∑ i ∈ Finset.Icc 0 (a + 2), thetaUCoeff i * thetaVCoeff (a - i)

theorem QoutCoeff_vanish_below {a : ℤ} (ha : a < -2) :
    QoutCoeff a = 0 := by
  unfold QoutCoeff
  rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]

/-! ## Finite root fibers of a fixed `Hq` row -/

def rowDisc (k m : ℤ) : ℤ :=
  4 * m - (16 * k ^ 2 + 8 * k) + (6 * k + 1) ^ 2

theorem row_square_identity (k r m : ℤ) (h : Hq k r = m) :
    (2 * r + 6 * k + 1) ^ 2 = rowDisc k m := by
  unfold Hq Q at h
  unfold rowDisc
  nlinarith

def rowRBound (k m : ℤ) : ℤ :=
  |rowDisc k m| + |6 * k + 1| + 2

theorem row_root_mem_window (k r m : ℤ) (h : Hq k r = m) :
    r ∈ Finset.Icc (-rowRBound k m) (rowRBound k m) := by
  rw [Finset.mem_Icc]
  let x : ℤ := 2 * r + 6 * k + 1
  have hx : x ^ 2 = rowDisc k m := by
    simpa [x] using row_square_identity k r m h
  have hdisc : 0 ≤ rowDisc k m := by
    rw [← hx]
    exact sq_nonneg x
  have hxu : x ≤ rowDisc k m + 1 := by
    rw [← hx]
    nlinarith [sq_nonneg (2 * x - 1)]
  have hxl : -x ≤ rowDisc k m + 1 := by
    rw [← hx]
    nlinarith [sq_nonneg (2 * x + 1)]
  have hd : rowDisc k m ≤ |rowDisc k m| := le_abs_self _
  have hc1 : 6 * k + 1 ≤ |6 * k + 1| := le_abs_self _
  have hc2 : -(6 * k + 1) ≤ |6 * k + 1| := neg_le_abs _
  unfold rowRBound
  dsimp [x] at hxu hxl
  constructor <;> omega

def rowFiber (k m : ℤ) : Finset ℤ :=
  (Finset.Icc (-rowRBound k m) (rowRBound k m)).filter
    (fun r => Hq k r = m)

def mixedSide (k r : ℤ) : Prop :=
  (0 ≤ k ∧ r ≤ -1) ∨ (k ≤ -1 ∧ 0 ≤ r)

def coneSide (k r : ℤ) : Prop :=
  (0 ≤ k ∧ 0 ≤ r) ∨ (k ≤ -1 ∧ r ≤ -1)

instance (k r : ℤ) : Decidable (mixedSide k r) := by
  unfold mixedSide; infer_instance
instance (k r : ℤ) : Decidable (coneSide k r) := by
  unfold coneSide; infer_instance

def rowMixedCoeff (k m : ℤ) : ℤ :=
  ((rowFiber k m).filter (mixedSide k)).sum mkSign

def rowConeCoeff (k m : ℤ) : ℤ :=
  ((rowFiber k m).filter (coneSide k)).sum mkSign

def rowMin (k : ℤ) : ℤ :=
  if 0 ≤ k then 4 * k ^ 2 + 2 * k else 4 * k ^ 2 - 4 * k

def rowEpsilon (k : ℤ) : ℤ := if 0 ≤ k then 1 else -1

/-- The transported row, with the `D-A` outer sign already included. -/
def coneSignedCoeff (k m : ℤ) : ℤ :=
  -rowEpsilon k * rowConeCoeff k m

def mkKBound (T : ℤ) : ℤ := |T| + 3

def mkRowCoeff (k T : ℤ) : ℤ :=
  ∑ a ∈ Finset.Icc (-2) (T - rowMin k),
    QoutCoeff a * rowMixedCoeff k (T - a)

/-- Missing-kernel coefficient, using the paper's row convention. -/
def MKcoeff (T : ℤ) : ℤ :=
  ∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
    rowEpsilon k * mkRowCoeff k T

def coneKBound (m : ℤ) : ℤ := |m| + 1

/-- The `H`-level coefficient of the cone difference `D-A`. -/
def coneDiffH (m : ℤ) : ℤ :=
  ∑ k ∈ Finset.Icc (-coneKBound m) (coneKBound m),
    coneSignedCoeff k m

end

end Ch10
end QseriesFormalization
