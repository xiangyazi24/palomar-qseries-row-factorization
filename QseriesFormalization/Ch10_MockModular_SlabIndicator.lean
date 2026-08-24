import QseriesFormalization.Ch10_MockModular_Pell
import QseriesFormalization.Ch10_MockModular_Sigma

/-!
# Ch10: Slab Indicator = Zwegers Cone Sign Difference

The slab indicator function equals ½(sgn B(v,c₁) − sgn B(v,c₂)),
stated in integer form: 2 · slabInd(k,r) = sgnZ(BAff(v,c₁)) − sgnZ(BAff(v,c₂)).

## Main result

* `two_mul_slabInd_eq_sign_diff`: the doubled identity over ℤ
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Custom integer sign function -/

def sgnZ (n : Int) : Int := if 0 < n then 1 else -1

@[simp] theorem sgnZ_pos {n : Int} (h : 0 < n) : sgnZ n = 1 := by
  simp [sgnZ, h]

@[simp] theorem sgnZ_neg {n : Int} (h : n < 0) : sgnZ n = -1 := by
  have : ¬ (0 < n) := by omega
  simp [sgnZ, this]

@[simp] theorem sgnZ_neg' {n : Int} (h : n ≤ 0) (h2 : n ≠ 0) : sgnZ n = -1 := by
  have : n < 0 := by omega
  exact sgnZ_neg this

/-! ## Slab indicator (integer-valued, ±1 or 0) -/

def slabInd (k r : Int) : Int :=
  if 0 ≤ k ∧ r ≤ -(6 * k + 1) then -1
  else if k ≤ -1 ∧ -6 * k ≤ r then 1
  else 0

/-! ## The doubled cone-indicator identity -/

theorem two_mul_slabInd_eq_sign_diff (k r : Int) :
    2 * slabInd k r =
      sgnZ (BAff (pellCoord k r) c1) -
      sgnZ (BAff (pellCoord k r) c2) := by
  simp only [BAff_pellCoord_c1, BAff_pellCoord_c2]
  unfold slabInd sgnZ
  split_ifs <;> omega

end Ch10
end QseriesFormalization
