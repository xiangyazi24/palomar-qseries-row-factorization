import QseriesFormalization.Ch10_NormTheta_Defs

/-!
# Ch10: Odd Theta Vanishing

The unary theta series Σ_{x∈ℤ} (-1)^x q^{c·x·(x+1)} vanishes identically
because the involution x ↦ -(x+1) preserves c·x·(x+1) and flips (-1)^x.

This is used for the one-sided completion: the correction term R_{c₁}
vanishes because the associated unary theta is odd.

## Main results

* `thetaInvol_preserves_product`: x*(x+1) is invariant under x ↦ -(x+1)
* `odd_theta_fiber_cancel`: (-1)^x + (-1)^{-(x+1)} = 0
* `fiber_pair`: if x*(x+1) = y*(y+1) then x = y or x = -(y+1)
-/

namespace QseriesFormalization
namespace Ch10

/-! ## The involution x ↦ -(x+1) -/

def thetaInvol (x : Int) : Int := -(x + 1)

theorem thetaInvol_involutive (x : Int) : thetaInvol (thetaInvol x) = x := by
  unfold thetaInvol; ring

theorem thetaInvol_no_fixed_point (x : Int) : thetaInvol x ≠ x := by
  unfold thetaInvol; omega

theorem thetaInvol_preserves_product (x : Int) :
    thetaInvol x * (thetaInvol x + 1) = x * (x + 1) := by
  unfold thetaInvol; ring

theorem thetaInvol_flips_parity (x : Int) :
    (thetaInvol x) % 2 ≠ x % 2 := by
  unfold thetaInvol; omega

/-! ## Sign cancellation -/

theorem negOnePowInt_thetaInvol (x : Int) :
    negOnePowInt (thetaInvol x) = -negOnePowInt x := by
  unfold negOnePowInt thetaInvol; split_ifs <;> omega

theorem odd_theta_fiber_cancel (x : Int) :
    negOnePowInt x + negOnePowInt (thetaInvol x) = 0 := by
  rw [negOnePowInt_thetaInvol]; omega

/-! ## Fiber classification

For any m : ℕ, the set {x : ℤ | x*(x+1) = m} is either empty or
consists of exactly two elements {x₀, -(x₀+1)} with opposite parity.
-/

theorem fiber_pair (x y : Int) (hx : x * (x + 1) = y * (y + 1)) :
    x = y ∨ x = thetaInvol y := by
  unfold thetaInvol
  have h : (2 * x + 1) ^ 2 = (2 * y + 1) ^ 2 := by nlinarith
  have h2 : 2 * x + 1 = 2 * y + 1 ∨ 2 * x + 1 = -(2 * y + 1) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h <;> [left; right] <;> linarith
  rcases h2 with h | h <;> [left; right] <;> omega

end Ch10
end QseriesFormalization
