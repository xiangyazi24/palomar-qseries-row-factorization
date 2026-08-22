import QseriesFormalization.Ch10_NormTheta_Defs
import QseriesFormalization.Ch10_NormTheta_Algebra

/-!
# Ch10: Sigma Involution and Slab Decomposition

The sigma involution σ_k(r) = -(6k+1)-r cancels the interior of the
cone-difference sum, leaving a thin "slab" residual.

## Main results

* `sigma_preserves_Q`: Q(k, σ_k(r)) = Q(k, r)
* `sigma_flips_sign`: negOnePowInt(σ_k(r)) = -negOnePowInt(r)
* `sigma_no_fixed_point`: σ_k(r) ≠ r
* `sigma_involutive`: σ_k(σ_k(r)) = r

These are the algebraic ingredients for Theorem (slab) in the paper.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## The sigma involution -/

def sigma (k r : Int) : Int := -(6 * k + 1) - r

theorem sigma_eq (k r : Int) : sigma k r = -(6 * k + 1) - r := rfl

/-! ## σ preserves Q -/

theorem sigma_preserves_Q (k r : Int) : Q k (sigma k r) = Q k r := by
  unfold Q sigma
  ring

theorem sigma_preserves_E (k r : Int) : E k (sigma k r) = E k r := by
  have h1 := Q_eq_two_mul_E k r
  have h2 := Q_eq_two_mul_E k (sigma k r)
  rw [sigma_preserves_Q] at h2
  omega

/-! ## σ flips parity -/

theorem sigma_flips_parity (k r : Int) :
    (sigma k r) % 2 ≠ r % 2 := by
  unfold sigma
  omega

theorem sigma_flips_sign (k r : Int) :
    negOnePowInt (sigma k r) = -negOnePowInt r := by
  unfold negOnePowInt sigma
  split_ifs with h1 h2 <;> omega

/-! ## σ has no fixed points -/

theorem sigma_no_fixed_point (k r : Int) : sigma k r ≠ r := by
  unfold sigma; omega

/-! ## σ is an involution -/

theorem sigma_involutive (k r : Int) : sigma k (sigma k r) = r := by
  unfold sigma; ring

/-! ## Slab and Interior regions -/

def InSlabPlus (k r : Int) : Prop := 0 ≤ k ∧ r ≤ -(6 * k + 1)

def InSlabMinus (k r : Int) : Prop := k ≤ -1 ∧ -6 * k ≤ r

def InSlab (k r : Int) : Prop := InSlabPlus k r ∨ InSlabMinus k r

def InHalfB (k r : Int) : Prop :=
  (0 ≤ k ∧ r ≤ -1) ∨ (k ≤ -1 ∧ 0 ≤ r)

def InInterior (k r : Int) : Prop :=
  InHalfB k r ∧ ¬ InSlab k r

instance (k r : Int) : Decidable (InSlabPlus k r) :=
  show Decidable (0 ≤ k ∧ r ≤ -(6 * k + 1)) from inferInstance

instance (k r : Int) : Decidable (InSlabMinus k r) :=
  show Decidable (k ≤ -1 ∧ -6 * k ≤ r) from inferInstance

instance (k r : Int) : Decidable (InSlab k r) :=
  show Decidable (InSlabPlus k r ∨ InSlabMinus k r) from inferInstance

instance (k r : Int) : Decidable (InHalfB k r) :=
  show Decidable ((0 ≤ k ∧ r ≤ -1) ∨ (k ≤ -1 ∧ 0 ≤ r)) from inferInstance

instance (k r : Int) : Decidable (InInterior k r) :=
  show Decidable (InHalfB k r ∧ ¬ InSlab k r) from inferInstance

/-! ## σ maps Interior to Interior -/

theorem sigma_maps_interior_nonneg (k r : Int) (_hk : 0 ≤ k)
    (hr_lo : -(6 * k) ≤ r) (hr_hi : r ≤ -1) :
    -(6 * k) ≤ sigma k r ∧ sigma k r ≤ -1 := by
  constructor <;> (unfold sigma; omega)

theorem sigma_maps_interior_neg (k r : Int) (_hk : k ≤ -1)
    (hr_lo : 0 ≤ r) (hr_hi : r ≤ -6 * k - 1) :
    0 ≤ sigma k r ∧ sigma k r ≤ -6 * k - 1 := by
  constructor <;> (unfold sigma; omega)

/-! ## Pell coordinates -/

def pellX (k r : Int) : Int := r + 3 * k
def pellY (k _r : Int) : Int := k

def Q_form (x y : Int) : Int := x ^ 2 - 5 * y ^ 2

theorem pell_coords_Q (k r : Int) :
    Q_form (pellX k r) (pellY k r) = 4 * k ^ 2 + 6 * k * r + r ^ 2 := by
  unfold Q_form pellX pellY; ring

/-! ## Pell automorph (in Pell coordinates) -/

def pellAutomorphX (x y : Int) : Int := 9 * x + 20 * y
def pellAutomorphY (x y : Int) : Int := 4 * x + 9 * y

theorem pell_automorph_preserves_Q (x y : Int) :
    Q_form (pellAutomorphX x y) (pellAutomorphY x y) = Q_form x y := by
  unfold Q_form pellAutomorphX pellAutomorphY; ring

theorem pell_automorph_mod2_x (x y : Int) :
    (pellAutomorphX x y) % 2 = x % 2 := by
  unfold pellAutomorphX; omega

theorem pell_automorph_mod2_y (x y : Int) :
    (pellAutomorphY x y) % 2 = y % 2 := by
  unfold pellAutomorphY; omega

/-! ## Cusp vectors and their norms -/

def c1_x : Int := 0
def c1_y : Int := 1
def c2_x : Int := -5
def c2_y : Int := 3

theorem c1_norm : Q_form c1_x c1_y = -5 := by decide
theorem c2_norm : Q_form c2_x c2_y = -20 := by decide
theorem cusp_norms_unequal : Q_form c1_x c1_y ≠ Q_form c2_x c2_y := by decide

/-! ## Bilinear form B(u,v) = 2(u₁v₁ - 5u₂v₂) -/

def bilinearB (u1 u2 v1 v2 : Int) : Int :=
  2 * (u1 * v1 - 5 * u2 * v2)

/-! ## Mc₁ is outside the slab cone (cone indecomposability) -/

def Mc1_x : Int := pellAutomorphX c1_x c1_y  -- = 20
def Mc1_y : Int := pellAutomorphY c1_x c1_y  -- = 9

theorem Mc1_val : (Mc1_x, Mc1_y) = (20, 9) := by
  unfold Mc1_x Mc1_y pellAutomorphX pellAutomorphY c1_x c1_y
  norm_num

theorem Mc1_bilinear_c2 : bilinearB Mc1_x Mc1_y c2_x c2_y = -470 := by
  unfold bilinearB Mc1_x Mc1_y pellAutomorphX pellAutomorphY c1_x c1_y c2_x c2_y
  norm_num

theorem cone_indecomposable : bilinearB Mc1_x Mc1_y c2_x c2_y < 0 := by
  rw [Mc1_bilinear_c2]; norm_num

end Ch10
end QseriesFormalization
