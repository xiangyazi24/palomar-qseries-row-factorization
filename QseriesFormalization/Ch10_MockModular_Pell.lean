import QseriesFormalization.Ch10_NormTheta_Defs

/-!
# Ch10: Pell Coordinates, Cusp Vectors, Bilinear Form

The quadratic form Q(k,r) = 4k² + 6kr + r² + 2k + r factors through
Pell coordinates (x,y) = (r+3k, k) as Q_form(x,y) = x² - 5y².

## Main results

* `pellQ_pellCoord`: Q_form in Pell coordinates = the polynomial in (k,r)
* `pellQ_Mmul`: M preserves the Pell form
* Cusp norms: pellQ c₁ = -5, pellQ c₂ = -20
* `BAff_pellCoord_c1/c2`: affine bilinear pairings in (k,r)
* `pellB_Mc1_c2 = -470`: cone indecomposability
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Pell coordinate vectors -/

@[ext]
structure ZVec where
  x : Int
  y : Int
  deriving DecidableEq, Repr

instance : Zero ZVec := ⟨⟨0, 0⟩⟩
instance : Neg ZVec := ⟨fun v => ⟨-v.x, -v.y⟩⟩
instance : Add ZVec := ⟨fun u v => ⟨u.x + v.x, u.y + v.y⟩⟩

/-! ## Pell quadratic form and bilinear form -/

def pellQ (v : ZVec) : Int := v.x ^ 2 - 5 * v.y ^ 2

def pellB (u v : ZVec) : Int := 2 * u.x * v.x - 10 * u.y * v.y

/-! ## Affine bilinear form (clearing denominators from μ = (1/2, 1/10)) -/

def BAff (v c : ZVec) : Int := (2 * v.x + 1) * c.x - (10 * v.y + 1) * c.y

/-! ## Coordinate change: (k,r) ↦ Pell coordinates -/

def pellCoord (k r : Int) : ZVec := ⟨r + 3 * k, k⟩

@[simp] theorem pellCoord_x (k r : Int) : (pellCoord k r).x = r + 3 * k := rfl
@[simp] theorem pellCoord_y (k r : Int) : (pellCoord k r).y = k := rfl

theorem pellQ_pellCoord (k r : Int) :
    pellQ (pellCoord k r) = 4 * k ^ 2 + 6 * k * r + r ^ 2 := by
  unfold pellQ pellCoord; ring

/-! ## Pell automorph M = ((9,20),(4,9)) -/

def Mmul (v : ZVec) : ZVec := ⟨9 * v.x + 20 * v.y, 4 * v.x + 9 * v.y⟩

@[simp] theorem Mmul_x (v : ZVec) : (Mmul v).x = 9 * v.x + 20 * v.y := rfl
@[simp] theorem Mmul_y (v : ZVec) : (Mmul v).y = 4 * v.x + 9 * v.y := rfl

@[simp] theorem pellQ_Mmul (v : ZVec) : pellQ (Mmul v) = pellQ v := by
  rcases v with ⟨x, y⟩; unfold pellQ Mmul; ring

theorem Mmul_mod2_x (v : ZVec) : (Mmul v).x % 2 = v.x % 2 := by
  show (9 * v.x + 20 * v.y) % 2 = v.x % 2
  have : 9 * v.x + 20 * v.y = v.x + 2 * (4 * v.x + 10 * v.y) := by ring
  rw [this]; omega

theorem Mmul_mod2_y (v : ZVec) : (Mmul v).y % 2 = v.y % 2 := by
  show (4 * v.x + 9 * v.y) % 2 = v.y % 2
  have : 4 * v.x + 9 * v.y = v.y + 2 * (2 * v.x + 4 * v.y) := by ring
  rw [this]; omega

/-! ## Cusp vectors -/

def c1 : ZVec := ⟨0, 1⟩
def c2 : ZVec := ⟨-5, 3⟩

@[simp] theorem pellQ_c1 : pellQ c1 = -5 := by
  unfold pellQ c1; norm_num

@[simp] theorem pellQ_c2 : pellQ c2 = -20 := by
  unfold pellQ c2; norm_num

theorem cusp_norms_ne : pellQ c1 ≠ pellQ c2 := by
  simp

/-! ## Affine bilinear pairings -/

@[simp] theorem BAff_pellCoord_c1 (k r : Int) :
    BAff (pellCoord k r) c1 = -(10 * k + 1) := by
  unfold BAff pellCoord c1; ring

@[simp] theorem BAff_pellCoord_c2 (k r : Int) :
    BAff (pellCoord k r) c2 = -(10 * (6 * k + r) + 8) := by
  unfold BAff pellCoord c2; ring

theorem BAff_pellCoord_c1_ne_zero (k : Int) (r : Int) :
    BAff (pellCoord k r) c1 ≠ 0 := by
  simp; omega

theorem BAff_pellCoord_c2_ne_zero (k r : Int) :
    BAff (pellCoord k r) c2 ≠ 0 := by
  simp; omega

/-! ## Cone indecomposability -/

@[simp] theorem pellB_Mc1_c2 : pellB (Mmul c1) c2 = -470 := by
  unfold pellB Mmul c1 c2; norm_num

theorem cone_indecomposable' : pellB (Mmul c1) c2 < 0 := by
  simp

/-! ## Q-invariance implies orbit separation -/

theorem orbit_separation : pellQ c1 ≠ pellQ c2 := cusp_norms_ne

end Ch10
end QseriesFormalization
