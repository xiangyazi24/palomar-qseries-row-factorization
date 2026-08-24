import QseriesFormalization.Ch10_NormTheta_Defs
import Mathlib.Data.ZMod.Basic

/-!
# Ch10: Shadow Nonvanishing

The shadow G = Θ₄ − Θ₉ + Θ₁₄ − Θ₁₉ is nonzero, witnessed by
shadowCoeff 4 = 1 (since 4 ≡ 4 mod 20, only Θ₄ contributes).

## Main results

* `shadowCoeff_four`: shadowCoeff 4 = 1
* `shadow_nonzero`: ∃ N, shadowCoeff N ≠ 0
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Theta component coefficients

Θ_a(q) = Σ_{n ≡ a mod 20} q^n, so the N-th coefficient is 1 if N ≡ a mod 20, else 0.
-/

def thetaComp (a : Nat) (N : Nat) : Int :=
  if N % 20 = a then 1 else 0

/-! ## Shadow coefficient: G = Θ₄ − Θ₉ + Θ₁₄ − Θ₁₉ -/

def shadowCoeff (N : Nat) : Int :=
  thetaComp 4 N - thetaComp 9 N + thetaComp 14 N - thetaComp 19 N

/-! ## Disjoint support: residues 4, 9, 14, 19 mod 20 are distinct -/

theorem residues_disjoint : ∀ N : Nat,
    (N % 20 = 4 → N % 20 ≠ 9 ∧ N % 20 ≠ 14 ∧ N % 20 ≠ 19) ∧
    (N % 20 = 9 → N % 20 ≠ 4 ∧ N % 20 ≠ 14 ∧ N % 20 ≠ 19) ∧
    (N % 20 = 14 → N % 20 ≠ 4 ∧ N % 20 ≠ 9 ∧ N % 20 ≠ 19) ∧
    (N % 20 = 19 → N % 20 ≠ 4 ∧ N % 20 ≠ 9 ∧ N % 20 ≠ 14) := by
  intro N; omega

/-! ## Concrete witness -/

theorem shadowCoeff_four : shadowCoeff 4 = 1 := by
  unfold shadowCoeff thetaComp; norm_num

theorem shadowCoeff_nine : shadowCoeff 9 = -1 := by
  unfold shadowCoeff thetaComp; norm_num

theorem shadow_nonzero : ∃ N : Nat, shadowCoeff N ≠ 0 :=
  ⟨4, by rw [shadowCoeff_four]; norm_num⟩

/-! ## Shadow coefficients are ±1 or 0 -/

theorem shadowCoeff_values (N : Nat) :
    shadowCoeff N = 0 ∨ shadowCoeff N = 1 ∨ shadowCoeff N = -1 := by
  unfold shadowCoeff thetaComp
  split_ifs <;> omega

end Ch10
end QseriesFormalization
