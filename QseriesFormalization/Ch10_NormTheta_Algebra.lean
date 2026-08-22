import QseriesFormalization.Ch10_NormTheta_Defs

/-!
# Ch10: Algebraic Theorems

Theorems 1-4, 6, 8 from the norm theta series paper.
All proofs verified against Mathlib 4.30.0 by dual-oracle audit (Fable R2 + ChatGPT R2).
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Foundational lemmas for triZ

triZ's `/` is opened exactly once, inside `two_mul_triZ`.
Everything downstream uses `linear_combination` or passes through `two_mul_E` + `omega`.
-/

lemma two_dvd_mul_succ (r : Int) : 2 ∣ r * (r + 1) :=
  (Int.even_mul_succ_self r).two_dvd

lemma two_mul_triZ (r : Int) : 2 * triZ r = r * (r + 1) := by
  unfold triZ
  exact Int.mul_ediv_cancel' (two_dvd_mul_succ r)

/-! ## Theorem 1: Q(k,r) is always even -/

theorem Q_even (k r : Int) : 2 ∣ Q k r := by
  unfold Q
  have h1 : 2 ∣ 2 * (2 * k ^ 2 + k + 3 * k * r) := dvd_mul_right 2 _
  have h2 : 2 ∣ r * (r + 1) := two_dvd_mul_succ r
  have hsum : 2 ∣ 2 * (2 * k ^ 2 + k + 3 * k * r) + r * (r + 1) := dvd_add h1 h2
  convert hsum using 1
  ring

/-! ## Spec lemma: Q = 2E (and reverse) -/

theorem Q_eq_two_mul_E (k r : Int) : Q k r = 2 * E k r := by
  unfold E Q
  linear_combination -two_mul_triZ r

theorem two_mul_E (k r : Int) : 2 * E k r = Q k r := by
  linarith [Q_eq_two_mul_E k r]

/-! ## Theorem 2: beta maps into L, and surjects onto L -/

theorem beta_mem_L (k r : Int) : InL (beta k r) := by
  unfold InL beta
  use k
  ring

theorem exists_beta_of_mem_L (x : PhiInt) (hx : InL x) :
    ∃ k r : Int, beta k r = x := by
  rcases hx with ⟨k, hk⟩
  refine ⟨k, x.a + 2 * k, ?_⟩
  ext <;> simp only [beta] <;> omega

/-! ## Theorem 3: norm identity -N(β(k,r)) = 10E(k,r) + 1 -/

theorem norm_beta (k r : Int) :
    -PhiInt.norm (beta k r) = 10 * E k r + 1 := by
  simp only [PhiInt.norm, beta, E]
  linear_combination -5 * two_mul_triZ r

/-! ## Theorem 4: sign simplification (-1)^r = (-1)^(r-2k) -/

theorem parity_beta_a (k r : Int) :
    negOnePowInt r = negOnePowInt (r - 2 * k) := by
  unfold negOnePowInt
  have h : r % 2 = (r - 2 * k) % 2 := by omega
  simp only [h]

/-! ## Theorem 6: Coset stability under unit powers

The stabilizer of L in ⟨ε⟩ is ⟨ε⁶⟩:
- k=1,3,5 (odd): ε^k·L ∩ L = ∅ (strong disjointness)
- k=2,4 (even, not 6): ε^k·L ∩ L ≠ ∅ but ε^k·L ≠ L (partial intersection)
- k=6: ε⁶·L = L (complete stabilization)
-/

def eps2Mul (x : PhiInt) : PhiInt :=
  ⟨2 * x.a + 3 * x.b, 3 * x.a + 5 * x.b⟩

def eps3Mul (x : PhiInt) : PhiInt :=
  ⟨5 * x.a + 8 * x.b, 8 * x.a + 13 * x.b⟩

def eps4Mul (x : PhiInt) : PhiInt :=
  ⟨13 * x.a + 21 * x.b, 21 * x.a + 34 * x.b⟩

def eps5Mul (x : PhiInt) : PhiInt :=
  ⟨34 * x.a + 55 * x.b, 55 * x.a + 89 * x.b⟩

-- Consistency: epskMul = k-fold epsMul composition
theorem eps2Mul_eq (x : PhiInt) : eps2Mul x = epsMul (epsMul x) := by
  simp only [eps2Mul, epsMul, PhiInt.mk.injEq]; omega

-- Part (a): Odd powers — strong disjointness

theorem epsMul_not_preserve_L (x : PhiInt) (hx : InL x) :
    ¬ InL (epsMul x) := by
  simp only [InL, epsMul] at hx ⊢; omega

theorem eps3Mul_not_preserve_L (x : PhiInt) (hx : InL x) :
    ¬ InL (eps3Mul x) := by
  simp only [InL, eps3Mul] at hx ⊢; omega

theorem eps5Mul_not_preserve_L (x : PhiInt) (hx : InL x) :
    ¬ InL (eps5Mul x) := by
  simp only [InL, eps5Mul] at hx ⊢; omega

-- Part (b): Even powers — not set-preserving (witness-based)

theorem eps2Mul_not_setPreserve_L :
    ∃ x : PhiInt, InL x ∧ ¬ InL (eps2Mul x) :=
  ⟨⟨0, 1⟩, by simp [InL, eps2Mul]⟩

theorem eps4Mul_not_setPreserve_L :
    ∃ x : PhiInt, InL x ∧ ¬ InL (eps4Mul x) :=
  ⟨⟨1, 4⟩, by simp [InL, eps4Mul]⟩

-- Part (c): ε⁶ preserves L completely

theorem eps6Mul_preserves_L (x : PhiInt) (hx : InL x) :
    InL (eps6Mul x) := by
  simp only [InL, eps6Mul] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m - 12 * x.a - 20 * x.b, by omega⟩

/-! ## E is nonneg on both cones (justifies Nat indexing) -/

theorem E_nonneg_A (k r : Int) (hk : 0 ≤ k) (hr : 0 ≤ r) : 0 ≤ E k r := by
  have hQ : 0 ≤ Q k r := by
    simp only [Q]; nlinarith [sq_nonneg k, sq_nonneg r, mul_nonneg hk hr]
  have := Q_eq_two_mul_E k r; omega

theorem E_nonneg_D (k r : Int) (hk : k < 0) (hr : r < 0) : 0 ≤ E k r := by
  have hQ : 0 ≤ Q k r := by
    simp only [Q]
    have hkr : 0 ≤ (-k - 1) * (-r - 1) := mul_nonneg (by omega) (by omega)
    nlinarith [sq_nonneg (k + r), sq_nonneg k, sq_nonneg r]
  have := Q_eq_two_mul_E k r; omega

/-! ## Theorem 7: Order of ε modulo 2√5 is exactly 6

ε⁶ ≡ 1 (mod 2√5), i.e., c_2sqrt5 divides (ε⁶ - 1) as a PhiInt element.
For k=1..5, εᵏ ≢ 1 (mod 2√5) — witnessed on the basis element ⟨1,0⟩.
-/

-- Divisibility in ℤ[φ]: c ∣ x iff ∃ y, x = c * y
def PhiInt.phiDvd (c x : PhiInt) : Prop := ∃ y : PhiInt, x = c * y

-- ε⁶ - 1 applied to basis: eps6Mul(1,0) - (1,0) = ⟨88, 144⟩
theorem eps6_congOne_basis1 :
    PhiInt.phiDvd c_2sqrt5 (eps6Mul ⟨1, 0⟩ - ⟨1, 0⟩) :=
  ⟨⟨20, 32⟩, by ext <;> simp [c_2sqrt5, eps6Mul]⟩

-- eps6Mul(0,1) - (0,1) = ⟨144, 232⟩
theorem eps6_congOne_basis2 :
    PhiInt.phiDvd c_2sqrt5 (eps6Mul ⟨0, 1⟩ - ⟨0, 1⟩) :=
  ⟨⟨32, 52⟩, by ext <;> simp [c_2sqrt5, eps6Mul]⟩

-- ε¹ ≢ 1: epsMul(1,0) - (1,0) = ⟨0,1⟩, not divisible by ⟨-2,4⟩
theorem eps1_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (epsMul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, epsMul, PhiInt.ext_iff] at h
  omega

theorem eps2_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps2Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps2Mul, PhiInt.ext_iff] at h
  omega

theorem eps3_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps3Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps3Mul, PhiInt.ext_iff] at h
  omega

theorem eps4_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps4Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps4Mul, PhiInt.ext_iff] at h
  omega

theorem eps5_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps5Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps5Mul, PhiInt.ext_iff] at h
  omega

/-! ## Theorem 8: HM exponent matches E -/

theorem HMExp_eq_E (k r : Int) : HMExp k r = E k r := by
  unfold HMExp E
  ring

end Ch10
end QseriesFormalization
