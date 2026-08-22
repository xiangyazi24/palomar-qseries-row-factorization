import QseriesFormalization.Ch10_NormTheta_Algebra

/-!
# Ch10: Coefficient Formula (Theorem 5)

B_N = Σ BWeight(k,r) over all (k,r) with E(k,r) = N.
Formalized as BCoeff = ACoeff + DCoeff, with completeness lemmas showing
the bounding boxes capture all solutions.

## Strategy (dual-oracle R3)
- Nat-parametrize each cone: A-cone ≅ ℕ², D-cone via (m,s) ↦ (-(m+1),-(s+1))
- Crude bounds via Q = 2N (division-free): k ≤ N, r ≤ 2N+1
- Completeness: if in cone and E = N, then in box
- Sanity check: decide specific coefficients
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Completeness: A-cone bounds

If k ≥ 0, r ≥ 0, and E(k,r) = N, then k ≤ N and r ≤ 2N+1.
Proved via Q = 2N (no triZ division).
-/

theorem A_bound_k (k r : Int) (hk : 0 ≤ k) (hr : 0 ≤ r) (hE : E k r = ↑N) :
    k ≤ ↑N := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  nlinarith [sq_nonneg r, mul_nonneg hk hr]

theorem A_bound_r (k r : Int) (hk : 0 ≤ k) (hr : 0 ≤ r) (hE : E k r = ↑N) :
    r ≤ 2 * ↑N + 1 := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  nlinarith [sq_nonneg k, mul_nonneg hk hr]

/-! ## Completeness: D-cone bounds

If k < 0, r < 0, and E(k,r) = N, then -(N+1) ≤ k and -(2N+2) ≤ r.
Equivalently, writing k = -(m+1), r = -(s+1): m ≤ N and s ≤ 2N+1.
-/

theorem D_bound_k (k r : Int) (hk : k < 0) (hr : r < 0) (hE : E k r = ↑N) :
    -(↑N + 1) ≤ k := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  have hkr : 0 ≤ (-k - 1) * (-r - 1) := mul_nonneg (by omega) (by omega)
  nlinarith [sq_nonneg r, sq_nonneg (k + r)]

theorem D_bound_r (k r : Int) (hk : k < 0) (hr : r < 0) (hE : E k r = ↑N) :
    -(2 * ↑N + 2) ≤ r := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  have hkr : 0 ≤ (-k - 1) * (-r - 1) := mul_nonneg (by omega) (by omega)
  nlinarith [sq_nonneg k, sq_nonneg (k + r)]

/-! ## Sanity check: kernel-verified small coefficients -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_0 : BCoeff 0 = -1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_1 : BCoeff 1 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_2 : BCoeff 2 = 0 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_3 : BCoeff 3 = -2 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_4 : BCoeff 4 = -1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_5 : BCoeff 5 = 0 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_6 : BCoeff 6 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_7 : BCoeff 7 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_8 : BCoeff 8 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_9 : BCoeff 9 = 0 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
theorem B_coeff_10 : BCoeff 10 = -2 := by decide

/-! ## Large coefficient: kernel-checked evaluation -/

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 4000 in
theorem B_coeff_34 : BCoeff 34 = 3 := by decide

/-- The coefficient sequence fails multiplicativity on the norm variables
`11`, `31`, and `341 = 11 * 31`. -/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  rw [B_coeff_34, B_coeff_1, B_coeff_3]
  norm_num

/-! ## Norm support (Theorem C)

If ACoeff N ≠ 0, there exists β ∈ L with N(β) = -(10N+1).
Proof: sum ≠ 0 ⟹ filtered finset nonempty ⟹ ∃ (k,r) with E=N ⟹ beta(k,r) witnesses.
-/

theorem ACoeff_ne_zero_norm_support (N : Nat) (h : ACoeff N ≠ 0) :
    ∃ x : PhiInt, InL x ∧ PhiInt.norm x = -(10 * ↑N + 1) := by
  unfold ACoeff at h
  -- The filtered finset must be nonempty (otherwise sum = 0)
  set S := (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N) with hS_def
  obtain ⟨⟨k, r⟩, hmem⟩ : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp only [hemp, Finset.sum_empty] at h
    exact h rfl
  simp only [hS_def, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
  exact ⟨beta (↑k) (↑r), beta_mem_L _ _, by have := norm_beta (↑k) (↑r); omega⟩

theorem DCoeff_ne_zero_norm_support (N : Nat) (h : DCoeff N ≠ 0) :
    ∃ x : PhiInt, InL x ∧ PhiInt.norm x = -(10 * ↑N + 1) := by
  unfold DCoeff at h
  set S := (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N) with hS_def
  obtain ⟨⟨m, s⟩, hmem⟩ : S.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp only [hemp, Finset.sum_empty] at h
    exact h rfl
  simp only [hS_def, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
  exact ⟨beta (-(↑m + 1)) (-(↑s + 1)), beta_mem_L _ _,
    by have := norm_beta (-(↑m + 1)) (-(↑s + 1)); omega⟩

/-! ## Combined norm support (Theorem C)

B_N ≠ 0 ⟹ 10N+1 is a norm from Z[φ].
-/

theorem BCoeff_ne_zero_norm_support (N : Nat) (h : BCoeff N ≠ 0) :
    ∃ x : PhiInt, InL x ∧ PhiInt.norm x = -(10 * ↑N + 1) := by
  unfold BCoeff at h
  by_cases hD : DCoeff N = 0
  · have hA : ACoeff N ≠ 0 := by omega
    exact ACoeff_ne_zero_norm_support N hA
  · exact DCoeff_ne_zero_norm_support N hD

end Ch10
end QseriesFormalization
