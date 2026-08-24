import QseriesFormalization.Ch10_NormTheta_Coeff
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Ch10 / Paper 2: the manuscript's `B_N` as an intrinsic cone sum

`Ch10_NormTheta_Defs` defines `BCoeff N = DCoeff N + ACoeff N` as a sum over the
boxes `Finset.range (N+1) ×ˢ Finset.range (2N+2)`.  The manuscript's
`def:B` instead defines

  `B_N = Σ_{(k,r) ∈ 𝒟, E(k,r)=N} (-1)^r - Σ_{(k,r) ∈ 𝒜, E(k,r)=N} (-1)^r`,

a sum over the *actual cones* `𝒜 = {k ≥ 0, r ≥ 0}` and `𝒟 = {k < 0, r < 0}`
with no box anywhere.  This file defines that intrinsic coefficient as a
`finsum` over all of `ℤ × ℤ`, proves its support is finite, and proves it equals
`BCoeff`.  After this the generating function appearing in the sign-kernel
bridge is the manuscript's `B(q)` by a theorem, not by convention.

Reused, not rebuilt: `E`, `Q`, `negOnePowInt`, `InACone`, `InDCone`, `BWeight`,
`ACoeff`, `DCoeff`, `BCoeff` from `Ch10_NormTheta_Defs`, and the four
completeness bounds `A_bound_k`, `A_bound_r`, `D_bound_k`, `D_bound_r` from
`Ch10_NormTheta_Coeff`.  `Mathlib.Algebra.BigOperators.Finprod` is imported for
`finsum` and `finsum_eq_sum_of_support_subset`; it is what makes the definition
box-free.

This says nothing about the relation of this `B` to Chan's original source
object.  The manuscript is explicit that the formal theorem is about the row
model defined there, and that an identification with the older source object
would require a separate source-to-model theorem; none is claimed here.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## The intrinsic coefficient -/

/-- The summand of `def:B`, in the repository's `BWeight` packaging:
`-(-1)^r` on `𝒜`, `+(-1)^r` on `𝒟`, and `0` off both cones. -/
def paper2ConeTerm (N : ℕ) (z : ℤ × ℤ) : ℤ :=
  if E z.1 z.2 = (N : ℤ) then BWeight z.1 z.2 else 0

/-- **The manuscript's `B_N`**, as a sum over all of `ℤ × ℤ` with no bounding
box.  Finiteness of the support is `paper2ConeTerm_support_finite`. -/
noncomputable def paper2ConeCoeff (N : ℕ) : ℤ := ∑ᶠ z : ℤ × ℤ, paper2ConeTerm N z

/-! ## Finite support -/

def paper2AImg (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).image
    fun p : ℕ × ℕ => ((p.1 : ℤ), (p.2 : ℤ))

def paper2DImg (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).image
    fun p : ℕ × ℕ => (-((p.1 : ℤ) + 1), -((p.2 : ℤ) + 1))

def paper2ConeSupportBox (N : ℕ) : Finset (ℤ × ℤ) := paper2AImg N ∪ paper2DImg N

theorem mem_paper2AImg {N : ℕ} {z : ℤ × ℤ} (hA : InACone z.1 z.2)
    (hE : E z.1 z.2 = (N : ℤ)) : z ∈ paper2AImg N := by
  obtain ⟨hk, hr⟩ := hA
  have h1 : z.1 ≤ (N : ℤ) := A_bound_k z.1 z.2 hk hr hE
  have h2 : z.2 ≤ 2 * (N : ℤ) + 1 := A_bound_r z.1 z.2 hk hr hE
  rw [paper2AImg, Finset.mem_image]
  refine ⟨(z.1.toNat, z.2.toNat), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    omega
  · refine Prod.ext ?_ ?_
    · show ((z.1.toNat : ℤ)) = z.1
      omega
    · show ((z.2.toNat : ℤ)) = z.2
      omega

theorem mem_paper2DImg {N : ℕ} {z : ℤ × ℤ} (hD : InDCone z.1 z.2)
    (hE : E z.1 z.2 = (N : ℤ)) : z ∈ paper2DImg N := by
  obtain ⟨hk, hr⟩ := hD
  have h1 : -((N : ℤ) + 1) ≤ z.1 := D_bound_k z.1 z.2 hk hr hE
  have h2 : -(2 * (N : ℤ) + 2) ≤ z.2 := D_bound_r z.1 z.2 hk hr hE
  rw [paper2DImg, Finset.mem_image]
  refine ⟨((-z.1 - 1).toNat, (-z.2 - 1).toNat), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    omega
  · refine Prod.ext ?_ ?_
    · show -(((-z.1 - 1).toNat : ℤ) + 1) = z.1
      omega
    · show -(((-z.2 - 1).toNat : ℤ) + 1) = z.2
      omega

theorem paper2ConeTerm_support_subset (N : ℕ) :
    Function.support (paper2ConeTerm N) ⊆ ↑(paper2ConeSupportBox N) := by
  intro z hz
  rw [Function.mem_support, paper2ConeTerm] at hz
  have hE : E z.1 z.2 = (N : ℤ) := by
    by_contra hc
    rw [if_neg hc] at hz
    exact hz rfl
  rw [if_pos hE, BWeight] at hz
  rw [paper2ConeSupportBox, Finset.coe_union, Set.mem_union]
  split_ifs at hz with h1 h2
  · exact Or.inl (mem_paper2AImg h1 hE)
  · exact Or.inr (mem_paper2DImg h2 hE)
  · exact absurd rfl hz

theorem paper2ConeTerm_support_finite (N : ℕ) :
    (Function.support (paper2ConeTerm N)).Finite :=
  Set.Finite.subset (paper2ConeSupportBox N).finite_toSet (paper2ConeTerm_support_subset N)

/-- The readable containment asked for by the objective: the support of the
`def:B` summand lies in `[-(N+1), N] × [-(2N+2), 2N+1]`. -/
theorem paper2ConeTerm_support_subset_Icc (N : ℕ) :
    Function.support (paper2ConeTerm N)
      ⊆ ↑(Finset.Icc (-((N : ℤ) + 1)) (N : ℤ) ×ˢ
            Finset.Icc (-(2 * (N : ℤ) + 2)) (2 * (N : ℤ) + 1)) := by
  refine subset_trans (paper2ConeTerm_support_subset N) ?_
  intro z hz
  rw [Finset.mem_coe, paper2ConeSupportBox, Finset.mem_union] at hz
  rw [Finset.mem_coe]
  rcases hz with h | h
  · rw [paper2AImg, Finset.mem_image] at h
    obtain ⟨p, hp, rfl⟩ := h
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  · rw [paper2DImg, Finset.mem_image] at h
    obtain ⟨p, hp, rfl⟩ := h
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega

theorem paper2ConeCoeff_eq_sum (N : ℕ) :
    paper2ConeCoeff N = ∑ z ∈ paper2ConeSupportBox N, paper2ConeTerm N z :=
  finsum_eq_sum_of_support_subset _ (paper2ConeTerm_support_subset N)

/-! ## The identification with `BCoeff` -/

theorem paper2AImg_disjoint_paper2DImg (N : ℕ) :
    Disjoint (paper2AImg N) (paper2DImg N) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [paper2AImg, Finset.mem_image] at hz
  rw [paper2DImg, Finset.mem_image] at hz'
  obtain ⟨x, _, hx⟩ := hz
  obtain ⟨y, _, hy⟩ := hz'
  have h1 : ((x.1 : ℤ)) = -((y.1 : ℤ) + 1) := congrArg Prod.fst (hx.trans hy.symm)
  omega

theorem paper2ConeTerm_AImg_sum (N : ℕ) :
    ∑ z ∈ paper2AImg N, paper2ConeTerm N z = ACoeff N := by
  rw [paper2AImg, Finset.sum_image]
  · rw [ACoeff, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hA : InACone ((p.1 : ℤ)) ((p.2 : ℤ)) :=
      ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
    simp only [paper2ConeTerm, BWeight]
    rw [if_pos hA]
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (by omega) (by omega)

theorem paper2ConeTerm_DImg_sum (N : ℕ) :
    ∑ z ∈ paper2DImg N, paper2ConeTerm N z = DCoeff N := by
  rw [paper2DImg, Finset.sum_image]
  · rw [DCoeff, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hnA : ¬ InACone (-((p.1 : ℤ) + 1)) (-((p.2 : ℤ) + 1)) := by
      rw [InACone]
      omega
    have hD : InDCone (-((p.1 : ℤ) + 1)) (-((p.2 : ℤ) + 1)) := by
      rw [InDCone]
      omega
    simp only [paper2ConeTerm, BWeight]
    rw [if_neg hnA, if_pos hD]
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (by omega) (by omega)

/-- **The manuscript's `B_N` is the repository's `BCoeff N`.** -/
theorem paper2ConeCoeff_eq_BCoeff (N : ℕ) : paper2ConeCoeff N = BCoeff N := by
  rw [paper2ConeCoeff_eq_sum, paper2ConeSupportBox,
    Finset.sum_union (paper2AImg_disjoint_paper2DImg N),
    paper2ConeTerm_AImg_sum, paper2ConeTerm_DImg_sum, BCoeff]
  ring

/-- Numeric spot-checks, inherited from the repository's kernel-verified
`B_coeff_*` lemmas through the identification. -/
theorem paper2ConeCoeff_zero : paper2ConeCoeff 0 = -1 := by
  rw [paper2ConeCoeff_eq_BCoeff]
  exact B_coeff_0

theorem paper2ConeCoeff_four : paper2ConeCoeff 4 = -1 := by
  rw [paper2ConeCoeff_eq_BCoeff]
  exact B_coeff_4

theorem paper2ConeCoeff_thirtyFour : paper2ConeCoeff 34 = 3 := by
  rw [paper2ConeCoeff_eq_BCoeff]
  exact B_coeff_34

/-! ## The literal `def:B` shape

`paper2ConeCoeff` packages the two cone sums through `BWeight`.  These two
lemmas show it really is the difference of the two sums as the manuscript
writes them, so no reading step is left between `def:B` and the Lean object. -/

noncomputable def paper2AConeSum (N : ℕ) : ℤ :=
  ∑ᶠ z : ℤ × ℤ, (if InACone z.1 z.2 ∧ E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0)

noncomputable def paper2DConeSum (N : ℕ) : ℤ :=
  ∑ᶠ z : ℤ × ℤ, (if InDCone z.1 z.2 ∧ E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0)

theorem paper2AConeSum_eq (N : ℕ) :
    paper2AConeSum N
      = ∑ z ∈ paper2AImg N, (if E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0) := by
  have hsupp : Function.support (fun z : ℤ × ℤ =>
      if InACone z.1 z.2 ∧ E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0)
      ⊆ ↑(paper2AImg N) := by
    intro z hz
    rw [Function.mem_support] at hz
    by_cases h : InACone z.1 z.2 ∧ E z.1 z.2 = (N : ℤ)
    · exact mem_paper2AImg h.1 h.2
    · exact absurd (if_neg h) hz
  rw [paper2AConeSum, finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hA : InACone z.1 z.2 := by
    rw [paper2AImg, Finset.mem_image] at hz
    obtain ⟨p, _, rfl⟩ := hz
    exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
  by_cases h : E z.1 z.2 = (N : ℤ)
  · rw [if_pos ⟨hA, h⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.2), if_neg h]

theorem paper2DConeSum_eq (N : ℕ) :
    paper2DConeSum N
      = ∑ z ∈ paper2DImg N, (if E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0) := by
  have hsupp : Function.support (fun z : ℤ × ℤ =>
      if InDCone z.1 z.2 ∧ E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0)
      ⊆ ↑(paper2DImg N) := by
    intro z hz
    rw [Function.mem_support] at hz
    by_cases h : InDCone z.1 z.2 ∧ E z.1 z.2 = (N : ℤ)
    · exact mem_paper2DImg h.1 h.2
    · exact absurd (if_neg h) hz
  rw [paper2DConeSum, finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hD : InDCone z.1 z.2 := by
    rw [paper2DImg, Finset.mem_image] at hz
    obtain ⟨p, _, rfl⟩ := hz
    exact ⟨by simp only []; omega, by simp only []; omega⟩
  by_cases h : E z.1 z.2 = (N : ℤ)
  · rw [if_pos ⟨hD, h⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.2), if_neg h]

/-- **`paper2ConeCoeff` is literally `def:B`**: the `𝒟` sum minus the `𝒜` sum
of `(-1)^r`, each taken over the cone with no bounding box. -/
theorem paper2ConeCoeff_eq_DConeSum_sub_AConeSum (N : ℕ) :
    paper2ConeCoeff N = paper2DConeSum N - paper2AConeSum N := by
  have hA : ∑ z ∈ paper2AImg N, paper2ConeTerm N z
      = -∑ z ∈ paper2AImg N, (if E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hAc : InACone z.1 z.2 := by
      rw [paper2AImg, Finset.mem_image] at hz
      obtain ⟨p, _, rfl⟩ := hz
      exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _⟩
    rw [paper2ConeTerm, BWeight, if_pos hAc]
    split_ifs <;> ring
  have hD : ∑ z ∈ paper2DImg N, paper2ConeTerm N z
      = ∑ z ∈ paper2DImg N, (if E z.1 z.2 = (N : ℤ) then negOnePowInt z.2 else 0) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hDc : InDCone z.1 z.2 := by
      rw [paper2DImg, Finset.mem_image] at hz
      obtain ⟨p, _, rfl⟩ := hz
      exact ⟨by simp only []; omega, by simp only []; omega⟩
    have hnA : ¬ InACone z.1 z.2 := by
      obtain ⟨h1, h2⟩ := hDc
      rw [InACone]
      omega
    rw [paper2ConeTerm, BWeight, if_neg hnA, if_pos hDc]
  rw [paper2ConeCoeff_eq_sum, paper2ConeSupportBox,
    Finset.sum_union (paper2AImg_disjoint_paper2DImg N), hA, hD,
    paper2AConeSum_eq, paper2DConeSum_eq]
  ring

end Ch10
end QseriesFormalization
