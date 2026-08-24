import QseriesFormalization.Ch10_Paper2_CompletedTheta
import QseriesFormalization.Ch10_MockModular_Certificate
import QseriesFormalization.Ch10_Paper2_ConeCoeff

/-!
# Ch10 / Paper 2: the sign-kernel bridge

The sign half of Zwegers' Definition 2.1 summand, isolated in
`Ch10_Paper2_CompletedTheta`, is here identified with `q^{1/10} B(q)`, where
`B` is the generating function of the repository's existing combinatorial
coefficients `BCoeff`.

Everything combinatorial is reused, not rebuilt: `E`, `Q`, `triZ`,
`negOnePowInt`, `ACoeff`, `DCoeff`, `BCoeff` from `Ch10_NormTheta_Defs`;
`two_mul_E` from `Ch10_NormTheta_Algebra`; `sigma` and its invariance lemmas
from `Ch10_MockModular_Sigma`; `BAff`, `pellCoord`, `c1`, `c2` from
`Ch10_MockModular_Pell`; `sgnZ`, `slabInd`, `two_mul_slabInd_eq_sign_diff`
from `Ch10_MockModular_SlabIndicator`; `slabWeight` from
`Ch10_MockModular_Certificate`.

The two imports are exactly the two things needed: the analytic file for the
sign series, and the certificate file for the combinatorial layer (which pulls
in the rest of that layer transitively).

No modular transformation law is proved here, and Zwegers' completion theorem
is not formalized anywhere in this repository.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## The generating function of `BCoeff` -/

/-- `B(q) = Σ_N B_N q^N`.  The coefficients are the repository's `BCoeff`;
`paper2BSeries_eq_coneSeries` below shows they are the manuscript's `def:B`
cone coefficients, so this is the manuscript's `B(q)`. -/
noncomputable def paper2BSeries (q : ℂ) : ℂ := ∑' N : ℕ, (BCoeff N : ℂ) * q ^ N

theorem abs_negOnePowInt (n : ℤ) : |negOnePowInt n| = 1 := by
  unfold negOnePowInt
  split_ifs <;> norm_num

theorem abs_ACoeff_le (N : ℕ) : |ACoeff N| ≤ 2 * ((N : ℤ) + 1) ^ 2 := by
  have hcard : ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
      (fun p : ℕ × ℕ => E (↑p.1) (↑p.2) = (N : ℤ))).card ≤ (N + 1) * (2 * N + 2) := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hone : ∀ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
      (fun p : ℕ × ℕ => E (↑p.1) (↑p.2) = (N : ℤ)),
      |(-negOnePowInt (↑p.2 : ℤ))| = 1 := by
    intro p _
    rw [abs_neg, abs_negOnePowInt]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine le_trans (Int.ofNat_le.2 hcard) (le_of_eq ?_)
  push_cast
  ring

theorem abs_DCoeff_le (N : ℕ) : |DCoeff N| ≤ 2 * ((N : ℤ) + 1) ^ 2 := by
  have hcard : ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
      (fun p : ℕ × ℕ => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = (N : ℤ))).card
        ≤ (N + 1) * (2 * N + 2) := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Finset.card_product, Finset.card_range, Finset.card_range]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hone : ∀ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
      (fun p : ℕ × ℕ => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = (N : ℤ)),
      |negOnePowInt (-((↑p.2 : ℤ) + 1))| = 1 := fun p _ => abs_negOnePowInt _
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine le_trans (Int.ofNat_le.2 hcard) (le_of_eq ?_)
  push_cast
  ring

/-- `|B_N| ≤ 4(N+1)²`: a signed sum of `±1` over a filtered box. -/
theorem abs_BCoeff_le (N : ℕ) : |BCoeff N| ≤ 4 * ((N : ℤ) + 1) ^ 2 := by
  have hA := abs_ACoeff_le N
  have hD := abs_DCoeff_le N
  have h1 := abs_le.1 hA
  have h2 := abs_le.1 hD
  rw [BCoeff, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem summable_BCoeff_mul_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun N : ℕ => (BCoeff N : ℂ) * q ^ N) := by
  have hr : ‖(‖q‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)]
    exact hq
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr
  have hmaj : Summable (fun N : ℕ => 4 * ((N : ℝ) + 1) ^ 2 * ‖q‖ ^ N) := by
    refine ((h2.mul_left 4).add ((h1.mul_left 8).add (h0.mul_left 4))).congr fun N => ?_
    ring
  refine hmaj.of_norm_bounded fun N => ?_
  rw [norm_mul, norm_pow, Complex.norm_intCast]
  have hb : |(BCoeff N : ℤ)| ≤ 4 * ((N : ℤ) + 1) ^ 2 := abs_BCoeff_le N
  have hb' : |((BCoeff N : ℤ) : ℝ)| ≤ 4 * ((N : ℝ) + 1) ^ 2 := by
    rw [← Int.cast_abs]
    exact_mod_cast hb
  have hq0 : (0 : ℝ) ≤ ‖q‖ ^ N := by positivity
  calc |((BCoeff N : ℤ) : ℝ)| * ‖q‖ ^ N ≤ 4 * ((N : ℝ) + 1) ^ 2 * ‖q‖ ^ N :=
        mul_le_mul_of_nonneg_right hb' hq0
    _ = 4 * ((N : ℝ) + 1) ^ 2 * ‖q‖ ^ N := rfl

/-! ## The coordinate change `(x,y) ↦ (k,r) = (y, x-3y)` -/

/-- The reindexing of the lattice by Pell coordinates: `x = r+3k`, `y = k`. -/
def paper2KR : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.2, p.1 - 3 * p.2)
  invFun z := (z.2 + 3 * z.1, z.1)
  left_inv p := by simp
  right_inv z := by simp

/-- `Q₀(v) = E(k,r) + 1/10` in Pell coordinates. -/
theorem paper2Q0_kr (k r : ℤ) :
    paper2Q0 (((r + 3 * k : ℤ) : ℝ) + 1 / 2) (((k : ℤ) : ℝ) + 1 / 10)
      = ((E k r : ℤ) : ℝ) + 1 / 10 := by
  have h : ((4 * k ^ 2 + 2 * k + r ^ 2 + (6 * k + 1) * r : ℤ) : ℝ) = 2 * ((E k r : ℤ) : ℝ) := by
    have hQ := Q_eq_two_mul_E k r
    unfold Q at hQ
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hQ
  rw [paper2Q0]
  push_cast at h ⊢
  linarith

/-- `e^{πi m} = (-1)^m` for integer `m`, in the repository's `negOnePowInt`
form. -/
theorem paper2_exp_pi_I_int (r : ℤ) :
    Complex.exp (Real.pi * Complex.I * (r : ℂ)) = ((negOnePowInt r : ℤ) : ℂ) := by
  rcases Int.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
  · have h1 : negOnePowInt r = 1 := negOnePowInt_even (by omega)
    rw [h1, ht]
    push_cast
    rw [show (Real.pi : ℂ) * Complex.I * ((t : ℂ) + (t : ℂ))
        = (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  · have h1 : negOnePowInt r = -1 := negOnePowInt_odd (by omega)
    rw [h1, ht]
    push_cast
    rw [show (Real.pi : ℂ) * Complex.I * (2 * (t : ℂ) + 1)
        = ((t : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I by
      ring]
    rw [Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, one_mul,
      Complex.exp_pi_mul_I]

theorem negOnePowInt_add_four_mul (k r : ℤ) : negOnePowInt (r + 4 * k) = negOnePowInt r := by
  unfold negOnePowInt
  split_ifs <;> omega

/-- The character phase in Pell coordinates: the `e^{3πi/5}` cancels the
manuscript's normalization and leaves `(-1)^r`. -/
theorem paper2CharPhase_kr (k r : ℤ) :
    paper2CharPhase (r + 3 * k, k)
      = Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5) * ((negOnePowInt r : ℤ) : ℂ) := by
  have hB : paper2B0 (((r + 3 * k : ℤ) : ℝ) + 1 / 2) (((k : ℤ) : ℝ) + 1 / 10) (1 / 2)
      (-(1 / 10)) = (((r + 4 * k : ℤ) : ℝ)) / 2 + 3 / 10 := by
    rw [paper2B0]
    push_cast
    ring
  simp only [paper2CharPhase]
  rw [hB]
  rw [show (2 * (Real.pi : ℂ) * Complex.I *
        ((((r + 4 * k : ℤ) : ℝ) / 2 + 3 / 10 : ℝ) : ℂ))
      = (Real.pi : ℂ) * Complex.I * ((r + 4 * k : ℤ) : ℂ) + 3 * (Real.pi : ℂ) * Complex.I / 5 by
    push_cast
    ring]
  rw [Complex.exp_add, paper2_exp_pi_I_int, negOnePowInt_add_four_mul]
  ring

/-- The sign difference in Pell coordinates is `-2·slabInd`, matching the
repository's `two_mul_slabInd_eq_sign_diff` with the opposite orientation. -/
theorem paper2SignDiff_kr (k r : ℤ) :
    paper2SignDiff (r + 3 * k, k) = -2 * ((slabInd k r : ℤ) : ℝ) := by
  have hs : ∀ n : ℤ, n ≠ 0 → Real.sign ((n : ℝ) / 2) = ((sgnZ n : ℤ) : ℝ) := by
    intro n hn
    rcases lt_or_gt_of_ne hn with h | h
    · rw [Real.sign_of_neg (by
        have : ((n : ℤ) : ℝ) < 0 := by exact_mod_cast h
        linarith), sgnZ_neg h]
      norm_num
    · rw [Real.sign_of_pos (by
        have : (0 : ℝ) < ((n : ℤ) : ℝ) := by exact_mod_cast h
        linarith), sgnZ_pos h]
      norm_num
  have hc2 : paper2B0 (-5) 3 (((r + 3 * k : ℤ) : ℝ) + 1 / 2) (((k : ℤ) : ℝ) + 1 / 10)
      = ((BAff (pellCoord k r) c2 : ℤ) : ℝ) / 2 := by
    rw [BAff_pellCoord_c2, paper2B0]
    push_cast
    ring
  have hc1 : paper2B0 0 1 (((r + 3 * k : ℤ) : ℝ) + 1 / 2) (((k : ℤ) : ℝ) + 1 / 10)
      = ((BAff (pellCoord k r) c1 : ℤ) : ℝ) / 2 := by
    rw [BAff_pellCoord_c1, paper2B0]
    push_cast
    ring
  simp only [paper2SignDiff]
  rw [hc2, hc1, hs _ (BAff_pellCoord_c2_ne_zero k r), hs _ (BAff_pellCoord_c1_ne_zero k r)]
  have h2 := two_mul_slabInd_eq_sign_diff k r
  have h3 : sgnZ (BAff (pellCoord k r) c2) - sgnZ (BAff (pellCoord k r) c1)
      = -2 * slabInd k r := by omega
  exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h3

/-- On the slab support the exponent is a nonnegative integer, so no negative
powers of `q` occur. -/
theorem slabInd_ne_zero_E_nonneg {k r : ℤ} (h : slabInd k r ≠ 0) : 0 ≤ E k r := by
  have hQ := two_mul_E k r
  unfold slabInd at h
  split_ifs at h with h1 h2
  · obtain ⟨hk, hr⟩ := h1
    have hpos : 0 ≤ Q k r := by
      unfold Q
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -r by linarith)
        (show (0 : ℤ) ≤ -(6 * k + 1) - r by linarith), sq_nonneg k, hk]
    omega
  · obtain ⟨hk, hr⟩ := h2
    have hpos : 0 ≤ Q k r := by
      unfold Q
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -k by linarith)
        (show (0 : ℤ) ≤ r + 6 * k by linarith), sq_nonneg (r + 6 * k), hk]
    omega
  · exact absurd rfl h

/-! ## The slab boxes and the per-degree fiber identity

`Ch10_MockModular_Certificate` proves `BCoeff N = slabCoeff N`, but its
`slabCoeff` is *extrinsic*: it is indexed by the same `A`/`D`-cone boxes as
`ACoeff`/`DCoeff`, with the summand rewritten through `σ`.  What the analytic
bridge needs is the *intrinsic* statement — the sum of `slabWeight` over the
slab points of a given degree — so that identity is proved here, by carrying
the index set through `σ` rather than only the summand. -/

def paper2SlabPlusBox (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).image
    fun p : ℕ × ℕ => ((p.1 : ℤ), sigma (p.1 : ℤ) (p.2 : ℤ))

def paper2SlabMinusBox (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).image
    fun p : ℕ × ℕ => (-((p.1 : ℤ) + 1), sigma (-((p.1 : ℤ) + 1)) (-((p.2 : ℤ) + 1)))

def paper2SlabBox (N : ℕ) : Finset (ℤ × ℤ) := paper2SlabPlusBox N ∪ paper2SlabMinusBox N

theorem slabInd_sigma_plus {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    slabInd a (sigma a b) = -1 := by
  unfold slabInd sigma
  split_ifs with h1 h2 <;> omega

theorem slabInd_sigma_minus {m s : ℤ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    slabInd (-(m + 1)) (sigma (-(m + 1)) (-(s + 1))) = 1 := by
  unfold slabInd sigma
  split_ifs with h1 h2 <;> omega

theorem slabPlusBox_sum (N : ℕ) :
    ∑ z ∈ paper2SlabPlusBox N, (if E z.1 z.2 = (N : ℤ) then slabWeight z.1 z.2 else 0)
      = ACoeff N := by
  rw [paper2SlabPlusBox, Finset.sum_image]
  · rw [ACoeff, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hE := sigma_preserves_E (p.1 : ℤ) (p.2 : ℤ)
    have hw : slabWeight (p.1 : ℤ) (sigma (p.1 : ℤ) (p.2 : ℤ)) = -negOnePowInt (p.2 : ℤ) := by
      rw [slabWeight, slabInd_sigma_plus (Int.natCast_nonneg _) (Int.natCast_nonneg _),
        sigma_flips_sign]
      ring
    rw [hE, hw]
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq, sigma] at hxy
    have h1 : x.1 = y.1 := by exact_mod_cast hxy.1
    have h2 : x.2 = y.2 := by
      have := hxy.2
      omega
    exact Prod.ext h1 h2

theorem slabMinusBox_sum (N : ℕ) :
    ∑ z ∈ paper2SlabMinusBox N, (if E z.1 z.2 = (N : ℤ) then slabWeight z.1 z.2 else 0)
      = DCoeff N := by
  rw [paper2SlabMinusBox, Finset.sum_image]
  · rw [DCoeff, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hE := sigma_preserves_E (-((p.1 : ℤ) + 1)) (-((p.2 : ℤ) + 1))
    have hw : slabWeight (-((p.1 : ℤ) + 1)) (sigma (-((p.1 : ℤ) + 1)) (-((p.2 : ℤ) + 1)))
        = negOnePowInt (-((p.2 : ℤ) + 1)) := by
      rw [slabWeight, slabInd_sigma_minus (Int.natCast_nonneg _) (Int.natCast_nonneg _),
        sigma_flips_sign]
      ring
    rw [hE, hw]
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq, sigma] at hxy
    have h1 : x.1 = y.1 := by
      have := hxy.1
      omega
    have h2 : x.2 = y.2 := by
      have := hxy.1
      have := hxy.2
      omega
    exact Prod.ext h1 h2

theorem paper2SlabBox_disjoint (N : ℕ) :
    Disjoint (paper2SlabPlusBox N) (paper2SlabMinusBox N) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [paper2SlabPlusBox, Finset.mem_image] at hz
  rw [paper2SlabMinusBox, Finset.mem_image] at hz'
  obtain ⟨x, _, hx⟩ := hz
  obtain ⟨y, _, hy⟩ := hz'
  have h1 : ((x.1 : ℤ)) = -((y.1 : ℤ) + 1) := congrArg Prod.fst (hx.trans hy.symm)
  omega

/-- **The intrinsic slab fiber identity.**  Summing `slabWeight` over the slab
points of degree `N` gives the repository's `BCoeff N`. -/
theorem slabBox_sum (N : ℕ) :
    ∑ z ∈ paper2SlabBox N, (if E z.1 z.2 = (N : ℤ) then slabWeight z.1 z.2 else 0)
      = BCoeff N := by
  rw [paper2SlabBox, Finset.sum_union (paper2SlabBox_disjoint N), slabPlusBox_sum,
    slabMinusBox_sum, BCoeff]
  ring

/-- Every slab point of degree `N` lies in the box. -/
theorem mem_paper2SlabBox {k r : ℤ} {N : ℕ} (h : slabInd k r ≠ 0) (hE : E k r = (N : ℤ)) :
    (k, r) ∈ paper2SlabBox N := by
  have hQ : Q k r = 2 * (N : ℤ) := by
    have h2 := two_mul_E k r
    omega
  unfold Q at hQ
  unfold slabInd at h
  split_ifs at h with h1 h2
  · obtain ⟨hk, hr⟩ := h1
    have ht : (0 : ℤ) ≤ -(6 * k + 1) - r := by linarith
    have hkN : k ≤ (N : ℤ) := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -r by linarith)
        (show (0 : ℤ) ≤ -(r + 6 * k + 1) by linarith), sq_nonneg k, hk]
    have htN : -(6 * k + 1) - r ≤ 2 * (N : ℤ) := by
      nlinarith [mul_nonneg ht (show (0 : ℤ) ≤ -r - 1 by linarith), sq_nonneg k, hk]
    refine Finset.mem_union_left _ ?_
    rw [paper2SlabPlusBox, Finset.mem_image]
    refine ⟨(k.toNat, (-(6 * k + 1) - r).toNat), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · have e1 : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk
      have e2 : (((-(6 * k + 1) - r).toNat : ℤ)) = -(6 * k + 1) - r := Int.toNat_of_nonneg ht
      simp only [Prod.mk.injEq, sigma]
      omega
  · obtain ⟨hk, hr⟩ := h2
    have hs : (0 : ℤ) ≤ r + 6 * k := by linarith
    have hmN : -k - 1 ≤ (N : ℤ) := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -k by linarith) hs, sq_nonneg (r + 6 * k),
        sq_nonneg k, hk]
    have hsN : r + 6 * k ≤ 2 * (N : ℤ) := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -k by linarith) hs, sq_nonneg (r + 6 * k),
        sq_nonneg k, hk]
    refine Finset.mem_union_right _ ?_
    rw [paper2SlabMinusBox, Finset.mem_image]
    refine ⟨((-k - 1).toNat, (r + 6 * k).toNat), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      omega
    · have e1 : (((-k - 1).toNat : ℤ)) = -k - 1 := Int.toNat_of_nonneg (by linarith)
      have e2 : (((r + 6 * k).toNat : ℤ)) = r + 6 * k := Int.toNat_of_nonneg hs
      simp only [Prod.mk.injEq, sigma]
      omega
  · exact absurd rfl h

/-! ## The analytic bridge

`½e^{-3πi/5} · Σ_p (sgn₂-sgn₁)(p) χ(p) q^{Q₀(v)} = q^{1/10} B(q)`.
The reindexing is `(x,y) ↦ (k,r) = (y, x-3y)`; then `Q₀(v) = E(k,r) + 1/10`,
the character phase contributes `e^{3πi/5}(-1)^r` (cancelling the
normalization), and the sign difference is `-2·slabInd`, so the summand becomes
`slabWeight(k,r) q^{1/10} q^{E(k,r)}`.  Regrouping by degree gives `BCoeff`. -/

noncomputable def paper2Nome (τ : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ)

noncomputable def paper2NomeTenth (τ : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ / 10)

/-- The degree of a lattice point.  `Int.toNat` clamps, so the degree-`0`
fiber also contains every point with `E < 0`; those all have `slabWeight = 0`
by `slabInd_ne_zero_E_nonneg`, which is what makes the regrouping legitimate. -/
def paper2Deg (z : ℤ × ℤ) : ℕ := (E z.1 z.2).toNat

noncomputable def paper2SgnKRTerm (z : ℤ × ℤ) (τ : ℂ) : ℂ :=
  ((slabWeight z.1 z.2 : ℤ) : ℂ) * (paper2NomeTenth τ * paper2Nome τ ^ paper2Deg z)

@[simp] theorem paper2KR_symm_apply (z : ℤ × ℤ) : paper2KR.symm z = (z.2 + 3 * z.1, z.1) := rfl

theorem norm_paper2Nome_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖paper2Nome τ‖ < 1 := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I * τ).re = -(2 * Real.pi * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [paper2Nome, Complex.norm_exp, hre, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

theorem paper2LatticeNome_kr (k r : ℤ) (n : ℕ) (hE : E k r = (n : ℤ)) (τ : ℂ) :
    paper2LatticeNome (r + 3 * k, k) τ = paper2NomeTenth τ * paper2Nome τ ^ n := by
  simp only [paper2LatticeNome]
  rw [paper2Q0_kr, hE]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * τ * ((((n : ℤ) : ℝ) + 1 / 10 : ℝ) : ℂ))
      = ((n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * τ)
        + 2 * (Real.pi : ℂ) * Complex.I * τ / 10 by push_cast; ring,
    Complex.exp_add, Complex.exp_nat_mul, paper2Nome, paper2NomeTenth]
  ring

/-- The termwise identity: the normalized sign summand, in Pell coordinates,
is `slabWeight · q^{1/10} · q^{E}`. -/
theorem paper2SgnTerm_kr (z : ℤ × ℤ) (τ : ℂ) :
    (1 / 2 : ℂ) * Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
        paper2LatticeSgnTerm (z.2 + 3 * z.1, z.1) τ = paper2SgnKRTerm z τ := by
  have hph : Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
      Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5) = 1 := by
    rw [← Complex.exp_add, show -3 * (Real.pi : ℂ) * Complex.I / 5
      + 3 * (Real.pi : ℂ) * Complex.I / 5 = 0 by ring, Complex.exp_zero]
  by_cases h : slabInd z.1 z.2 = 0
  · have hw : slabWeight z.1 z.2 = 0 := by rw [slabWeight, h]; ring
    have hsd : paper2SignDiff (z.2 + 3 * z.1, z.1) = 0 := by
      rw [paper2SignDiff_kr, h]
      norm_num
    rw [paper2SgnKRTerm, hw, paper2LatticeSgnTerm, hsd]
    push_cast
    ring
  · have hE := slabInd_ne_zero_E_nonneg h
    have hn : E z.1 z.2 = ((paper2Deg z : ℕ) : ℤ) := by
      rw [paper2Deg]
      exact (Int.toNat_of_nonneg hE).symm
    rw [paper2LatticeSgnTerm, paper2SignDiff_kr, paper2CharPhase_kr,
      paper2LatticeNome_kr z.1 z.2 (paper2Deg z) hn, paper2SgnKRTerm, slabWeight]
    push_cast
    linear_combination (-((slabInd z.1 z.2 : ℤ) : ℂ) * ((negOnePowInt z.2 : ℤ) : ℂ) *
      (paper2NomeTenth τ * paper2Nome τ ^ paper2Deg z)) * hph

theorem summable_paper2SgnKRTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun z : ℤ × ℤ => paper2SgnKRTerm z τ) := by
  have h := ((summable_paper2LatticeSgnTerm hτ).comp_injective
    paper2KR.symm.injective).mul_left
      ((1 / 2 : ℂ) * Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5))
  exact h.congr fun z => paper2SgnTerm_kr z τ

/-- Each degree fiber contributes `B_N q^{1/10} q^N`. -/
theorem paper2_fiber_tsum {τ : ℂ} (N : ℕ) :
    ∑' z : ↥(paper2Deg ⁻¹' {N}), paper2SgnKRTerm z τ
      = ((BCoeff N : ℤ) : ℂ) * (paper2NomeTenth τ * paper2Nome τ ^ N) := by
  classical
  have hterm : ∀ z : ℤ × ℤ,
      Set.indicator (paper2Deg ⁻¹' {N}) (fun z => paper2SgnKRTerm z τ) z
        = ((if E z.1 z.2 = (N : ℤ) then slabWeight z.1 z.2 else 0 : ℤ) : ℂ) *
            (paper2NomeTenth τ * paper2Nome τ ^ N) := by
    intro z
    rw [Set.indicator_apply]
    by_cases h : slabInd z.1 z.2 = 0
    · have hw : slabWeight z.1 z.2 = 0 := by rw [slabWeight, h]; ring
      rw [paper2SgnKRTerm, hw]
      split_ifs <;> simp
    · have hE := slabInd_ne_zero_E_nonneg h
      by_cases hd : z ∈ paper2Deg ⁻¹' {N}
      · have hEN : E z.1 z.2 = (N : ℤ) := by
          have hdd : paper2Deg z = N := hd
          rw [paper2Deg] at hdd
          omega
        have hdz : paper2Deg z = N := hd
        rw [if_pos hd, if_pos hEN, paper2SgnKRTerm, hdz]
      · have hEN : E z.1 z.2 ≠ (N : ℤ) := by
          intro hc
          exact hd (show paper2Deg z = N by rw [paper2Deg, hc]; simp)
        rw [if_neg hd, if_neg hEN]
        simp
  have hsupp : Function.support
      (Set.indicator (paper2Deg ⁻¹' {N}) (fun z => paper2SgnKRTerm z τ))
      ⊆ ↑(paper2SlabBox N) := by
    intro z hz
    rw [Function.mem_support, hterm z] at hz
    have h1 : (if E z.1 z.2 = (N : ℤ) then slabWeight z.1 z.2 else 0) ≠ 0 := by
      intro hc
      exact hz (by rw [hc]; simp)
    have hEN : E z.1 z.2 = (N : ℤ) := by
      by_contra hc
      rw [if_neg hc] at h1
      exact h1 rfl
    rw [if_pos hEN] at h1
    have hind : slabInd z.1 z.2 ≠ 0 := fun hc => h1 (by rw [slabWeight, hc]; ring)
    simpa using mem_paper2SlabBox hind hEN
  have hcast : ∑ z ∈ paper2SlabBox N,
      ((if E z.1 z.2 = (N : ℤ) then slabWeight z.1 z.2 else 0 : ℤ) : ℂ)
      = ((BCoeff N : ℤ) : ℂ) := by
    rw [← slabBox_sum N, Int.cast_sum]
  have hsub : (∑' z : ↥(paper2Deg ⁻¹' {N}), paper2SgnKRTerm (z : ℤ × ℤ) τ)
      = ∑' z : ℤ × ℤ, Set.indicator (paper2Deg ⁻¹' {N}) (fun z => paper2SgnKRTerm z τ) z :=
    tsum_subtype (paper2Deg ⁻¹' {N}) (fun z => paper2SgnKRTerm z τ)
  rw [hsub, tsum_eq_sum' hsupp, Finset.sum_congr rfl fun z _ => hterm z,
    ← Finset.sum_mul, hcast]

/-- **The sign-kernel bridge.**  The sign half of Zwegers' Definition 2.1
summand, with the manuscript's normalization, is `q^{1/10} B(q)`. -/
theorem paper2_sign_bridge {τ : ℂ} (hτ : 0 < τ.im) :
    (1 / 2 : ℂ) * Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
        (∑' p : ℤ × ℤ, paper2LatticeSgnTerm p τ)
      = paper2NomeTenth τ * paper2BSeries (paper2Nome τ) := by
  have hq := norm_paper2Nome_lt_one hτ
  have hfib := ((summable_paper2SgnKRTerm hτ).hasSum).tsum_fiberwise paper2Deg
  have hfun : (fun N : ℕ => ∑' z : ↥(paper2Deg ⁻¹' {N}), paper2SgnKRTerm z τ)
      = fun N : ℕ => paper2NomeTenth τ * (((BCoeff N : ℤ) : ℂ) * paper2Nome τ ^ N) := by
    funext N
    rw [paper2_fiber_tsum N]
    ring
  rw [hfun] at hfib
  have hB : HasSum (fun N : ℕ => paper2NomeTenth τ * (((BCoeff N : ℤ) : ℂ) * paper2Nome τ ^ N))
      (paper2NomeTenth τ * paper2BSeries (paper2Nome τ)) :=
    ((summable_BCoeff_mul_pow hq).hasSum).mul_left _
  have hlhs : ∑' z : ℤ × ℤ, paper2SgnKRTerm z τ
      = (1 / 2 : ℂ) * Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
          (∑' p : ℤ × ℤ, paper2LatticeSgnTerm p τ) := by
    rw [← (summable_paper2LatticeSgnTerm hτ).tsum_mul_left,
      ← paper2KR.symm.tsum_eq (fun p : ℤ × ℤ => (1 / 2 : ℂ) *
        Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) * paper2LatticeSgnTerm p τ)]
    exact tsum_congr fun z => (paper2SgnTerm_kr z τ).symm
  rw [← hlhs]
  exact hfib.unique hB

/-- **Zwegers' Definition 2.1 object, decomposed.**  `F̂ = q^{1/10}B(q)` plus
the boundary correction whose `∂̄` was computed in
`Ch10_Paper2_CompletedTheta`.  The holomorphic part is exactly `q^{1/10}B(q)`.

This is an identity of explicit convergent series.  It does not by itself say
that `F̂` transforms modularly: Zwegers' completion theorem is not formalized
here. -/
theorem paper2LatticeTheta_eq_bridge {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta τ
      = paper2NomeTenth τ * paper2BSeries (paper2Nome τ) + paper2LatticeCorrection τ := by
  rw [paper2LatticeTheta_eq hτ, paper2_sign_bridge hτ]

/-! ## The bridge, restated with the manuscript's own `B_N`

`paper2ConeCoeff` (in `Ch10_Paper2_ConeCoeff`) is `def:B` verbatim: a box-free
sum over the two cones.  With `paper2ConeCoeff_eq_BCoeff` the generating
function occurring in the bridge is the manuscript's `B(q)` by a theorem.

What this closes: the `B` in `paper2LatticeTheta_eq_bridge` is the `B` of the
manuscript's `def:B`.  What it does **not** close: any identification of that
`B` with Chan's original source object.  The manuscript is explicit that its
formal theorem concerns the row model defined there and that a
source-to-model theorem would be needed and is not claimed; none is claimed
here either. -/

/-- The bridge's generating function has the manuscript's `def:B` coefficients.
No hypothesis on `q` is needed — the identity is termwise. -/
theorem paper2BSeries_eq_coneSeries (q : ℂ) :
    paper2BSeries q = ∑' N : ℕ, ((paper2ConeCoeff N : ℤ) : ℂ) * q ^ N := by
  rw [paper2BSeries]
  exact tsum_congr fun N => by rw [paper2ConeCoeff_eq_BCoeff]

theorem summable_paper2ConeCoeff_mul_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun N : ℕ => ((paper2ConeCoeff N : ℤ) : ℂ) * q ^ N) :=
  (summable_BCoeff_mul_pow hq).congr fun N => by rw [paper2ConeCoeff_eq_BCoeff]

/-- **The sign-kernel bridge with the manuscript's `B`.** -/
theorem paper2_sign_bridge_cone {τ : ℂ} (hτ : 0 < τ.im) :
    (1 / 2 : ℂ) * Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
        (∑' p : ℤ × ℤ, paper2LatticeSgnTerm p τ)
      = paper2NomeTenth τ * ∑' N : ℕ, ((paper2ConeCoeff N : ℤ) : ℂ) * paper2Nome τ ^ N := by
  rw [paper2_sign_bridge hτ, paper2BSeries_eq_coneSeries]

/-- **Zwegers' Definition 2.1 object, decomposed, with the manuscript's `B`.**
`F̂ = q^{1/10}B(q) + (boundary correction)`, where `B` is now literally the
`def:B` cone series and the correction is the object whose `∂̄`, `ξ₁` and `Δ₁`
were computed in `Ch10_Paper2_CompletedTheta`.

Still an identity of explicit convergent series: it does not say `F̂`
transforms modularly, and Zwegers' completion theorem is not formalized. -/
theorem paper2LatticeTheta_eq_coneBridge {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta τ
      = paper2NomeTenth τ * (∑' N : ℕ, ((paper2ConeCoeff N : ℤ) : ℂ) * paper2Nome τ ^ N)
        + paper2LatticeCorrection τ := by
  rw [paper2LatticeTheta_eq_bridge hτ, paper2BSeries_eq_coneSeries]

end Ch10
end QseriesFormalization
