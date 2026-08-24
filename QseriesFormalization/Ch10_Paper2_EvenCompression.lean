import QseriesFormalization.Ch10_Paper2_LaurentFactorization

/-!
# Paper 2: even-support compression

The row model in Paper 2 is first assembled in an auxiliary variable `x`,
where every exponent is even, and is then rewritten in the manuscript variable
`q = x^2`.  This file makes that change of variables structural.  The ring
homomorphism `paper2ExpandEven` sends a Laurent monomial `q^n` to `x^(2n)`;
its injectivity lets the checked `x`-level factorization descend without any
coefficientwise cancellation.
-/

namespace QseriesFormalization
namespace Ch10

open QseriesFormalization.Pending.Ch10HM
open QseriesFormalization.Pending.JTPFormalPSPentagonal

noncomputable section

/-! ## The exponent-doubling ring embedding -/

/-- The additive exponent map implementing the substitution `q = x^2`. -/
def paper2DoubleExp : ℤ →+ ℤ where
  toFun n := 2 * n
  map_zero' := by ring
  map_add' := by intro a b; ring

@[simp] theorem paper2DoubleExp_apply (n : ℤ) :
    paper2DoubleExp n = 2 * n := rfl

theorem paper2DoubleExp_injective : Function.Injective paper2DoubleExp := by
  intro a b h
  change 2 * a = 2 * b at h
  omega

theorem paper2DoubleExp_le_iff (a b : ℤ) :
    paper2DoubleExp a ≤ paper2DoubleExp b ↔ a ≤ b := by
  change 2 * a ≤ 2 * b ↔ a ≤ b
  omega

/-- Expansion from the `q`-level Laurent ring to the even exponents of the
`x`-level Laurent ring.  It is a ring homomorphism because exponent doubling
preserves addition and order. -/
def paper2ExpandEven : QLaurent →+* QLaurent :=
  HahnSeries.embDomainRingHom paper2DoubleExp paper2DoubleExp_injective
    paper2DoubleExp_le_iff

@[simp] theorem lcoeff_paper2ExpandEven_two_mul (f : QLaurent) (n : ℤ) :
    lcoeff (paper2ExpandEven f) (2 * n) = lcoeff f n := by
  unfold paper2ExpandEven
  simp only [HahnSeries.embDomainRingHom]
  show (HahnSeries.embDomain
    ⟨⟨paper2DoubleExp, paper2DoubleExp_injective⟩,
      fun {a b} => paper2DoubleExp_le_iff a b⟩ f).coeff (2 * n) = f.coeff n
  simpa using HahnSeries.embDomain_mk_coeff paper2DoubleExp_injective
    paper2DoubleExp_le_iff (x := f) (a := n)

/-- An exponent outside `2ℤ` has zero coefficient after even expansion. -/
theorem lcoeff_paper2ExpandEven_of_not_two_dvd (f : QLaurent) {e : ℤ}
    (he : ¬ 2 ∣ e) :
    lcoeff (paper2ExpandEven f) e = 0 := by
  unfold paper2ExpandEven lcoeff
  simp only [HahnSeries.embDomainRingHom]
  show (HahnSeries.embDomain
    ⟨⟨paper2DoubleExp, paper2DoubleExp_injective⟩,
      fun {a b} => paper2DoubleExp_le_iff a b⟩ f).coeff e = 0
  rw [HahnSeries.embDomain_notin_range]
  rintro ⟨n, hn⟩
  apply he
  refine ⟨n, ?_⟩
  simpa [paper2DoubleExp] using hn.symm

/-- Exponent doubling is injective on Laurent series; equality can be tested
after the manuscript substitution `q = x^2`. -/
theorem paper2ExpandEven_injective : Function.Injective paper2ExpandEven := by
  intro f g h
  ext n
  have hn := congrArg (fun s : QLaurent => lcoeff s (2 * n)) h
  simpa using hn

@[simp] theorem paper2ExpandEven_Qpow (n : ℤ) :
    paper2ExpandEven (Qpow n) = Qpow (2 * n) := by
  unfold paper2ExpandEven Qpow
  simp only [HahnSeries.embDomainRingHom]
  change HahnSeries.embDomain
      ⟨⟨paper2DoubleExp, paper2DoubleExp_injective⟩,
        fun {a b} => paper2DoubleExp_le_iff a b⟩
      (HahnSeries.single n (1 : ℚ)) = HahnSeries.single (2 * n) (1 : ℚ)
  rw [HahnSeries.embDomain_single]
  rfl

/-! ## Parity of the row-model coefficients -/

/-- Every exponent in the first Jacobi leg is even. -/
theorem thetaU_exponent_even (u : ℤ) : 2 ∣ 5 * u ^ 2 - 3 * u := by
  rcases Int.even_or_odd u with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨10 * m ^ 2 - 3 * m, ?_⟩
    rw [hm]
    ring
  · refine ⟨10 * m ^ 2 + 7 * m + 1, ?_⟩
    rw [hm]
    ring

/-- Every exponent in the second Jacobi leg is even. -/
theorem thetaV_exponent_even (v : ℤ) : 2 ∣ 5 * v ^ 2 - 7 * v := by
  rcases Int.even_or_odd v with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨10 * m ^ 2 - 7 * m, ?_⟩
    rw [hm]
    ring
  · refine ⟨10 * m ^ 2 + 3 * m - 1, ?_⟩
    rw [hm]
    ring

/-- The first theta leg has zero coefficient at every odd exponent. -/
theorem thetaUCoeff_odd {e : ℤ} (he : ¬ 2 ∣ e) : thetaUCoeff e = 0 := by
  unfold thetaUCoeff
  apply Finset.sum_eq_zero
  intro u _hu
  split_ifs with hroot
  · have hEven := thetaU_exponent_even u
    rw [hroot] at hEven
    exact (he hEven).elim
  · rfl

/-- The second theta leg has zero coefficient at every odd exponent. -/
theorem thetaVCoeff_odd {e : ℤ} (he : ¬ 2 ∣ e) : thetaVCoeff e = 0 := by
  unfold thetaVCoeff
  apply Finset.sum_eq_zero
  intro v _hv
  split_ifs with hroot
  · have hEven := thetaV_exponent_even v
    rw [hroot] at hEven
    exact (he hEven).elim
  · rfl

/-- The theta-leg convolution is supported on even exponents. -/
theorem QoutCoeff_odd {e : ℤ} (he : ¬ 2 ∣ e) : QoutCoeff e = 0 := by
  unfold QoutCoeff
  apply Finset.sum_eq_zero
  intro a _ha
  by_cases ha : 2 ∣ a
  · have hrest : ¬ 2 ∣ e - a := by
      intro h
      apply he
      convert dvd_add h ha using 1
      ring
    rw [thetaVCoeff_odd hrest, mul_zero]
  · rw [thetaUCoeff_odd ha, zero_mul]

/-- The complete row kernel has no odd exponent.  In the finite convolution,
an even theta exponent meets an odd cone exponent, while an odd theta
exponent already has zero coefficient. -/
theorem MKcoeff_odd {e : ℤ} (he : ¬ 2 ∣ e) : MKcoeff e = 0 := by
  rw [mk_factorization]
  apply Finset.sum_eq_zero
  intro a _ha
  by_cases ha : 2 ∣ a
  · have hrest : ¬ 2 ∣ e - a := by
      intro h
      apply he
      convert dvd_add h ha using 1
      ring
    rw [coneDiffH_odd hrest, mul_zero]
  · rw [QoutCoeff_odd ha, zero_mul]

/-! ## Laurent series in the manuscript variable -/

/-- The coefficient sequence of the cone series `B(q)`, extended by zero to
negative integer exponents. -/
def paper2BCoeffZ (e : ℤ) : ℤ :=
  if 0 ≤ e then BCoeff e.toNat else 0

@[simp] theorem paper2BCoeffZ_ofNat (N : ℕ) :
    paper2BCoeffZ (N : ℤ) = BCoeff N := by
  simp [paper2BCoeffZ]

theorem paper2BCoeffZ_of_neg {e : ℤ} (he : e < 0) :
    paper2BCoeffZ e = 0 := by
  simp [paper2BCoeffZ, not_le.mpr he]

/-- The cone series `B(q) = Σ_{N≥0} B_N q^N` as a rational Laurent series. -/
def paper2BLaurent : QLaurent :=
  HahnSeries.ofSuppBddBelow (fun e : ℤ => (paper2BCoeffZ e : ℚ)) <| by
    refine ⟨0, ?_⟩
    intro e he
    by_contra hlow
    have hz : paper2BCoeffZ e = 0 := paper2BCoeffZ_of_neg (by omega)
    exact he (by simp [hz])

/-- The halved row model whose coefficient at `q^N` is the coefficient of
`x^(2N)` in the original row kernel. -/
def paper2RowLaurent : QLaurent :=
  HahnSeries.ofSuppBddBelow (fun e : ℤ => (MKcoeff (2 * e) : ℚ)) <| by
    refine ⟨-1, ?_⟩
    intro e he
    by_contra hlow
    have hz : MKcoeff (2 * e) = 0 := by
      rw [mk_factorization, Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]
    exact he (by simp [hz])

/-- The Jacobi factor `j(q;q^5)` in the manuscript variable. -/
def paper2ThetaQ : QLaurent := jLaurent 1 5

@[simp] theorem lcoeff_paper2BLaurent (e : ℤ) :
    lcoeff paper2BLaurent e = (paper2BCoeffZ e : ℚ) := by
  simp [lcoeff, paper2BLaurent]

@[simp] theorem lcoeff_paper2RowLaurent (e : ℤ) :
    lcoeff paper2RowLaurent e = (MKcoeff (2 * e) : ℚ) := by
  simp [lcoeff, paper2RowLaurent]

/-! ## Compatibility with exponent doubling -/

/-- Doubling both Jacobi parameters doubles every exponent and leaves the
coefficient sign unchanged. -/
theorem jExp_two_ten_eq_two_mul_one_five (n : ℤ) :
    jExp 2 10 n = 2 * jExp 1 5 n := by
  have hbig := two_mul_jExp 2 10 n
  have hsmall := two_mul_jExp 1 5 n
  unfold jExpTwice at hbig hsmall
  nlinarith

/-- Coefficients of `j(x^2;x^10)` at even exponents are those of
`j(q;q^5)` after halving the exponent. -/
theorem jCoeff_two_ten_two_mul (e : ℤ) :
    jCoeff 2 10 (2 * e) = jCoeff 1 5 e := by
  let W : ℤ := max (jCoeffWindow 2 10 (2 * e)) (jCoeffWindow 1 5 e)
  have hbig : jCoeff 2 10 (2 * e) =
      ∑ n ∈ Finset.Icc (-W) W,
        if jExp 2 10 n = 2 * e then negOnePowIntQ n else 0 :=
    jCoeff_eq_sum_Icc_of_window_le 2 10 (2 * e) W (by norm_num)
      (le_max_left _ _)
  have hsmall : jCoeff 1 5 e =
      ∑ n ∈ Finset.Icc (-W) W,
        if jExp 1 5 n = e then negOnePowIntQ n else 0 :=
    jCoeff_eq_sum_Icc_of_window_le 1 5 e W (by norm_num)
      (le_max_right _ _)
  rw [hbig, hsmall]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  rw [jExp_two_ten_eq_two_mul_one_five]
  by_cases hroot : jExp 1 5 n = e
  · rw [if_pos hroot, if_pos (by omega)]
  · rw [if_neg hroot, if_neg (by intro h; apply hroot; omega)]

/-- The doubled Jacobi series has no odd coefficient. -/
theorem jCoeff_two_ten_odd {e : ℤ} (he : ¬ 2 ∣ e) :
    jCoeff 2 10 e = 0 := by
  rw [jCoeff_eq_sum_Icc_of_window_le 2 10 e (jCoeffWindow 2 10 e)
    (by norm_num) le_rfl]
  apply Finset.sum_eq_zero
  intro n _hn
  split_ifs with hroot
  · have hEven : 2 ∣ jExp 2 10 n := by
      rw [jExp_two_ten_eq_two_mul_one_five]
      exact dvd_mul_right 2 _
    rw [hroot] at hEven
    exact (he hEven).elim
  · rfl

/-- The manuscript Jacobi factor expands to the first `x`-level theta leg. -/
theorem paper2ExpandEven_thetaQ :
    paper2ExpandEven paper2ThetaQ = paper2ThetaU := by
  ext e
  change lcoeff (paper2ExpandEven paper2ThetaQ) e = lcoeff paper2ThetaU e
  by_cases he : 2 ∣ e
  · obtain ⟨n, rfl⟩ := he
    rw [lcoeff_paper2ExpandEven_two_mul]
    rw [paper2ThetaQ, paper2ThetaU, coeff_jLaurent, coeff_jLaurent]
    exact (jCoeff_two_ten_two_mul n).symm
  · rw [lcoeff_paper2ExpandEven_of_not_two_dvd _ he]
    rw [paper2ThetaU, coeff_jLaurent, jCoeff_two_ten_odd he]

/-- Expanding `B(q)` recovers the `H`-level cone difference.  The even
coefficients use `coneDiffH_two_mul`; the odd coefficients use
`coneDiffH_odd`. -/
theorem paper2ExpandEven_BLaurent :
    paper2ExpandEven paper2BLaurent = paper2ConeLaurent := by
  ext e
  change lcoeff (paper2ExpandEven paper2BLaurent) e = lcoeff paper2ConeLaurent e
  by_cases he : 2 ∣ e
  · obtain ⟨n, rfl⟩ := he
    rw [lcoeff_paper2ExpandEven_two_mul, lcoeff_paper2BLaurent,
      lcoeff_paper2ConeLaurent]
    by_cases hn : 0 ≤ n
    · rw [paper2BCoeffZ, if_pos hn]
      have hnat : (((n.toNat : ℕ) : ℤ)) = n := Int.toNat_of_nonneg hn
      simpa [hnat] using
        congrArg (fun z : ℤ => (z : ℚ)) (coneDiffH_two_mul n.toNat).symm
    · rw [paper2BCoeffZ, if_neg hn]
      have hcone : coneDiffH (2 * n) = 0 :=
        coneDiffH_vanish_below_zero (by omega)
      rw [hcone]
  · rw [lcoeff_paper2ExpandEven_of_not_two_dvd _ he,
      lcoeff_paper2ConeLaurent]
    simp [coneDiffH_odd he]

/-- Expanding the halved row model recovers the original row kernel; odd
coefficients vanish by `MKcoeff_odd`. -/
theorem paper2ExpandEven_rowLaurent :
    paper2ExpandEven paper2RowLaurent = paper2MKLaurent := by
  ext e
  change lcoeff (paper2ExpandEven paper2RowLaurent) e = lcoeff paper2MKLaurent e
  by_cases he : 2 ∣ e
  · obtain ⟨n, rfl⟩ := he
    rw [lcoeff_paper2ExpandEven_two_mul, lcoeff_paper2RowLaurent,
      lcoeff_paper2MKLaurent]
  · rw [lcoeff_paper2ExpandEven_of_not_two_dvd _ he,
      lcoeff_paper2MKLaurent]
    simp [MKcoeff_odd he]

/-! ## The boxed factorization in the `q` variable -/

/-- Formal Jacobi triple product for the manuscript factor `j(q;q^5)`. -/
theorem paper2ThetaQ_eq_tripleProduct :
    paper2ThetaQ =
      ((qPochAPPS ℚ 5 5 : PowerSeries ℚ) : QLaurent) *
        ((qPochAPPS ℚ 1 5 : PowerSeries ℚ) : QLaurent) *
          ((qPochAPPS ℚ 4 5 : PowerSeries ℚ) : QLaurent) := by
  simpa [paper2ThetaQ] using jLaurent_eq_tripleProductInf 1 5 (by norm_num) (by norm_num)

/-- Paper 2's boxed halved-variable identity
`R(q) = -q^(-1) j(q;q^5)^2 B(q)`.  The proof expands both sides to the
already checked `x`-level identity and cancels the injective substitution. -/
theorem paper2RowLaurent_eq_jacobi_sq_mul_B :
    paper2RowLaurent =
      (-Qpow (-1) * paper2ThetaQ ^ 2) * paper2BLaurent := by
  apply paper2ExpandEven_injective
  rw [paper2ExpandEven_rowLaurent]
  simp only [map_mul, map_neg, map_pow, paper2ExpandEven_Qpow,
    paper2ExpandEven_thetaQ, paper2ExpandEven_BLaurent]
  norm_num
  simpa [neg_mul, mul_assoc] using paper2MKLaurent_eq_jacobi_sq_mul_cone

end

end Ch10
end QseriesFormalization
