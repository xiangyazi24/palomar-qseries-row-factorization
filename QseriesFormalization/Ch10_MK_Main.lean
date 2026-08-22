import QseriesFormalization.Ch10_MK_Separation
import QseriesFormalization.Ch10_NormTheta_Coeff

/-!
# Ch10: coefficientwise missing-kernel factorization

The headline theorem is a finite convolution identity.  This file also bridges
the independently defined `H`-level cone count to the existing `BCoeff` atom
infrastructure at even levels.
-/

namespace QseriesFormalization
namespace Ch10

set_option maxHeartbeats 400000

/-! ## Finite separation -/

theorem mk_factorization (T : ℤ) :
    MKcoeff T =
      ∑ a ∈ Finset.Icc (-2) T,
        QoutCoeff a * coneDiffH (T - a) := by
  classical
  unfold MKcoeff
  calc
    (∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
        rowEpsilon k * mkRowCoeff k T) =
        ∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
          rowEpsilon k * mkGlobalRowCoeff k T := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [mkRowCoeff_eq_global]
    _ = ∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
          ∑ a ∈ Finset.Icc (-2) T,
            QoutCoeff a * coneSignedCoeff k (T - a) := by
          apply Finset.sum_congr rfl
          intro k _hk
          unfold mkGlobalRowCoeff
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _ha
          calc
            rowEpsilon k *
                (QoutCoeff a * rowMixedCoeff k (T - a)) =
                QoutCoeff a *
                  (rowEpsilon k * rowMixedCoeff k (T - a)) := by ring
            _ = QoutCoeff a * coneSignedCoeff k (T - a) := by
              rw [row_signed_transport]
    _ = ∑ a ∈ Finset.Icc (-2) T,
          QoutCoeff a *
            (∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
              coneSignedCoeff k (T - a)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
    _ = ∑ a ∈ Finset.Icc (-2) T,
          QoutCoeff a * coneDiffH (T - a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [coneDiffH_eq_sum_mk_window ha]

/-! ## Reindexing a cone row by the Nat atom coordinate -/

private theorem rowCone_nonneg_as_nat (N k : ℕ) :
    rowConeCoeff (k : ℤ) (2 * (N : ℤ)) =
      ∑ r ∈ (Finset.range (2 * N + 2)).filter
          (fun r : ℕ => E (k : ℤ) (r : ℤ) = (N : ℤ)),
        mkSign (r : ℤ) := by
  classical
  unfold rowConeCoeff
  refine Finset.sum_nbij'
    (fun r => r.toNat) (fun r : ℕ => (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, rowFiber] at hr
    obtain ⟨⟨_hwin, hH⟩, hcone⟩ := hr
    have hr0 : 0 ≤ r := by
      rcases hcone with hA | hD
      · exact hA.2
      · omega
    have hQ : Q (k : ℤ) r = 2 * (N : ℤ) := hH
    have hE : E (k : ℤ) r = (N : ℤ) := by
      have hQE := Q_eq_two_mul_E (k : ℤ) r
      omega
    have hrb := A_bound_r (k : ℤ) r (Int.natCast_nonneg k) hr0 hE
    show r.toNat ∈ (Finset.range (2 * N + 2)).filter
        (fun r : ℕ => E (k : ℤ) (r : ℤ) = (N : ℤ))
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · have hcast : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
      rw [hcast]
      exact hE
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    have hE := hr.2
    have hQ : Q (k : ℤ) (r : ℤ) = 2 * (N : ℤ) := by
      have hQE := Q_eq_two_mul_E (k : ℤ) (r : ℤ)
      omega
    have hH : Hq (k : ℤ) (r : ℤ) = 2 * (N : ℤ) := hQ
    show (r : ℤ) ∈ (rowFiber (k : ℤ) (2 * (N : ℤ))).filter (coneSide (k : ℤ))
    rw [Finset.mem_filter, rowFiber, Finset.mem_filter]
    exact ⟨⟨row_root_mem_window _ _ _ hH, hH⟩,
      Or.inl ⟨Int.natCast_nonneg k, Int.natCast_nonneg r⟩⟩
  · intro r hr
    simp only [Finset.mem_filter, rowFiber] at hr
    have hr0 : 0 ≤ r := by
      rcases hr.2 with hA | hD
      · exact hA.2
      · omega
    show ((r.toNat : ℕ) : ℤ) = r
    exact Int.toNat_of_nonneg hr0
  · intro r _hr
    show ((r : ℤ)).toNat = r
    omega
  · intro r hr
    simp only [Finset.mem_filter, rowFiber] at hr
    have hr0 : 0 ≤ r := by
      rcases hr.2 with hA | hD
      · exact hA.2
      · omega
    have hcast : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    show mkSign r = mkSign ((r.toNat : ℕ) : ℤ)
    rw [hcast]

private theorem rowCone_neg_as_nat (N n : ℕ) :
    rowConeCoeff (-((n : ℤ) + 1)) (2 * (N : ℤ)) =
      ∑ s ∈ (Finset.range (2 * N + 2)).filter
          (fun s : ℕ => E (-((n : ℤ) + 1)) (-((s : ℤ) + 1)) = (N : ℤ)),
        mkSign (-((s : ℤ) + 1)) := by
  classical
  unfold rowConeCoeff
  refine Finset.sum_nbij'
    (fun r => (-r - 1).toNat) (fun s : ℕ => -((s : ℤ) + 1)) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, rowFiber] at hr
    obtain ⟨⟨_hwin, hH⟩, hcone⟩ := hr
    have hrn : r ≤ -1 := by
      rcases hcone with hA | hD
      · omega
      · exact hD.2
    have hQ : Q (-((n : ℤ) + 1)) r = 2 * (N : ℤ) := hH
    have hE : E (-((n : ℤ) + 1)) r = (N : ℤ) := by
      have hQE := Q_eq_two_mul_E (-((n : ℤ) + 1)) r
      omega
    have hrb := D_bound_r (-((n : ℤ) + 1)) r (by omega) (by omega) hE
    show (-r - 1).toNat ∈ (Finset.range (2 * N + 2)).filter
        (fun s : ℕ => E (-((n : ℤ) + 1)) (-((s : ℤ) + 1)) = (N : ℤ))
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · have harg : -((((-r - 1).toNat : ℕ) : ℤ) + 1) = r := by omega
      rw [harg]
      exact hE
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_range] at hs
    have hE := hs.2
    have hQ : Q (-((n : ℤ) + 1)) (-((s : ℤ) + 1)) = 2 * (N : ℤ) := by
      have hQE := Q_eq_two_mul_E (-((n : ℤ) + 1)) (-((s : ℤ) + 1))
      omega
    have hH : Hq (-((n : ℤ) + 1)) (-((s : ℤ) + 1)) = 2 * (N : ℤ) := hQ
    show -((s : ℤ) + 1) ∈
        (rowFiber (-((n : ℤ) + 1)) (2 * (N : ℤ))).filter
          (coneSide (-((n : ℤ) + 1)))
    rw [Finset.mem_filter, rowFiber, Finset.mem_filter]
    exact ⟨⟨row_root_mem_window _ _ _ hH, hH⟩,
      Or.inr ⟨by omega, by omega⟩⟩
  · intro r hr
    simp only [Finset.mem_filter, rowFiber] at hr
    have hrn : r ≤ -1 := by
      rcases hr.2 with hA | hD
      · omega
      · exact hD.2
    show -((((-r - 1).toNat : ℕ) : ℤ) + 1) = r
    omega
  · intro s _hs
    show (-(-((s : ℤ) + 1)) - 1).toNat = s
    omega
  · intro r hr
    simp only [Finset.mem_filter, rowFiber] at hr
    have hrn : r ≤ -1 := by
      rcases hr.2 with hA | hD
      · omega
      · exact hD.2
    have harg : -((((-r - 1).toNat : ℕ) : ℤ) + 1) = r := by omega
    show mkSign r = mkSign (-((((-r - 1).toNat : ℕ) : ℤ) + 1))
    rw [harg]

private theorem sum_nonneg_Icc_eq_range (N : ℕ) (f : ℤ → ℤ) :
    ∑ k ∈ Finset.Icc 0 (N : ℤ), f k =
      ∑ n ∈ Finset.range (N + 1), f (n : ℤ) := by
  classical
  refine Finset.sum_nbij'
    (s := Finset.Icc (0 : ℤ) (N : ℤ)) (t := Finset.range (N + 1))
      Int.toNat (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    have hcast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk.1
    omega
  · intro n hn
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc]
    constructor
    · exact Int.natCast_nonneg n
    · have hnle : n ≤ N := Nat.lt_succ_iff.mp hn
      exact Int.ofNat_le_ofNat_of_le hnle
  · intro k hk
    rw [Finset.mem_Icc] at hk
    exact Int.toNat_of_nonneg hk.1
  · intro n _hn
    exact Int.toNat_natCast n
  · intro k hk
    rw [Finset.mem_Icc] at hk
    simp [Int.toNat_of_nonneg hk.1]

private theorem sum_neg_Icc_eq_range (N : ℕ) (f : ℤ → ℤ) :
    ∑ k ∈ Finset.Icc (-((N : ℤ) + 1)) (-1), f k =
      ∑ n ∈ Finset.range (N + 1), f (-((n : ℤ) + 1)) := by
  classical
  refine Finset.sum_nbij'
    (s := Finset.Icc (-((N : ℤ) + 1)) (-1)) (t := Finset.range (N + 1))
      (fun k => (-k - 1).toNat) (fun n => -((n : ℤ) + 1)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    have h0 : 0 ≤ -k - 1 := by omega
    have hcast : (((-k - 1).toNat : ℕ) : ℤ) = -k - 1 :=
      Int.toNat_of_nonneg h0
    have hleZ : (((-k - 1).toNat : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [hcast]
      omega
    have hle : (-k - 1).toNat ≤ N := Int.le_of_ofNat_le_ofNat hleZ
    exact Nat.lt_succ_iff.mpr hle
  · intro n hn
    rw [Finset.mem_range] at hn
    show -((n : ℤ) + 1) ∈ Finset.Icc (-((N : ℤ) + 1)) (-1)
    rw [Finset.mem_Icc]
    constructor <;> omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    show -((((-k - 1).toNat : ℕ) : ℤ) + 1) = k
    omega
  · intro n _hn
    show (-(-((n : ℤ) + 1)) - 1).toNat = n
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have h0 : 0 ≤ -k - 1 := by omega
    have hcast : (((-k - 1).toNat : ℕ) : ℤ) = -k - 1 :=
      Int.toNat_of_nonneg h0
    congr 1
    rw [hcast]
    ring

private theorem ACoeff_eq_double_sum (N : ℕ) :
    ACoeff N =
      ∑ k ∈ Finset.range (N + 1),
        ∑ r ∈ (Finset.range (2 * N + 2)).filter
            (fun r : ℕ => E (k : ℤ) (r : ℤ) = (N : ℤ)),
          -mkSign (r : ℤ) := by
  unfold ACoeff
  simp_rw [← mkSign_eq_negOnePowInt]
  apply Finset.sum_finset_product
  intro p
  simp [and_assoc]

private theorem DCoeff_eq_double_sum (N : ℕ) :
    DCoeff N =
      ∑ n ∈ Finset.range (N + 1),
        ∑ s ∈ (Finset.range (2 * N + 2)).filter
            (fun s : ℕ => E (-((n : ℤ) + 1)) (-((s : ℤ) + 1)) = (N : ℤ)),
          mkSign (-((s : ℤ) + 1)) := by
  unfold DCoeff
  simp_rw [← mkSign_eq_negOnePowInt]
  apply Finset.sum_finset_product
  intro p
  simp [and_assoc]

private theorem cone_positive_sum_eq_ACoeff (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 (N : ℤ),
      coneSignedCoeff k (2 * (N : ℤ))) = ACoeff N := by
  rw [sum_nonneg_Icc_eq_range, ACoeff_eq_double_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    coneSignedCoeff (k : ℤ) (2 * (N : ℤ)) =
        -rowConeCoeff (k : ℤ) (2 * (N : ℤ)) := by
          simp [coneSignedCoeff, rowEpsilon]
    _ = -(∑ r ∈ (Finset.range (2 * N + 2)).filter
          (fun r : ℕ => E (k : ℤ) (r : ℤ) = (N : ℤ)),
        mkSign (r : ℤ)) := by rw [rowCone_nonneg_as_nat]
    _ = ∑ r ∈ (Finset.range (2 * N + 2)).filter
          (fun r : ℕ => E (k : ℤ) (r : ℤ) = (N : ℤ)),
        -mkSign (r : ℤ) := by rw [Finset.sum_neg_distrib]

private theorem cone_negative_sum_eq_DCoeff (N : ℕ) :
    (∑ k ∈ Finset.Icc (-((N : ℤ) + 1)) (-1),
      coneSignedCoeff k (2 * (N : ℤ))) = DCoeff N := by
  rw [sum_neg_Icc_eq_range, DCoeff_eq_double_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  calc
    coneSignedCoeff (-((n : ℤ) + 1)) (2 * (N : ℤ)) =
        rowConeCoeff (-((n : ℤ) + 1)) (2 * (N : ℤ)) := by
          have hkneg : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
          rw [coneSignedCoeff, rowEpsilon, if_neg hkneg]
          ring
    _ = ∑ s ∈ (Finset.range (2 * N + 2)).filter
          (fun s : ℕ => E (-((n : ℤ) + 1)) (-((s : ℤ) + 1)) = (N : ℤ)),
        mkSign (-((s : ℤ) + 1)) := rowCone_neg_as_nat N n

/-! ## Truncating and splitting the cone-row sum -/

private theorem rowCone_nonneg_zero_of_gt {N : ℕ} {k : ℤ}
    (hk0 : 0 ≤ k) (hkN : (N : ℤ) < k) :
    rowConeCoeff k (2 * (N : ℤ)) = 0 := by
  unfold rowConeCoeff
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_filter, rowFiber, Finset.mem_filter] at hr
  have hr0 : 0 ≤ r := by
    rcases hr.2 with hA | hD
    · exact hA.2
    · omega
  have hE : E k r = (N : ℤ) := by
    have hQ : Q k r = 2 * (N : ℤ) := hr.1.2
    have hQE := Q_eq_two_mul_E k r
    omega
  have := A_bound_k k r hk0 hr0 hE
  omega

private theorem rowCone_neg_zero_of_lt {N : ℕ} {k : ℤ}
    (hkneg : k ≤ -1) (hkN : k < -((N : ℤ) + 1)) :
    rowConeCoeff k (2 * (N : ℤ)) = 0 := by
  unfold rowConeCoeff
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_filter, rowFiber, Finset.mem_filter] at hr
  have hrneg : r ≤ -1 := by
    rcases hr.2 with hA | hD
    · omega
    · exact hD.2
  have hE : E k r = (N : ℤ) := by
    have hQ : Q k r = 2 * (N : ℤ) := hr.1.2
    have hQE := Q_eq_two_mul_E k r
    omega
  have := D_bound_k k r (by omega) (by omega) hE
  omega

private theorem coneDiffH_two_mul_truncate (N : ℕ) :
    coneDiffH (2 * (N : ℤ)) =
      ∑ k ∈ Finset.Icc (-((N : ℤ) + 1)) (N : ℤ),
        coneSignedCoeff k (2 * (N : ℤ)) := by
  unfold coneDiffH
  symm
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    simp only [coneKBound]
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (N : ℤ))]
    constructor <;> omega
  · intro k hkBig hkSmall
    rw [Finset.mem_Icc] at hkBig
    rw [Finset.mem_Icc] at hkSmall
    by_cases hk0 : 0 ≤ k
    · have hkN : (N : ℤ) < k := by omega
      unfold coneSignedCoeff
      rw [rowCone_nonneg_zero_of_gt hk0 hkN, mul_zero]
    · have hkneg : k ≤ -1 := by omega
      have hkN : k < -((N : ℤ) + 1) := by omega
      unfold coneSignedCoeff
      rw [rowCone_neg_zero_of_lt hkneg hkN, mul_zero]

private theorem sum_relevant_split (N : ℕ) (f : ℤ → ℤ) :
    (∑ k ∈ Finset.Icc (-((N : ℤ) + 1)) (N : ℤ), f k) =
      (∑ k ∈ Finset.Icc 0 (N : ℤ), f k) +
      (∑ k ∈ Finset.Icc (-((N : ℤ) + 1)) (-1), f k) := by
  classical
  let S : Finset ℤ := Finset.Icc (-((N : ℤ) + 1)) (N : ℤ)
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun k => 0 ≤ k) f
  have hpos : S.filter (fun k => 0 ≤ k) = Finset.Icc 0 (N : ℤ) := by
    ext k
    simp [S, Finset.mem_Icc]
    omega
  have hneg : S.filter (fun k => ¬ 0 ≤ k) =
      Finset.Icc (-((N : ℤ) + 1)) (-1) := by
    ext k
    simp [S, Finset.mem_Icc]
    omega
  rw [hpos, hneg] at hsplit
  simpa [S] using hsplit.symm

/-! ## Bridge to the existing `BCoeff` atoms -/

theorem coneDiffH_two_mul (N : ℕ) :
    coneDiffH (2 * (N : ℤ)) = BCoeff N := by
  rw [coneDiffH_two_mul_truncate]
  rw [sum_relevant_split]
  rw [cone_positive_sum_eq_ACoeff, cone_negative_sum_eq_DCoeff]
  unfold BCoeff
  ring

theorem rowConeCoeff_vanish_odd {k m : ℤ} (hm : ¬ 2 ∣ m) :
    rowConeCoeff k m = 0 := by
  unfold rowConeCoeff
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_filter, rowFiber, Finset.mem_filter] at hr
  exfalso
  apply hm
  rw [← hr.1.2]
  exact Q_even k r

theorem coneDiffH_odd {m : ℤ} (hm : ¬ 2 ∣ m) :
    coneDiffH m = 0 := by
  unfold coneDiffH coneSignedCoeff
  apply Finset.sum_eq_zero
  intro k _hk
  rw [rowConeCoeff_vanish_odd hm, mul_zero]

/-!
The Jacobi-triple-product evaluation of the two theta legs and the halved
variable restatement are intentionally phase 2.  The theorem above is the
complete coefficientwise series-level factorization required here.
-/

end Ch10
end QseriesFormalization
