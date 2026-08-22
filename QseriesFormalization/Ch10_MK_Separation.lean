import QseriesFormalization.Ch10_MK_RowTransport

/-!
# Ch10: support separation and finite-window correctness

Row transport moves every mixed row to the cone side.  The cone side has the
explicit lower support `rowMin k`; this supplies all local-finiteness bounds
used by `MKcoeff` and by the final finite-sum interchange.
-/

namespace QseriesFormalization
namespace Ch10

set_option maxHeartbeats 400000

theorem rowMin_nonneg (k : ℤ) : 0 ≤ rowMin k := by
  unfold rowMin
  split_ifs with hk
  · nlinarith [sq_nonneg k]
  · have hk' : k ≤ -1 := by omega
    nlinarith [sq_nonneg k]

theorem abs_k_le_rowMin (k : ℤ) : |k| ≤ rowMin k := by
  unfold rowMin
  split_ifs with hk
  · rw [abs_of_nonneg hk]
    nlinarith [sq_nonneg k]
  · have hk' : k ≤ -1 := by omega
    rw [abs_of_nonpos (by omega)]
    nlinarith [sq_nonneg k]

theorem Hq_ge_rowMin_of_cone {k r : ℤ} (hcone : coneSide k r) :
    rowMin k ≤ Hq k r := by
  rcases hcone with hA | hD
  · have hp : 0 ≤ r * (r + 6 * k + 1) :=
      mul_nonneg hA.2 (by omega)
    simp only [rowMin, if_pos hA.1, Hq, Q]
    nlinarith
  · have hk : ¬ 0 ≤ k := by omega
    have hp : 0 ≤ (r + 1) * (r + 6 * k) :=
      mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    simp only [rowMin, if_neg hk, Hq, Q]
    nlinarith

theorem rowConeCoeff_vanish_below {k m : ℤ} (hm : m < rowMin k) :
    rowConeCoeff k m = 0 := by
  unfold rowConeCoeff
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_filter] at hr
  rw [rowFiber, Finset.mem_filter] at hr
  have hmin := Hq_ge_rowMin_of_cone hr.2
  omega

theorem rowMixed_vanish_below {k m : ℤ} (hm : m < rowMin k) :
    rowMixedCoeff k m = 0 := by
  rw [row_transport_all, rowConeCoeff_vanish_below hm, neg_zero]

theorem coneSignedCoeff_vanish_below {k m : ℤ} (hm : m < rowMin k) :
    coneSignedCoeff k m = 0 := by
  unfold coneSignedCoeff
  rw [rowConeCoeff_vanish_below hm, mul_zero]

theorem coneDiffH_vanish_below_zero {m : ℤ} (hm : m < 0) :
    coneDiffH m = 0 := by
  unfold coneDiffH
  apply Finset.sum_eq_zero
  intro k _hk
  apply coneSignedCoeff_vanish_below
  have := rowMin_nonneg k
  omega

/-! ## The exact inner window and its rectangular extension -/

noncomputable def mkGlobalRowCoeff (k T : ℤ) : ℤ :=
  ∑ a ∈ Finset.Icc (-2) T, QoutCoeff a * rowMixedCoeff k (T - a)

theorem mkRowCoeff_eq_global (k T : ℤ) :
    mkRowCoeff k T = mkGlobalRowCoeff k T := by
  unfold mkRowCoeff mkGlobalRowCoeff
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    have hmin := rowMin_nonneg k
    omega
  · intro a haGlobal haSmall
    rw [Finset.mem_Icc] at haGlobal
    have hlt : T - a < rowMin k := by
      by_contra h
      apply haSmall
      rw [Finset.mem_Icc]
      constructor <;> omega
    rw [rowMixed_vanish_below hlt, mul_zero]

theorem Qout_window_correct_low {a : ℤ} (ha : a < -2) :
    QoutCoeff a = 0 := QoutCoeff_vanish_below ha

theorem mk_summand_vanish_above {k T a : ℤ} (ha : T < a) :
    QoutCoeff a * rowMixedCoeff k (T - a) = 0 := by
  have hlt : T - a < rowMin k := by
    have := rowMin_nonneg k
    omega
  rw [rowMixed_vanish_below hlt, mul_zero]

theorem mkGlobalRowCoeff_vanish_outside
    {k T : ℤ}
    (hk : k ∉ Finset.Icc (-mkKBound T) (mkKBound T)) :
    mkGlobalRowCoeff k T = 0 := by
  by_cases hT : -2 ≤ T
  · unfold mkGlobalRowCoeff
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hk' : k < -mkKBound T ∨ mkKBound T < k := by
      rw [Finset.mem_Icc] at hk
      omega
    have hlarge : mkKBound T < |k| := by
      rcases hk' with hk' | hk'
      · have habs : -k ≤ |k| := neg_le_abs k
        omega
      · have habs : k ≤ |k| := le_abs_self k
        omega
    have hTle : T ≤ |T| := le_abs_self T
    have hkmin := abs_k_le_rowMin k
    have hbelow : T - a < rowMin k := by
      unfold mkKBound at hlarge
      omega
    rw [rowMixed_vanish_below hbelow, mul_zero]
  · unfold mkGlobalRowCoeff
    rw [Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]

/-! ## Comparing the `m`-window with the global `T`-window -/

theorem coneDiffH_eq_sum_mk_window {T a : ℤ}
    (ha : a ∈ Finset.Icc (-2) T) :
    coneDiffH (T - a) =
      ∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
        coneSignedCoeff k (T - a) := by
  rw [Finset.mem_Icc] at ha
  have hm : 0 ≤ T - a := by omega
  have hcb : (0:ℤ) ≤ coneKBound (T - a) := by
    unfold coneKBound
    have := abs_nonneg (T - a)
    omega
  have hmb : (0:ℤ) ≤ mkKBound T := by
    unfold mkKBound
    have := abs_nonneg T
    omega
  have hvan : ∀ k : ℤ, coneKBound (T - a) < |k| →
      coneSignedCoeff k (T - a) = 0 := by
    intro k hk
    apply coneSignedCoeff_vanish_below
    have hkmin := abs_k_le_rowMin k
    unfold coneKBound at hk
    rw [abs_of_nonneg hm] at hk
    linarith
  have hvan2 : ∀ k : ℤ, mkKBound T < |k| →
      coneSignedCoeff k (T - a) = 0 := by
    intro k hk
    apply coneSignedCoeff_vanish_below
    have hkmin := abs_k_le_rowMin k
    have hT : T ≤ |T| := le_abs_self T
    unfold mkKBound at hk
    linarith
  set B : ℤ := coneKBound (T - a) + mkKBound T with hB
  have h1 : coneDiffH (T - a) =
      ∑ k ∈ Finset.Icc (-B) B, coneSignedCoeff k (T - a) := by
    unfold coneDiffH
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hknot
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Icc] at hknot
      apply hvan
      rcases abs_cases k with ⟨h1a, h2a⟩ | ⟨h1a, h2a⟩ <;> omega
  have h2 : (∑ k ∈ Finset.Icc (-(mkKBound T)) (mkKBound T),
        coneSignedCoeff k (T - a)) =
      ∑ k ∈ Finset.Icc (-B) B, coneSignedCoeff k (T - a) := by
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hknot
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Icc] at hknot
      apply hvan2
      rcases abs_cases k with ⟨h1a, h2a⟩ | ⟨h1a, h2a⟩ <;> omega
  rw [h1, h2]

theorem rows_outside_kwindow_zero {k T : ℤ}
    (hk : k ∉ Finset.Icc (-mkKBound T) (mkKBound T)) :
    rowEpsilon k * mkGlobalRowCoeff k T = 0 := by
  rw [mkGlobalRowCoeff_vanish_outside hk, mul_zero]

end Ch10
end QseriesFormalization
