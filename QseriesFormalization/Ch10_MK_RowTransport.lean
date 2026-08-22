import QseriesFormalization.Ch10_MK_Defs

/-!
# Ch10: row transport for the missing kernel

The proof is coefficientwise.  On a fixed finite root fiber, `sigma k` is a
fixed-point-free involution preserving `Hq` and negating the sign.  Splitting
that fiber into its mixed and cone halves gives the two row-transport formulas.
-/

namespace QseriesFormalization
namespace Ch10

set_option maxHeartbeats 400000

theorem mkSign_sigma (k r : ℤ) :
    mkSign (sigma k r) = -mkSign r := by
  have hunit : (sigma k r).negOnePow = -r.negOnePow := by
    calc
      (sigma k r).negOnePow =
          (-r + (2 * (-3 * k - 1) + 1)).negOnePow := by
            congr 1
            unfold sigma
            ring
      _ = -r.negOnePow := by
        rw [Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_neg,
          Int.negOnePow_two_mul, Int.negOnePow_one]
        simp
  simpa [mkSign] using congrArg (fun z : ℤˣ => (z : ℤ)) hunit

theorem sigma_mem_rowFiber (k m r : ℤ) (hr : r ∈ rowFiber k m) :
    sigma k r ∈ rowFiber k m := by
  rw [rowFiber, Finset.mem_filter] at hr ⊢
  have hH : Hq k (sigma k r) = m := by
    calc
      Hq k (sigma k r) = Hq k r := sigma_preserves_Q k r
      _ = m := hr.2
  exact ⟨row_root_mem_window k (sigma k r) m hH, hH⟩

theorem rowFiber_sum_zero (k m : ℤ) :
    (rowFiber k m).sum mkSign = 0 := by
  apply finset_sum_cancel_invol (rowFiber k m) (sigma k) mkSign
  · intro r hr
    exact sigma_mem_rowFiber k m r hr
  · intro r _hr
    exact sigma_involutive k r
  · intro r _hr
    exact sigma_no_fixed_point k r
  · intro r _hr
    exact mkSign_sigma k r

theorem coneSide_iff_not_mixedSide (k r : ℤ) :
    coneSide k r ↔ ¬ mixedSide k r := by
  by_cases hk : 0 ≤ k
  · have hkn : ¬ k ≤ -1 := by omega
    simp only [coneSide, mixedSide, hk, hkn, true_and, false_and, or_false]
    omega
  · have hkn : k ≤ -1 := by omega
    simp only [coneSide, mixedSide, hk, hkn, false_and, true_and, false_or]
    omega

theorem rowConeCoeff_eq_complement (k m : ℤ) :
    rowConeCoeff k m =
      ((rowFiber k m).filter (fun r => ¬ mixedSide k r)).sum mkSign := by
  unfold rowConeCoeff
  apply Finset.sum_congr
  · ext r
    simp only [Finset.mem_filter]
    rw [coneSide_iff_not_mixedSide]
  · intro r _hr
    rfl

theorem rowMixed_add_rowCone (k m : ℤ) :
    rowMixedCoeff k m + rowConeCoeff k m = (rowFiber k m).sum mkSign := by
  rw [rowConeCoeff_eq_complement]
  exact Finset.sum_filter_add_sum_filter_not (rowFiber k m) (mixedSide k) mkSign

theorem row_transport_all (k m : ℤ) :
    rowMixedCoeff k m = -rowConeCoeff k m := by
  have hsplit := rowMixed_add_rowCone k m
  have hzero := rowFiber_sum_zero k m
  omega

/-- Row transport on an `A` row (`k ≥ 0`). -/
theorem row_transport (k m : ℤ) (_hk : 0 ≤ k) :
    rowMixedCoeff k m = -rowConeCoeff k m :=
  row_transport_all k m

/-- Mirror row transport on a `D` row (`k ≤ -1`). -/
theorem row_transport_neg (k m : ℤ) (_hk : k ≤ -1) :
    rowMixedCoeff k m = -rowConeCoeff k m :=
  row_transport_all k m

theorem row_signed_transport (k m : ℤ) :
    rowEpsilon k * rowMixedCoeff k m = coneSignedCoeff k m := by
  rw [row_transport_all]
  unfold coneSignedCoeff
  ring

end Ch10
end QseriesFormalization
