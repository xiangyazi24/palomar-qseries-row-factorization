import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ch10: Finset Sum Cancellation by Fixed-Point-Free Involution

A local wrapper around Mathlib's `Finset.sum_involution` adapted
to the specific needs of the interior cancellation and odd theta
vanishing proofs.

## Main result

* `finset_sum_cancel_invol`: if ι is a fixed-point-free involution on
  a Finset that negates the weight function, then the sum is zero.
-/

namespace QseriesFormalization
namespace Ch10

theorem finset_sum_cancel_invol
    {α : Type} [DecidableEq α]
    (s : Finset α) (ι : α → α) (w : α → Int)
    (hmem : ∀ a ∈ s, ι a ∈ s)
    (hinv : ∀ a ∈ s, ι (ι a) = a)
    (hfix : ∀ a ∈ s, ι a ≠ a)
    (hneg : ∀ a ∈ s, w (ι a) = -w a) :
    s.sum w = 0 := by
  apply Finset.sum_involution (fun a _ => ι a)
  · intro a ha
    rw [hneg a ha]
    omega
  · intro a ha _
    exact hfix a ha
  · intro a ha
    exact hmem a ha
  · intro a ha
    exact hinv a ha

end Ch10
end QseriesFormalization
