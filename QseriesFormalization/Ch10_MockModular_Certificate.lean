import QseriesFormalization.Ch10_MockModular_Sigma
import QseriesFormalization.Ch10_MockModular_Pell
import QseriesFormalization.Ch10_MockModular_SlabIndicator
import QseriesFormalization.Ch10_MockModular_OddTheta
import QseriesFormalization.Ch10_MockModular_Shadow

/-!
# Ch10: Mock Modularity Certificate

The algebraic/combinatorial certificate for Chan's Θ₁₀ over Q(√5).
Conjuncts are the inputs to Zwegers' theorem specialized to our lattice.
`MockCertificate` is a historical project name: the structure below packages
finite algebraic inputs and does not itself prove a modular transformation law,
harmonicity, or a standard harmonic-Maass mock-modularity statement.

## Slab decomposition

BCoeff N = slabCoeff N is proved by σ-reindexing (not interior
cancellation). Each A-cone point (k,r) maps via σ_k to a slab+ point
with weight negOnePowInt(σ_k(r)) = -negOnePowInt(r), which is exactly
the ACoeff weight. Similarly for D-cone → slab-.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Slab coefficient via σ-reindex (extrinsic: same box as ACoeff/DCoeff) -/

def slabWeight (k r : Int) : Int := -slabInd k r * negOnePowInt r

def slabPlusCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N)).sum
    (fun p => negOnePowInt (sigma (↑p.1) (↑p.2)))

def slabMinusCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N)).sum
    (fun p => -negOnePowInt (sigma (-(↑p.1 + 1)) (-(↑p.2 + 1))))

def slabCoeff (N : Nat) : Int := slabPlusCoeff N + slabMinusCoeff N

/-! ## Slab decomposition proof -/

theorem ACoeff_eq_slabPlusCoeff (N : Nat) : ACoeff N = slabPlusCoeff N := by
  unfold ACoeff slabPlusCoeff
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have := sigma_flips_sign (↑p.1) (↑p.2)
  omega

theorem DCoeff_eq_slabMinusCoeff (N : Nat) : DCoeff N = slabMinusCoeff N := by
  unfold DCoeff slabMinusCoeff
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have := sigma_flips_sign (-(↑p.1 + 1)) (-(↑p.2 + 1))
  omega

theorem BCoeff_eq_slabCoeff (N : Nat) : BCoeff N = slabCoeff N := by
  unfold BCoeff slabCoeff
  rw [ACoeff_eq_slabPlusCoeff, DCoeff_eq_slabMinusCoeff]
  ring

/-! ## The certificate structure -/

structure MockCertificate : Prop where
  slab_decomp : ∀ N : Nat, BCoeff N = slabCoeff N
  cone_indicator : ∀ k r : Int,
    2 * slabInd k r =
      sgnZ (BAff (pellCoord k r) c1) -
      sgnZ (BAff (pellCoord k r) c2)
  c1_norm : pellQ c1 = -5
  c2_norm : pellQ c2 = -20
  cusp_norms_distinct : pellQ c1 ≠ pellQ c2
  odd_theta_cancel : ∀ x : Int,
    negOnePowInt x + negOnePowInt (thetaInvol x) = 0
  shadow_witness : shadowCoeff 4 = 1
  shadow_nonzero : ∃ N : Nat, shadowCoeff N ≠ 0
  pell_form_invariant : ∀ v : ZVec, pellQ (Mmul v) = pellQ v
  cone_indecomp : pellB (Mmul c1) c2 < 0

/-! ## Inhabiting the certificate -/

theorem chanTheta10_mock_certificate : MockCertificate where
  slab_decomp := BCoeff_eq_slabCoeff
  cone_indicator := two_mul_slabInd_eq_sign_diff
  c1_norm := pellQ_c1
  c2_norm := pellQ_c2
  cusp_norms_distinct := cusp_norms_ne
  odd_theta_cancel := odd_theta_fiber_cancel
  shadow_witness := shadowCoeff_four
  shadow_nonzero := shadow_nonzero
  pell_form_invariant := pellQ_Mmul
  cone_indecomp := cone_indecomposable'

end Ch10
end QseriesFormalization
