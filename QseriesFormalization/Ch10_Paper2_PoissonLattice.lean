import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Poisson summation on the lattice `ℤᵈ ⊆ ℝᵈ`

Mathlib's `Mathlib/Analysis/Fourier/PoissonSummation.lean` is entirely one-dimensional: all
five of its results are sums over `ℤ`.  There is no lattice or LCA version.  This file supplies
the lattice version in the shape Paper 2 needs, for the square lattice `ℤᵈ` acting on `ℝᵈ`.

The route is a port of `Real.fourierCoeff_tsum_comp_add` to the multivariate torus.  The
ingredients that already exist are:

* `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`, the pointwise convergence of the
  multivariate Fourier series of a continuous function on `UnitAddTorus d` with summable
  Fourier coefficients;
* `UnitAddTorus.mFourierCoeff_eq_integral`, which rewrites the torus integral defining
  `mFourierCoeff` as an integral over a fundamental box `∏ i, (aᵢ, aᵢ + 1] ⊆ ℝᵈ`, with respect
  to the ordinary pi volume.

The missing piece, supplied here as `paper2_mFourierCoeff_periodization`, is the multivariate
analogue of `Real.fourierCoeff_tsum_comp_add`: the `n`-th Fourier coefficient of the
periodization `x ↦ ∑' m : ℤᵈ, f (x + m)` is the Fourier transform of `f` at `n`.  Its proof
follows the one-dimensional calc block step for step — unwind the coefficient to an integral
over the fundamental box, push the sum through the integrand, swap sum and integral using a
locally-summable-norm hypothesis, absorb the character into the translate, and reassemble the
sum of box integrals into a single integral over `ℝᵈ`.

Three remarks on the mathlib API this rests on.

* `Mathlib/Analysis/Fourier/AddCircleMulti.lean` installs `MeasureSpace UnitAddCircle` as a
  *local* instance, so no downstream file can state anything about `volume` on
  `UnitAddTorus d`.  This is not an obstruction: the three results consumed here have
  measure-free statements, and `mFourierCoeff_eq_integral` hands back an integral over a box
  in `ℝᵈ` with the ordinary pi volume.  All measure theory below therefore happens on `ℝᵈ`.
* `UnitAddTorus d = d → UnitAddCircle` carries the *product* topology, not a coinduced one, so
  the one-dimensional descent argument (`continuous_coinduced_dom`) does not transfer.  The
  replacement is `IsOpenQuotientMap.piMap` applied to `QuotientAddGroup.isOpenQuotientMap_mk`:
  a finite product of open quotient maps is an open quotient map, and an open quotient map is a
  quotient map.
* `WithLp` is a structure, so `EuclideanSpace ℝ d` is not defeq to `d → ℝ` and the `𝓕`
  notation is unavailable here.  The Fourier transform is therefore written as an explicit
  integral against `paper2Char`, with `paper2_integral_char_mul_eq_fourierIntegral` identifying
  it with `VectorFourier.fourierIntegral` against the standard dot pairing, and
  `paper2Char_apply` giving the explicit exponential.

Nothing in this file is specific to Paper 2's quadratic form; `Ch10_Paper2_Poisson2D` proves the
much weaker product case and is not used.
-/

namespace QseriesFormalization
namespace Ch10

open MeasureTheory
open scoped Real

noncomputable section

variable {d : Type*} [Fintype d]

/-! ## §1 The lattice, the fundamental box, and the tiling of `ℝᵈ` -/

/-- The embedding of the lattice `ℤᵈ` into `ℝᵈ`. -/
def paper2LatticeVec (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)

omit [Fintype d] in
@[simp]
theorem paper2LatticeVec_apply (n : d → ℤ) (i : d) : paper2LatticeVec n i = (n i : ℝ) := rfl

omit [Fintype d] in
@[simp]
theorem paper2LatticeVec_zero : paper2LatticeVec (0 : d → ℤ) = 0 := by
  funext i; simp [paper2LatticeVec]

omit [Fintype d] in
theorem paper2LatticeVec_add (n m : d → ℤ) :
    paper2LatticeVec (n + m) = paper2LatticeVec n + paper2LatticeVec m := by
  funext i; simp [paper2LatticeVec]

/-- Local normal summability of all lattice translates in the two-dimensional
case needed by Paper 2.  Naming this hypothesis keeps dependent proof terms
opaque in the Fourier-coefficient interface. -/
def Paper2LocallySummable2 (f : C(Fin 2 → ℝ, ℂ)) : Prop :=
  ∀ K : TopologicalSpace.Compacts (Fin 2 → ℝ), Summable fun n : Fin 2 → ℤ =>
    ‖(f.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict K‖

theorem Paper2LocallySummable2.apply {f : C(Fin 2 → ℝ, ℂ)}
    (hf : Paper2LocallySummable2 f) (K : TopologicalSpace.Compacts (Fin 2 → ℝ)) :
    Summable fun n : Fin 2 → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict K‖ :=
  hf K

/-- The half-open fundamental box `∏ i, (aᵢ, aᵢ + 1] ⊆ ℝᵈ`, written in exactly the form
`UnitAddTorus.mFourierCoeff_eq_integral` produces. -/
def paper2Box (a : d → ℝ) : Set (d → ℝ) := {x : d → ℝ | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)}

omit [Fintype d] in theorem paper2Box_eq_pi (a : d → ℝ) :
    paper2Box a = Set.univ.pi fun i : d => Set.Ioc (a i) (a i + 1) := by
  ext x
  simp only [paper2Box, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]

theorem measurableSet_paper2Box (a : d → ℝ) : MeasurableSet (paper2Box a) := by
  rw [paper2Box_eq_pi, Set.univ_pi_eq_iInter]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ioc.preimage (measurable_pi_apply i)

theorem volume_paper2Box (a : d → ℝ) : volume (paper2Box a) = 1 := by
  rw [paper2Box_eq_pi, volume_pi_pi]
  simp [Real.volume_Ioc]

theorem paper2_pairwise_disjoint_box (d : Type*) [Fintype d] :
    Pairwise fun n m : d → ℤ =>
      Disjoint (paper2Box (paper2LatticeVec n)) (paper2Box (paper2LatticeVec m)) := by
  intro n m hnm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hnm
  refine Set.disjoint_left.2 fun x hxn hxm => ?_
  have h1 : x i ∈ Set.Ioc ((0 : ℝ) + (n i : ℝ)) ((0 : ℝ) + (n i : ℝ) + 1) := by
    simpa using hxn i
  have h2 : x i ∈ Set.Ioc ((0 : ℝ) + (m i : ℝ)) ((0 : ℝ) + (m i : ℝ) + 1) := by
    simpa using hxm i
  exact Set.disjoint_left.1 (Set.pairwise_disjoint_Ioc_add_intCast (0 : ℝ) hi) h1 h2

theorem paper2_iUnion_box (d : Type*) [Fintype d] :
    (⋃ n : d → ℤ, paper2Box (paper2LatticeVec n)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have h : ∀ i : d, ∃ k : ℤ, x i ∈ Set.Ioc ((k : ℝ)) ((k : ℝ) + 1) := by
    intro i
    have hx : x i ∈ ⋃ k : ℤ, Set.Ioc ((k : ℝ)) ((k : ℝ) + 1) := by
      rw [iUnion_Ioc_intCast ℝ]; trivial
    exact Set.mem_iUnion.mp hx
  choose k hk using h
  exact Set.mem_iUnion.2 ⟨k, fun i => hk i⟩

/-- The closed box `∏ i, [aᵢ, aᵢ + 1]`, as a compact set. -/
def paper2ClosedBox (a : d → ℝ) : TopologicalSpace.Compacts (d → ℝ) where
  carrier := Set.univ.pi fun i => Set.Icc (a i) (a i + 1)
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc

omit [Fintype d] in theorem paper2_mem_closedBox {a x : d → ℝ} :
    x ∈ (paper2ClosedBox a : Set (d → ℝ)) ↔ ∀ i, x i ∈ Set.Icc (a i) (a i + 1) := by
  simp only [paper2ClosedBox, TopologicalSpace.Compacts.coe_mk, Set.mem_pi, Set.mem_univ,
    forall_const]

omit [Fintype d] in theorem paper2Box_subset_closedBox (a : d → ℝ) :
    paper2Box a ⊆ (paper2ClosedBox a : Set (d → ℝ)) := by
  intro x hx
  rw [paper2_mem_closedBox]
  exact fun i => Set.Ioc_subset_Icc_self (hx i)

theorem volume_paper2ClosedBox (a : d → ℝ) :
    volume ((paper2ClosedBox a : Set (d → ℝ))) = 1 := by
  show volume (Set.univ.pi fun i => Set.Icc (a i) (a i + 1)) = 1
  rw [volume_pi_pi]
  simp [Real.volume_Icc]

theorem measureReal_paper2ClosedBox (a : d → ℝ) :
    (volume : Measure (d → ℝ)).real ((paper2ClosedBox a : Set (d → ℝ))) = 1 := by
  rw [measureReal_def, volume_paper2ClosedBox]
  simp

theorem paper2_iUnion_closedBox (d : Type*) [Fintype d] :
    (⋃ n : d → ℤ, (paper2ClosedBox (paper2LatticeVec n) : Set (d → ℝ))) = Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← paper2_iUnion_box d]
  exact Set.iUnion_mono fun n => paper2Box_subset_closedBox _

/-! ## §2 Reassembling box integrals into an integral over `ℝᵈ` -/

/-- The multivariate analogue of `MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int`:
the integrals of the lattice translates of `g` over the fundamental box sum to the integral of
`g` over `ℝᵈ`. -/
theorem paper2_hasSum_setIntegral_box {g : (d → ℝ) → ℂ} (hg : Integrable g) :
    HasSum (fun n : d → ℤ => ∫ x in paper2Box (0 : d → ℝ), g (x + paper2LatticeVec n))
      (∫ x, g x) := by
  have key : ∀ n : d → ℤ,
      (∫ x in paper2Box (0 : d → ℝ), g (x + paper2LatticeVec n))
        = ∫ x in paper2Box (paper2LatticeVec n), g x := by
    intro n
    have hmp : MeasurePreserving (fun x : d → ℝ => x + paper2LatticeVec n)
        (volume : Measure (d → ℝ)) volume :=
      measurePreserving_add_right volume (paper2LatticeVec n)
    have hme : MeasurableEmbedding (fun x : d → ℝ => x + paper2LatticeVec n) :=
      (MeasurableEquiv.addRight (paper2LatticeVec n)).measurableEmbedding
    have hpre : (fun x : d → ℝ => x + paper2LatticeVec n) ⁻¹' paper2Box (paper2LatticeVec n)
        = paper2Box (0 : d → ℝ) := by
      ext x
      simp only [Set.mem_preimage, paper2Box, Set.mem_setOf_eq, Pi.add_apply,
        paper2LatticeVec_apply, Pi.zero_apply, Set.mem_Ioc]
      constructor
      · intro h i
        obtain ⟨h1, h2⟩ := h i
        constructor <;> linarith
      · intro h i
        obtain ⟨h1, h2⟩ := h i
        constructor <;> linarith
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb hme g _
  simp_rw [key]
  have hcover := paper2_iUnion_box d
  have hint : IntegrableOn g (⋃ n : d → ℤ, paper2Box (paper2LatticeVec n)) volume := by
    rw [hcover]
    exact hg.integrableOn
  have h := hasSum_integral_iUnion (μ := (volume : Measure (d → ℝ))) (f := g)
    (fun n : d → ℤ => measurableSet_paper2Box (paper2LatticeVec n))
    (paper2_pairwise_disjoint_box d) hint
  rwa [hcover, setIntegral_univ] at h

/-- The multivariate analogue of `Real.integrable_of_summable_norm_Icc`. -/
theorem paper2_integrable_of_summable_norm_box {g : C(d → ℝ, ℂ)}
    (hg : Summable fun n : d → ℤ =>
      ‖(g.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict
        (paper2ClosedBox (0 : d → ℝ))‖) :
    Integrable g := by
  refine integrable_of_summable_norm_restrict
    (s := fun n : d → ℤ => paper2ClosedBox (paper2LatticeVec n))
    (Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) measureReal_nonneg)
      (fun n => ?_) hg) (paper2_iUnion_closedBox d)
  rw [measureReal_paper2ClosedBox, mul_one, ContinuousMap.norm_le _ (norm_nonneg _)]
  rintro ⟨z, hz⟩
  rw [paper2_mem_closedBox] at hz
  have hz' : z - paper2LatticeVec n ∈ (paper2ClosedBox (0 : d → ℝ) : Set (d → ℝ)) := by
    rw [paper2_mem_closedBox]
    intro i
    obtain ⟨h1, h2⟩ := hz i
    simp only [Pi.sub_apply, paper2LatticeVec_apply, Pi.zero_apply, Set.mem_Icc, zero_add] at *
    constructor <;> linarith
  have h := ContinuousMap.norm_coe_le_norm
    ((g.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict
      ((paper2ClosedBox (0 : d → ℝ)) : Set (d → ℝ))) ⟨z - paper2LatticeVec n, hz'⟩
  simpa only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_addRight, sub_add_cancel] using h

/-- Pointwise sum of a family of continuous functions; naming it keeps the
dominated-convergence statement from unfolding the continuous-map coercions. -/
def paper2PointwiseTsum {ι : Type*} (F : ι → C(d → ℝ, ℂ)) (x : d → ℝ) : ℂ :=
  ∑' i : ι, F i x

/-- Integration over the fixed fundamental box, named to keep the theorem
signatures below opaque to the elaborator. -/
def paper2BoxIntegral (g : (d → ℝ) → ℂ) : ℂ :=
  ∫ x in paper2Box (0 : d → ℝ), g x

/-- Dimension-two specialization of the pointwise sum. -/
def paper2PointwiseTsum2
    (F : (Fin 2 → ℤ) → C(Fin 2 → ℝ, ℂ))
    (x : Fin 2 → ℝ) : ℂ :=
  ∑' i : Fin 2 → ℤ, F i x

/-- Dimension-two specialization of integration over the fundamental box. -/
def paper2BoxIntegral2 (g : (Fin 2 → ℝ) → ℂ) : ℂ :=
  ∫ x in paper2Box (0 : Fin 2 → ℝ), g x

/-- The general-measure analogue of
`intervalIntegral.hasSum_intervalIntegral_of_summable_norm`, on the fundamental box. -/
theorem paper2_hasSum_setIntegral_of_summable_norm
    (F : (Fin 2 → ℤ) → C(Fin 2 → ℝ, ℂ))
    (hF : Summable fun i : Fin 2 → ℤ =>
      ‖(F i).restrict (paper2ClosedBox (0 : Fin 2 → ℝ))‖) :
    HasSum (fun i : Fin 2 → ℤ => paper2BoxIntegral2 (F i))
      (paper2BoxIntegral2 (paper2PointwiseTsum2 F)) := by
  unfold paper2BoxIntegral2
  haveI : IsFiniteMeasure ((volume : Measure (Fin 2 → ℝ)).restrict
      (paper2Box (0 : Fin 2 → ℝ))) := by
    constructor
    rw [Measure.restrict_apply_univ, volume_paper2Box]
    exact ENNReal.one_lt_top
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun i (_ : Fin 2 → ℝ) =>
      ‖(F i).restrict (paper2ClosedBox (0 : Fin 2 → ℝ))‖)
    (fun i => (map_continuous (F i)).aestronglyMeasurable)
  · intro i
    filter_upwards [ae_restrict_mem
      (measurableSet_paper2Box (0 : Fin 2 → ℝ))] with x hx
    have h := ContinuousMap.norm_coe_le_norm
      ((F i).restrict ((paper2ClosedBox (0 : Fin 2 → ℝ)) :
        Set (Fin 2 → ℝ)))
      ⟨x, paper2Box_subset_closedBox _ hx⟩
    simpa only [ContinuousMap.restrict_apply] using h
  · exact Filter.Eventually.of_forall fun _ => hF
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem
      (measurableSet_paper2Box (0 : Fin 2 → ℝ))] with x hx
    have hsum : Summable fun i : Fin 2 → ℤ => F i x := by
      have h := ContinuousMap.summable_apply hF.of_norm
        (⟨x, paper2Box_subset_closedBox _ hx⟩ :
          ((paper2ClosedBox (0 : Fin 2 → ℝ)) :
            Set (Fin 2 → ℝ)))
      simpa only [ContinuousMap.restrict_apply] using h
    simpa only [paper2PointwiseTsum2] using hsum.hasSum

/-! ## §3 The quotient map `ℝᵈ → 𝕋ᵈ` and the descent of lattice-invariant functions -/

/-- The projection `ℝᵈ → 𝕋ᵈ`. -/
def paper2TorusProj (d : Type*) [Fintype d] : C(d → ℝ, UnitAddTorus d) where
  toFun x := fun i => ((x i : ℝ) : UnitAddCircle)
  continuous_toFun := continuous_pi fun i => continuous_quotient_mk'.comp (continuous_apply i)

@[simp]
theorem paper2TorusProj_apply (x : d → ℝ) (i : d) :
    paper2TorusProj d x i = ((x i : ℝ) : UnitAddCircle) := rfl

theorem paper2_isOpenQuotientMap_torusProj (d : Type*) [Fintype d] :
    IsOpenQuotientMap (paper2TorusProj d) := by
  have h : IsOpenQuotientMap
      (Pi.map fun _ : d => fun x : ℝ => ((x : ℝ) : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  exact h

theorem paper2_coe_eq_coe_iff {a b : ℝ} :
    ((a : ℝ) : UnitAddCircle) = ((b : ℝ) : UnitAddCircle) ↔ ∃ k : ℤ, a = b + k := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff (p := (1 : ℝ))]
  constructor
  · rintro ⟨n, hn⟩
    rw [zsmul_eq_mul, mul_one] at hn
    exact ⟨n, by linarith⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one, hk]
    ring

theorem paper2_torusProj_eq_iff {x y : d → ℝ} :
    paper2TorusProj d x = paper2TorusProj d y ↔ ∃ m : d → ℤ, x = y + paper2LatticeVec m := by
  constructor
  · intro h
    have h' : ∀ i : d, ∃ k : ℤ, x i = y i + k := fun i =>
      paper2_coe_eq_coe_iff.mp (congrFun h i)
    choose m hm using h'
    exact ⟨m, funext fun i => by simpa using hm i⟩
  · rintro ⟨m, rfl⟩
    funext i
    exact paper2_coe_eq_coe_iff.mpr ⟨m i, rfl⟩

theorem paper2_torusProj_surjective (d : Type*) [Fintype d] :
    Function.Surjective (paper2TorusProj d) :=
  (paper2_isOpenQuotientMap_torusProj d).surjective

/-- A section of `paper2TorusProj`, obtained from surjectivity. -/
def paper2Rep (z : UnitAddTorus d) : d → ℝ :=
  Function.surjInv (paper2_torusProj_surjective d) z

theorem paper2_torusProj_rep (z : UnitAddTorus d) : paper2TorusProj d (paper2Rep z) = z :=
  Function.surjInv_eq _ z

/-- The descent of a function on `ℝᵈ` to the torus, along the section `paper2Rep`.  It is the
genuine descent exactly when the function is lattice-invariant; see `paper2_descend_comp`. -/
def paper2Descend (P : (d → ℝ) → ℂ) : UnitAddTorus d → ℂ := fun z => P (paper2Rep z)

theorem paper2_descend_comp {P : (d → ℝ) → ℂ}
    (hP : ∀ (m : d → ℤ) (x : d → ℝ), P (x + paper2LatticeVec m) = P x) (x : d → ℝ) :
    paper2Descend P (paper2TorusProj d x) = P x := by
  obtain ⟨m, hm⟩ := paper2_torusProj_eq_iff.mp (paper2_torusProj_rep (paper2TorusProj d x))
  rw [paper2Descend, hm, hP]

/-- The descent of a lattice-invariant continuous function, as a continuous map on the torus.
Continuity comes from `paper2TorusProj` being an open quotient map. -/
def paper2DescendC (P : C(d → ℝ, ℂ))
    (hP : ∀ (m : d → ℤ) (x : d → ℝ), P (x + paper2LatticeVec m) = P x) :
    C(UnitAddTorus d, ℂ) where
  toFun := paper2Descend (P : (d → ℝ) → ℂ)
  continuous_toFun := by
    rw [← (paper2_isOpenQuotientMap_torusProj d).continuous_comp_iff]
    have h : paper2Descend (P : (d → ℝ) → ℂ) ∘ (paper2TorusProj d) = (P : (d → ℝ) → ℂ) :=
      funext fun x => paper2_descend_comp hP x
    rw [h]
    exact P.continuous

@[simp]
theorem paper2DescendC_apply (P : C(d → ℝ, ℂ))
    (hP : ∀ (m : d → ℤ) (x : d → ℝ), P (x + paper2LatticeVec m) = P x) (z : UnitAddTorus d) :
    paper2DescendC P hP z = paper2Descend (P : (d → ℝ) → ℂ) z := rfl

/-! ## §4 The periodization and the lattice character -/

/-- The periodization `x ↦ ∑' n : ℤᵈ, f (x + n)`, as a continuous map. -/
def paper2Periodization (f : C(d → ℝ, ℂ)) : C(d → ℝ, ℂ) :=
  ∑' n : d → ℤ, f.comp (ContinuousMap.addRight (paper2LatticeVec n))

theorem paper2_summable_comp_addRight {f : C(d → ℝ, ℂ)}
    (hf : ∀ K : TopologicalSpace.Compacts (d → ℝ), Summable fun n : d → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict K‖) :
    Summable fun n : d → ℤ => f.comp (ContinuousMap.addRight (paper2LatticeVec n)) :=
  ContinuousMap.summable_of_locally_summable_norm hf

theorem paper2_periodization_apply {f : C(d → ℝ, ℂ)}
    (hf : ∀ K : TopologicalSpace.Compacts (d → ℝ), Summable fun n : d → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict K‖) (x : d → ℝ) :
    paper2Periodization f x = ∑' n : d → ℤ, f (x + paper2LatticeVec n) := by
  rw [paper2Periodization, ← ContinuousMap.tsum_apply (paper2_summable_comp_addRight hf) x]
  exact tsum_congr fun _ => rfl

theorem paper2_periodization_add_lattice {f : C(d → ℝ, ℂ)}
    (hf : ∀ K : TopologicalSpace.Compacts (d → ℝ), Summable fun n : d → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict K‖)
    (m : d → ℤ) (x : d → ℝ) :
    paper2Periodization f (x + paper2LatticeVec m) = paper2Periodization f x := by
  rw [paper2_periodization_apply hf, paper2_periodization_apply hf]
  have hre : ∀ n : d → ℤ,
      x + paper2LatticeVec m + paper2LatticeVec n = x + paper2LatticeVec (n + m) := by
    intro n
    rw [paper2LatticeVec_add]
    abel
  simp_rw [hre]
  exact (Equiv.addRight m).tsum_eq fun n : d → ℤ => f (x + paper2LatticeVec n)

/-- The lattice character `x ↦ e^{-2πi⟨n, x⟩}`, as the pullback of `mFourier (-n)` along the
projection to the torus. -/
def paper2Char (n : d → ℤ) : C(d → ℝ, ℂ) :=
  (UnitAddTorus.mFourier (-n)).comp (paper2TorusProj d)

theorem paper2Char_apply (n : d → ℤ) (x : d → ℝ) :
    paper2Char n x
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i : d, (n i : ℂ) * (x i : ℂ)) := by
  have hfac : ∀ i : d, fourier ((-n) i) ((x i : ℝ) : UnitAddCircle)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((n i : ℂ) * (x i : ℂ))) := by
    intro i
    rw [fourier_coe_apply]
    congr 1
    simp only [Pi.neg_apply]
    push_cast
    ring
  simp only [paper2Char, ContinuousMap.comp_apply, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    paper2TorusProj_apply, hfac]
  rw [← Complex.exp_sum, Finset.mul_sum]

theorem norm_paper2Char (n : d → ℤ) (x : d → ℝ) : ‖paper2Char n x‖ = 1 := by
  simp only [paper2Char, ContinuousMap.comp_apply, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem paper2_torusProj_add_lattice (m : d → ℤ) (x : d → ℝ) :
    paper2TorusProj d (x + paper2LatticeVec m) = paper2TorusProj d x :=
  paper2_torusProj_eq_iff.mpr ⟨m, rfl⟩

theorem paper2Char_comp_addRight (n m : d → ℤ) :
    (paper2Char n).comp (ContinuousMap.addRight (paper2LatticeVec m)) = paper2Char n := by
  ext x
  show UnitAddTorus.mFourier (-n) (paper2TorusProj d (x + paper2LatticeVec m))
    = UnitAddTorus.mFourier (-n) (paper2TorusProj d x)
  rw [paper2_torusProj_add_lattice]

theorem norm_restrict_paper2Char_mul (n : d → ℤ) (K : TopologicalSpace.Compacts (d → ℝ))
    (g : C(d → ℝ, ℂ)) : ‖(paper2Char n * g).restrict K‖ = ‖g.restrict K‖ := by
  simp_rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.restrict_apply,
    ContinuousMap.mul_apply, norm_mul, norm_paper2Char, one_mul]

/-! ## §5 The Fourier coefficient of the periodization

This is the multivariate analogue of `Real.fourierCoeff_tsum_comp_add`. -/

/-- The continuous function on the torus obtained by descending the lattice
periodization.  Naming it prevents repeated unfolding of the quotient descent
inside Fourier-coefficient theorem signatures. -/
def paper2PeriodizationTorus {f : C(d → ℝ, ℂ)}
    (hf : ∀ K : TopologicalSpace.Compacts (d → ℝ), Summable fun n : d → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (paper2LatticeVec n))).restrict K‖) :
    C(UnitAddTorus d, ℂ) :=
  paper2DescendC (paper2Periodization f) (paper2_periodization_add_lattice hf)

/-- Dimension-two specialization of the descended periodization. -/
def paper2PeriodizationTorus2 (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f) :
    C(UnitAddTorus (Fin 2), ℂ) :=
  paper2DescendC (paper2Periodization f)
    (paper2_periodization_add_lattice fun K => hf.apply K)

theorem paper2_summable_char_translates (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f)
    (n : Fin 2 → ℤ) : Summable fun m : Fin 2 → ℤ =>
      ‖((paper2Char n * f).comp (ContinuousMap.addRight (paper2LatticeVec m))).restrict
        (paper2ClosedBox (0 : Fin 2 → ℝ))‖ := by
  have hrw : ∀ m : Fin 2 → ℤ,
      ((paper2Char n * f).comp (ContinuousMap.addRight (paper2LatticeVec m)))
        = paper2Char n * f.comp (ContinuousMap.addRight (paper2LatticeVec m)) := by
    intro m
    rw [ContinuousMap.mul_comp, paper2Char_comp_addRight]
  simp_rw [hrw, norm_restrict_paper2Char_mul]
  exact hf.apply (paper2ClosedBox (0 : Fin 2 → ℝ))

theorem paper2_integrable_char_mul (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f)
    (n : Fin 2 → ℤ) : Integrable ((paper2Char n * f : C(Fin 2 → ℝ, ℂ)) :
      (Fin 2 → ℝ) → ℂ) :=
  paper2_integrable_of_summable_norm_box (paper2_summable_char_translates f hf n)

theorem paper2_mFourierCoeff_periodization_box (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f)
    (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (paper2PeriodizationTorus2 f hf) n
      = ∫ x in paper2Box (0 : Fin 2 → ℝ),
          paper2Char n x * paper2Periodization f x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ n (0 : Fin 2 → ℝ)]
  refine setIntegral_congr_fun
    (measurableSet_paper2Box (0 : Fin 2 → ℝ)) fun x _ => ?_
  show UnitAddTorus.mFourier (-n) (paper2TorusProj (Fin 2) x) •
      paper2PeriodizationTorus2 f hf (paper2TorusProj (Fin 2) x)
    = paper2Char n x * paper2Periodization f x
  rw [paper2PeriodizationTorus2, paper2DescendC_apply,
    paper2_descend_comp (paper2_periodization_add_lattice fun K => hf.apply K) x,
    smul_eq_mul]
  rfl

theorem paper2_integral_char_periodization_eq_tsum (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f)
    (n : Fin 2 → ℤ) :
    (∫ x in paper2Box (0 : Fin 2 → ℝ), paper2Char n x * paper2Periodization f x) =
      ∫ x in paper2Box (0 : Fin 2 → ℝ), ∑' m : Fin 2 → ℤ,
        (paper2Char n * f.comp (ContinuousMap.addRight (paper2LatticeVec m))) x := by
  refine setIntegral_congr_fun
    (measurableSet_paper2Box (0 : Fin 2 → ℝ)) fun x _ => ?_
  rw [paper2Periodization,
    ← ContinuousMap.tsum_apply (paper2_summable_comp_addRight fun K => hf.apply K) x,
    ← tsum_mul_left]
  rfl

theorem paper2_integral_tsum_char_eq_tsum_integrals (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f)
    (n : Fin 2 → ℤ) :
    (∫ x in paper2Box (0 : Fin 2 → ℝ), ∑' m : Fin 2 → ℤ,
        (paper2Char n * f.comp (ContinuousMap.addRight (paper2LatticeVec m))) x) =
      ∑' m : Fin 2 → ℤ, ∫ x in paper2Box (0 : Fin 2 → ℝ),
        (paper2Char n * f.comp (ContinuousMap.addRight (paper2LatticeVec m))) x := by
  refine (paper2_hasSum_setIntegral_of_summable_norm
    (fun m => paper2Char n * f.comp (ContinuousMap.addRight (paper2LatticeVec m))) ?_).tsum_eq.symm
  simp_rw [norm_restrict_paper2Char_mul]
  exact hf.apply (paper2ClosedBox (0 : Fin 2 → ℝ))

theorem paper2_tsum_char_integrals_eq_translates (f : C(Fin 2 → ℝ, ℂ))
    (n : Fin 2 → ℤ) :
    (∑' m : Fin 2 → ℤ, ∫ x in paper2Box (0 : Fin 2 → ℝ),
        (paper2Char n * f.comp (ContinuousMap.addRight (paper2LatticeVec m))) x) =
      ∑' m : Fin 2 → ℤ, ∫ x in paper2Box (0 : Fin 2 → ℝ),
        (paper2Char n * f) (x + paper2LatticeVec m) := by
  refine tsum_congr fun m => ?_
  refine setIntegral_congr_fun
    (measurableSet_paper2Box (0 : Fin 2 → ℝ)) fun x _ => ?_
  have h : ((paper2Char n * f).comp (ContinuousMap.addRight (paper2LatticeVec m)))
      = paper2Char n * f.comp (ContinuousMap.addRight (paper2LatticeVec m)) := by
    rw [ContinuousMap.mul_comp, paper2Char_comp_addRight]
  exact congrFun
    (congrArg (fun g : C(Fin 2 → ℝ, ℂ) => (g : (Fin 2 → ℝ) → ℂ)) h.symm) x

theorem paper2_tsum_char_translates_eq_integral (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f)
    (n : Fin 2 → ℤ) :
    (∑' m : Fin 2 → ℤ, ∫ x in paper2Box (0 : Fin 2 → ℝ),
        (paper2Char n * f) (x + paper2LatticeVec m)) =
      ∫ x : Fin 2 → ℝ, paper2Char n x * f x :=
  (paper2_hasSum_setIntegral_box (paper2_integrable_char_mul f hf n)).tsum_eq

theorem paper2_mFourierCoeff_periodization (f : C(Fin 2 → ℝ, ℂ))
    (hf : Paper2LocallySummable2 f)
    (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (paper2PeriodizationTorus2 f hf) n
      = ∫ x : Fin 2 → ℝ, paper2Char n x * f x := by
  rw [paper2_mFourierCoeff_periodization_box f hf n,
    paper2_integral_char_periodization_eq_tsum f hf n,
    paper2_integral_tsum_char_eq_tsum_integrals f hf n,
    paper2_tsum_char_integrals_eq_translates f n,
    paper2_tsum_char_translates_eq_integral f hf n]

/-! ## §6 Poisson summation on the lattice -/

/-- **Poisson summation on the square lattice `ℤ²`**.  If the translates of `f` are
locally normally summable and the Fourier transform of `f` is summable along the lattice, then
the periodization of `f` is the sum of its multivariate Fourier series. -/
theorem paper2_tsum_lattice_eq_tsum_fourier
    {f : C(Fin 2 → ℝ, ℂ)}
    (hf : Paper2LocallySummable2 f)
    (h_sum : Summable fun n : Fin 2 → ℤ =>
      ∫ y : Fin 2 → ℝ, paper2Char n y * f y)
    (x : Fin 2 → ℝ) :
    ∑' n : Fin 2 → ℤ, f (x + paper2LatticeVec n)
      = ∑' m : Fin 2 → ℤ,
        (∫ y : Fin 2 → ℝ, paper2Char m y * f y) *
          UnitAddTorus.mFourier m (paper2TorusProj (Fin 2) x) := by
  have hcoeff : ∀ m : Fin 2 → ℤ,
      UnitAddTorus.mFourierCoeff
        (paper2PeriodizationTorus2 f hf) m
        = ∫ y : Fin 2 → ℝ, paper2Char m y * f y :=
    fun m => paper2_mFourierCoeff_periodization f hf m
  have hsummable : Summable (UnitAddTorus.mFourierCoeff
      (paper2PeriodizationTorus2 f hf)) := by
    exact h_sum.congr fun m => (hcoeff m).symm
  have hpt := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsummable
    (paper2TorusProj (Fin 2) x)
  have hL : (paper2PeriodizationTorus2 f hf)
      (paper2TorusProj (Fin 2) x) =
        ∑' n : Fin 2 → ℤ, f (x + paper2LatticeVec n) := by
    rw [paper2PeriodizationTorus2, paper2DescendC_apply,
      paper2_descend_comp (paper2_periodization_add_lattice fun K => hf.apply K) x]
    exact paper2_periodization_apply (fun K => hf.apply K) x
  rw [← hL, ← hpt.tsum_eq]
  exact tsum_congr fun m => by rw [hcoeff m, smul_eq_mul]

/-! ## The Fourier transform in mathlib's `VectorFourier` form -/

/-- The standard dot pairing on `ℝᵈ`, as a bilinear map. -/
def paper2DotL (d : Type*) [Fintype d] : (d → ℝ) →ₗ[ℝ] (d → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i : d, x i * y i)
    (fun x y z => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun x y z => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm])

@[simp]
theorem paper2DotL_apply (x y : d → ℝ) : paper2DotL d x y = ∑ i : d, x i * y i := rfl

/-- The integral against `paper2Char n` is the Fourier transform of `f` at the lattice point
`n`, in mathlib's `VectorFourier.fourierIntegral` form for the standard dot pairing. -/
theorem paper2_integral_char_mul_eq_fourierIntegral (f : C(d → ℝ, ℂ)) (n : d → ℤ) :
    (∫ x : d → ℝ, paper2Char n x * f x)
      = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure (d → ℝ))
          (paper2DotL d) (f : (d → ℝ) → ℂ) (paper2LatticeVec n) := by
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change paper2Char n x * f x =
    Complex.exp (((-2 * Real.pi * paper2DotL d x (paper2LatticeVec n) : ℝ) : ℂ) *
      Complex.I) * f x
  rw [paper2Char_apply]
  congr 2
  have hcast : ((∑ i : d, x i * (paper2LatticeVec n) i : ℝ) : ℂ)
      = ∑ i : d, (n i : ℂ) * (x i : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [paper2DotL_apply]
  push_cast [← hcast]
  ring

end

end Ch10
end QseriesFormalization
