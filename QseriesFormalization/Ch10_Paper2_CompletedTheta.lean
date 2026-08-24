import QseriesFormalization.Ch10_Paper2_ErrorKernel
import QseriesFormalization.Ch10_Paper2_UnaryTheta
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Paper 2: the completed `c₂` correction series

Paper 2 splits the index-four boundary lattice at `c₂=(5,1)` by the
coordinates `n = 5x+15y+4` and `T = 3x+5y+2` associated with the orthogonal
vector `e₂=(3,-1)`.  In these coordinates the shifted quadratic form is
`Q₀(v) = T²/8 - n²/40`, the lattice character is `(-1)^j`, and the surviving
Zwegers correction attached to `c₂` is `E(-n√(Y/10)) - sgn(-n)`.

This file makes that data analytic.  It records the coordinate dictionary as
proved arithmetic identities, defines the longitudinal correction summands
`(E(-n√(Y/10)) - sgn(-n)) q^{-n²/40}` filtered by the residue class
`n ≡ 5j+4 (mod 20)`, and proves that each such series converges absolutely on
the upper half-plane.  The growth `|q^{-n²/40}| = e^{πn²Y/20}` is beaten by
the Gaussian tail bound of `Ch10_Paper2_ErrorKernel`, which decays like
`e^{-πn²Y/10}`; the surviving majorant is `e^{-πn²Y/20}`.

With both factors absolutely convergent, each residue block of the `c₂`
correction factors exactly as a product of the transverse unary theta
component and the longitudinal correction component.  Zwegers' completion
theorem itself, and hence the identification of the assembled expression with
the analytic boundary correction of `F̂`, is not formalized here.
-/

namespace QseriesFormalization
namespace Ch10

open Complex Filter

noncomputable section

/-! ## The `(n,T)` boundary coordinates

All statements in this section are exact transcriptions of the displayed
formulas of Paper 2 between the definition of `e₂=(3,-1)` and the definition
of `θ_j`, `g_j`. -/

/-- Paper 2's longitudinal coordinate `n = 5x+15y+4` along `c₂`. -/
def paper2LongCoord (x y : ℤ) : ℤ := 5 * x + 15 * y + 4

/-- Paper 2's transverse coordinate `T = 3x+5y+2` along `e₂=(3,-1)`. -/
def paper2TransCoord (x y : ℤ) : ℤ := 3 * x + 5 * y + 2

/-- The residue label of the four boundary cosets, `j ≡ x+3y (mod 4)`. -/
def paper2CosetLabel (x y : ℤ) : ℤ := x + 3 * y

/-- Paper 2's ambient quadratic form `Q₀(X,Y) = ½(X²-5Y²)`. -/
def paper2Q0 (X Y : ℝ) : ℝ := (X ^ 2 - 5 * Y ^ 2) / 2

/-- The longitudinal residue condition `n ≡ 5j+4 (mod 20)` holds for the
coordinate `n` of every lattice point. -/
theorem paper2GResidue_longCoord (x y : ℤ) :
    paper2GResidue (paper2CosetLabel x y) (paper2LongCoord x y) := by
  unfold paper2GResidue paper2CosetLabel paper2LongCoord
  omega

/-- The transverse residue condition `T ≡ 3j+2 (mod 4)` holds for the
coordinate `T` of every lattice point. -/
theorem paper2ThetaResidue_transCoord (x y : ℤ) :
    paper2ThetaResidue (paper2CosetLabel x y) (paper2TransCoord x y) := by
  unfold paper2ThetaResidue paper2CosetLabel paper2TransCoord
  omega

/-- The manuscript's inverse formula `x = (3T-n-2)/4`, in cleared form. -/
theorem paper2_four_mul_fst (x y : ℤ) :
    4 * x = 3 * paper2TransCoord x y - paper2LongCoord x y - 2 := by
  unfold paper2TransCoord paper2LongCoord
  ring

/-- The manuscript's inverse formula `y = (3n-5T-2)/20`, in cleared form. -/
theorem paper2_twenty_mul_snd (x y : ℤ) :
    20 * y = 3 * paper2LongCoord x y - 5 * paper2TransCoord x y - 2 := by
  unfold paper2TransCoord paper2LongCoord
  ring

/-- The coordinate change `(x,y) ↦ (n,T)` is injective. -/
theorem paper2Coord_injective {x y x' y' : ℤ}
    (hn : paper2LongCoord x y = paper2LongCoord x' y')
    (hT : paper2TransCoord x y = paper2TransCoord x' y') :
    x = x' ∧ y = y' := by
  unfold paper2LongCoord at hn
  unfold paper2TransCoord at hT
  omega

/-- Every pair `(n,T)` satisfying the two residue conditions for a label `j`
comes from an integer lattice point.  Together with
`paper2Coord_injective`, `paper2GResidue_longCoord` and
`paper2ThetaResidue_transCoord` this is the manuscript's statement that the
integer lattice is the disjoint union of the four residue blocks. -/
theorem paper2Coord_surjective {j n T : ℤ} (hn : paper2GResidue j n)
    (hT : paper2ThetaResidue j T) :
    ∃ x y : ℤ, paper2LongCoord x y = n ∧ paper2TransCoord x y = T := by
  unfold paper2GResidue at hn
  unfold paper2ThetaResidue at hT
  obtain ⟨s, hs⟩ : ∃ s : ℤ, n = 5 * j + 4 + 20 * s :=
    ⟨(n - (5 * j + 4)) / 20, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, T = 3 * j + 2 + 4 * t :=
    ⟨(T - (3 * j + 2)) / 4, by omega⟩
  refine ⟨j + 3 * t - 5 * s, 3 * s - t, ?_, ?_⟩
  · unfold paper2LongCoord
    omega
  · unfold paper2TransCoord
    omega

/-- The residue label of a block is determined modulo `4` already by the
longitudinal coordinate `n`. -/
theorem paper2CosetLabel_unique {j j' n : ℤ} (hn : paper2GResidue j n)
    (hn' : paper2GResidue j' n) : j % 4 = j' % 4 := by
  unfold paper2GResidue at hn hn'
  omega

/-- The orthogonal decomposition value of Paper 2:
`Q₀((x,y)+a) = T²/8 - n²/40` for the characteristic `a = (1/2, 1/10)`. -/
theorem paper2Q0_shift (x y : ℤ) :
    paper2Q0 ((x : ℝ) + 1 / 2) ((y : ℝ) + 1 / 10)
      = (paper2TransCoord x y : ℝ) ^ 2 / 8 - (paper2LongCoord x y : ℝ) ^ 2 / 40 := by
  unfold paper2Q0 paper2TransCoord paper2LongCoord
  push_cast
  ring

/-- The lattice character `(-1)^{x+y}` equals `(-1)^j` for the coset label
`j = x+3y`. -/
theorem paper2Sign_eq_cosetLabel (x y : ℤ) :
    ((-1 : ℂ)) ^ (x + y) = ((-1 : ℂ)) ^ paper2CosetLabel x y := by
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  have hlabel : paper2CosetLabel x y = x + y + 2 * y := by
    unfold paper2CosetLabel
    ring
  have h2 : ((-1 : ℂ)) ^ (2 * y) = 1 := by
    rw [zpow_mul]
    norm_num
  calc ((-1 : ℂ)) ^ (x + y) = ((-1 : ℂ)) ^ (x + y) * 1 := (mul_one _).symm
    _ = ((-1 : ℂ)) ^ (x + y) * ((-1 : ℂ)) ^ (2 * y) := by rw [h2]
    _ = ((-1 : ℂ)) ^ (x + y + 2 * y) := (zpow_add₀ hne _ _).symm
    _ = ((-1 : ℂ)) ^ paper2CosetLabel x y := by rw [hlabel]

/-- Paper 2's ambient bilinear form `B₀((X,Y),(X',Y')) = XX'-5YY'`. -/
def paper2B0 (X Y X' Y' : ℝ) : ℝ := X * X' - 5 * (Y * Y')

/-- The boundary vector `c₂=(-5,3)` has `Q₀(c₂) = -10`. -/
theorem paper2Q0_c2 : paper2Q0 (-5) 3 = -10 := by
  unfold paper2Q0
  norm_num

/-- The boundary vector `c₂=(-5,3)` is `B₀`-orthogonal to `e₂=(3,-1)`. -/
theorem paper2B0_c2_e2 : paper2B0 (-5) 3 3 (-1) = 0 := by
  unfold paper2B0
  norm_num

/-- The longitudinal coordinate is minus the `c₂` pairing:
`B₀(c₂,v) = -n` for `v = (x,y)+a`. -/
theorem paper2B0_c2_shift (x y : ℤ) :
    paper2B0 (-5) 3 ((x : ℝ) + 1 / 2) ((y : ℝ) + 1 / 10)
      = -(paper2LongCoord x y : ℝ) := by
  unfold paper2B0 paper2LongCoord
  push_cast
  ring

/-- First coordinate of the orthogonal decomposition
`v = (n/20)c₂ + (T/4)e₂`. -/
theorem paper2_decomposition_fst (x y : ℤ) :
    (paper2LongCoord x y : ℝ) / 20 * (-5) + (paper2TransCoord x y : ℝ) / 4 * 3
      = (x : ℝ) + 1 / 2 := by
  unfold paper2LongCoord paper2TransCoord
  push_cast
  ring

/-- Second coordinate of the orthogonal decomposition
`v = (n/20)c₂ + (T/4)e₂`. -/
theorem paper2_decomposition_snd (x y : ℤ) :
    (paper2LongCoord x y : ℝ) / 20 * 3 + (paper2TransCoord x y : ℝ) / 4 * (-1)
      = (y : ℝ) + 1 / 10 := by
  unfold paper2LongCoord paper2TransCoord
  push_cast
  ring

/-- Zwegers' error-kernel argument at the boundary vector `c₂`:
`B₀(c₂,v)√Y/√(-Q₀(c₂)) = -n√(Y/10)`.  This fixes the exact constant behind
the manuscript's `E(-n√(Y/10))`. -/
theorem paper2_kernel_argument (x y : ℤ) {Y : ℝ} (hY : 0 < Y) :
    paper2B0 (-5) 3 ((x : ℝ) + 1 / 2) ((y : ℝ) + 1 / 10) * Real.sqrt Y /
        Real.sqrt (-paper2Q0 (-5) 3)
      = -(paper2LongCoord x y : ℝ) * Real.sqrt (Y / 10) := by
  have hten : -paper2Q0 (-5) 3 = 10 := by
    rw [paper2Q0_c2]
    norm_num
  rw [paper2B0_c2_shift, hten, Real.sqrt_div hY.le]
  ring

/-! ## The longitudinal nome and the surviving correction factor -/

/-- The longitudinal nome `q^{-n²/40}` with `q = e^{2πiτ}`.  This is the
factor of `q^{Q₀(v)}` carried by the `c₂` direction. -/
def paper2LongNome (n : ℤ) (τ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * τ * (-(n : ℂ) ^ 2 / 40))

/-- The longitudinal nome written with a real scalar, for norm computations. -/
theorem paper2LongNome_eq (n : ℤ) (τ : ℂ) :
    paper2LongNome n τ
      = Complex.exp ((-(Real.pi * (n : ℝ) ^ 2 / 20) : ℝ) * (Complex.I * τ)) := by
  unfold paper2LongNome
  congr 1
  push_cast
  ring

/-- Exact growth of the longitudinal nome:
`|q^{-n²/40}| = e^{πn²Y/20}` with `Y = Im τ`. -/
theorem norm_paper2LongNome (n : ℤ) (τ : ℂ) :
    ‖paper2LongNome n τ‖ = Real.exp (Real.pi * (n : ℝ) ^ 2 * τ.im / 20) := by
  have hre : (Complex.I * τ).re = -τ.im := by
    simp [Complex.mul_re]
  rw [paper2LongNome_eq, Complex.norm_exp, Complex.re_ofReal_mul, hre]
  congr 1
  ring

/-- The transverse and longitudinal nomes multiply to the full orthogonal
weight `q^{Q₀(v)} = q^{T²/8-n²/40}`. -/
theorem jacobiTheta₂_term_mul_paper2LongNome (n T : ℤ) (τ : ℂ) :
    jacobiTheta₂_term T 0 (τ / 4) * paper2LongNome n τ
      = Complex.exp (2 * Real.pi * Complex.I * τ *
          ((T : ℂ) ^ 2 / 8 - (n : ℂ) ^ 2 / 40)) := by
  rw [jacobiTheta₂_term, paper2LongNome, ← Complex.exp_add]
  congr 1
  ring

/-- The surviving `c₂` correction factor `E(-n√(Y/10)) - sgn(-n)` evaluated at
`Y = Im τ`. -/
def paper2C2Factor (n : ℤ) (τ : ℂ) : ℝ :=
  paper2BoundaryCorrection (n : ℝ) τ.im

@[simp] theorem paper2C2Factor_zero (τ : ℂ) : paper2C2Factor 0 τ = 0 := by
  simp [paper2C2Factor]

/-! ## The residue-filtered longitudinal correction series -/

/-- Summand of the longitudinal `c₂` correction
`G_j(τ) = Σ_{n≡5j+4 (20)} (E(-n√(Y/10)) - sgn(-n)) q^{-n²/40}`. -/
def paper2C2LongTerm (j n : ℤ) (τ : ℂ) : ℂ :=
  if paper2GResidue j n then (paper2C2Factor n τ : ℂ) * paper2LongNome n τ else 0

/-- Under the two residue conditions the product of a transverse summand and a
longitudinal correction summand is the correction factor times the full
orthogonal weight `q^{Q₀(v)}`. -/
theorem paper2ThetaTerm_mul_paper2C2LongTerm (j n T : ℤ) (τ : ℂ)
    (hn : paper2GResidue j n) (hT : paper2ThetaResidue j T) :
    paper2ThetaTerm j T τ * paper2C2LongTerm j n τ
      = (paper2C2Factor n τ : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * τ *
            ((T : ℂ) ^ 2 / 8 - (n : ℂ) ^ 2 / 40)) := by
  rw [paper2ThetaTerm, if_pos hT, paper2C2LongTerm, if_pos hn,
    ← jacobiTheta₂_term_mul_paper2LongNome n T τ]
  ring

/-- The Gaussian majorant used for the longitudinal series: for `c>0` the
family `n ↦ e^{-πcn²}` is summable over `ℤ`. -/
theorem summable_exp_neg_pi_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * c * (n : ℝ) ^ 2)) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) hc 0).congr fun n => ?_
  rw [pow_zero, one_mul]
  congr 1
  ring

/-- The pointwise majorant for the completed longitudinal summand.  The
Gaussian tail bound `e^{-πn²Y/10}/(π|n|√(Y/10))` beats the nome growth
`e^{πn²Y/20}`, leaving `e^{-πn²Y/20}` up to the constant
`(π√(Y/10))⁻¹`. -/
theorem norm_paper2C2LongTerm_le (j n : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖paper2C2LongTerm j n τ‖
      ≤ (Real.pi * Real.sqrt (τ.im / 10))⁻¹ *
          Real.exp (-Real.pi * (τ.im / 20) * (n : ℝ) ^ 2) := by
  have hs : 0 < Real.sqrt (τ.im / 10) := Real.sqrt_pos.2 (by positivity)
  have hπs : 0 < Real.pi * Real.sqrt (τ.im / 10) := by positivity
  by_cases hres : paper2GResidue j n
  · by_cases hn : n = 0
    · subst hn
      rw [paper2C2LongTerm, if_pos hres, paper2C2Factor_zero, Complex.ofReal_zero,
        zero_mul, norm_zero]
      positivity
    · have hcast : ((n : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hn
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rcases lt_or_gt_of_ne hn with h | h
        · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
          rw [abs_of_neg (by exact_mod_cast h)]
          linarith
        · have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ n)
          rw [abs_of_pos (by exact_mod_cast h)]
          linarith
      have hb : |paper2C2Factor n τ|
          ≤ Real.exp (-Real.pi * (n : ℝ) ^ 2 * τ.im / 10) /
              (Real.pi * (|(n : ℝ)| * Real.sqrt (τ.im / 10))) :=
        abs_paper2BoundaryCorrection_le hcast hτ
      have hexp : Real.exp (-Real.pi * (n : ℝ) ^ 2 * τ.im / 10) *
            Real.exp (Real.pi * (n : ℝ) ^ 2 * τ.im / 20)
          = Real.exp (-Real.pi * (τ.im / 20) * (n : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hden : Real.pi * Real.sqrt (τ.im / 10)
          ≤ Real.pi * (|(n : ℝ)| * Real.sqrt (τ.im / 10)) := by
        nlinarith [Real.pi_pos, hs, hn1]
      have hinv : (Real.pi * (|(n : ℝ)| * Real.sqrt (τ.im / 10)))⁻¹
          ≤ (Real.pi * Real.sqrt (τ.im / 10))⁻¹ := inv_anti₀ hπs hden
      rw [paper2C2LongTerm, if_pos hres, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, norm_paper2LongNome]
      calc |paper2C2Factor n τ| * Real.exp (Real.pi * (n : ℝ) ^ 2 * τ.im / 20)
          ≤ Real.exp (-Real.pi * (n : ℝ) ^ 2 * τ.im / 10) /
              (Real.pi * (|(n : ℝ)| * Real.sqrt (τ.im / 10))) *
              Real.exp (Real.pi * (n : ℝ) ^ 2 * τ.im / 20) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        _ = (Real.pi * (|(n : ℝ)| * Real.sqrt (τ.im / 10)))⁻¹ *
              Real.exp (-Real.pi * (τ.im / 20) * (n : ℝ) ^ 2) := by
            rw [← hexp, div_eq_inv_mul]
            ring
        _ ≤ (Real.pi * Real.sqrt (τ.im / 10))⁻¹ *
              Real.exp (-Real.pi * (τ.im / 20) * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
  · rw [paper2C2LongTerm, if_neg hres, norm_zero]
    positivity

/-- Absolute convergence of the residue-filtered longitudinal `c₂` correction
series for every `Im τ > 0`. -/
theorem summable_norm_paper2C2LongTerm (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖paper2C2LongTerm j n τ‖) := by
  have hc : 0 < τ.im / 20 := by positivity
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_paper2C2LongTerm_le j n hτ) ?_
  exact (summable_exp_neg_pi_mul_sq hc).mul_left _

/-- Summability of the residue-filtered longitudinal `c₂` correction series. -/
theorem summable_paper2C2LongTerm (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => paper2C2LongTerm j n τ) :=
  Summable.of_norm (summable_norm_paper2C2LongTerm j hτ)

/-- Absolute convergence of the transverse unary theta component. -/
theorem summable_norm_paper2ThetaTerm (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun T : ℤ => ‖paper2ThetaTerm j T τ‖) :=
  (summable_paper2ThetaTerm j hτ).norm

/-! ## The four factorized `c₂` correction components -/

/-- The longitudinal `c₂` correction component
`G_j(τ) = Σ_{n≡5j+4 (20)} (E(-n√(Y/10)) - sgn(-n)) q^{-n²/40}`. -/
def paper2C2LongComponent (j : ℤ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, paper2C2LongTerm j n τ

/-- The `j`-th factorized block of the `c₂` correction, `θ_j(τ)·G_j(τ)`. -/
def paper2C2Component (j : ℤ) (τ : ℂ) : ℂ :=
  paper2ThetaComponent j τ * paper2C2LongComponent j τ

/-- The `(T,n)` double family of a residue block is absolutely summable. -/
theorem summable_paper2C2Block (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable
      (fun z : ℤ × ℤ => paper2ThetaTerm j z.1 τ * paper2C2LongTerm j z.2 τ) := by
  have hf : Summable fun T : ℤ => ‖paper2ThetaTerm j T τ‖ :=
    summable_norm_paper2ThetaTerm j hτ
  have hg : Summable fun n : ℤ => ‖paper2C2LongTerm j n τ‖ :=
    summable_norm_paper2C2LongTerm j hτ
  exact summable_mul_of_summable_norm (R := ℂ)
    (f := fun T : ℤ => paper2ThetaTerm j T τ)
    (g := fun n : ℤ => paper2C2LongTerm j n τ) hf hg

/-- Exact factorization of the residue-`j` block of the `c₂` correction: the
double series over the orthogonal `(T,n)` coordinates is the product of the
transverse unary theta component and the longitudinal correction component. -/
theorem paper2C2Component_eq_tsum_prod (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    paper2C2Component j τ
      = ∑' z : ℤ × ℤ, paper2ThetaTerm j z.1 τ * paper2C2LongTerm j z.2 τ := by
  have hf : Summable fun T : ℤ => ‖paper2ThetaTerm j T τ‖ :=
    summable_norm_paper2ThetaTerm j hτ
  have hg : Summable fun n : ℤ => ‖paper2C2LongTerm j n τ‖ :=
    summable_norm_paper2C2LongTerm j hτ
  rw [paper2C2Component, paper2ThetaComponent, paper2C2LongComponent]
  exact tsum_mul_tsum_of_summable_norm (R := ℂ)
    (f := fun T : ℤ => paper2ThetaTerm j T τ)
    (g := fun n : ℤ => paper2C2LongTerm j n τ) hf hg

/-- The longitudinal correction summand depends only on `j mod 4`. -/
theorem paper2C2LongTerm_add_four (j n : ℤ) (τ : ℂ) :
    paper2C2LongTerm (j + 4) n τ = paper2C2LongTerm j n τ := by
  have hmod : (5 * (j + 4) + 4) % 20 = (5 * j + 4) % 20 := by omega
  simp [paper2C2LongTerm, paper2GResidue, hmod]

/-- The longitudinal correction component depends only on `j mod 4`. -/
theorem paper2C2LongComponent_add_four (j : ℤ) (τ : ℂ) :
    paper2C2LongComponent (j + 4) τ = paper2C2LongComponent j τ :=
  tsum_congr fun n => paper2C2LongTerm_add_four j n τ

/-- The factorized `c₂` block depends only on `j mod 4`, as required by the
four-coset decomposition. -/
theorem paper2C2Component_add_four (j : ℤ) (τ : ℂ) :
    paper2C2Component (j + 4) τ = paper2C2Component j τ := by
  rw [paper2C2Component, paper2C2Component, paper2ThetaComponent_add_four,
    paper2C2LongComponent_add_four]

/-- The four-component expression assembled in Paper 2's exact completion,
`½ Σ_{j=0}^{3} (-1)^j θ_j(τ) G_j(τ)`.  The factor `½` and the cancellation of
`e^{3πi/5}` against `e^{-3πi/5}` are those of the manuscript's exact
completion formula and characteristic phase.  This is a definition of that
expression; identifying it with the analytic boundary correction of `F̂`
requires Zwegers' completion theorem, which is not formalized here. -/
def paper2C2Correction (τ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2C2Component (j : ℤ) τ

/-! ## Zwegers' `c₂` correction summand on the original shifted lattice

The definitions below transcribe the `c₂` half of Definition 2.1 of Zwegers'
thesis at the manuscript's data `a = (1/2,1/10)`, `b = (1/2,-1/10)`,
`c₂ = (-5,3)`, in the ambient `(x,y)` coordinates of the shifted lattice
`a + ℤ²`.  Subtracting `sgn B₀(c₂,v)` removes the holomorphic sign part, so
what remains is exactly the nonholomorphic `c₂` boundary correction.  Nothing
here formalizes Zwegers' modular transformation theorem; only the lattice sum
is treated. -/

/-- Zwegers' error-kernel argument at the boundary vector `c₂` for the shifted
lattice point `v = (x,y)+a`, namely `B₀(c₂,v)√Y/√(-Q₀(c₂))`. -/
def paper2C2KernelArg (p : ℤ × ℤ) (Y : ℝ) : ℝ :=
  paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * Real.sqrt Y /
    Real.sqrt (-paper2Q0 (-5) 3)

/-- The characteristic phase `e^{2πi B₀(v,b)}` of Zwegers' definition, at the
manuscript's characteristic `b = (1/2,-1/10)`. -/
def paper2CharPhase (p : ℤ × ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    (paper2B0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) (1 / 2) (-(1 / 10)) : ℝ))

/-- The weight `q^{Q₀(v)}` of Zwegers' definition, at the shifted lattice
point `v = (x,y)+a`. -/
def paper2LatticeNome (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * τ *
    (paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ))

/-- The `c₂` correction summand of Zwegers' completed indefinite theta series
at `v = (x,y)+a`:
`(E(B₀(c₂,v)√Y/√(-Q₀(c₂))) - sgn B₀(c₂,v)) e^{2πi B₀(v,b)} q^{Q₀(v)}`. -/
def paper2LatticeC2Term (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  ((zwegersErrorKernel (paper2C2KernelArg p τ.im) -
      Real.sign (paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) : ℝ) : ℂ) *
    (paper2CharPhase p * paper2LatticeNome p τ)

/-! ## The `(T,n)` coordinate change as a summability-preserving reindexing -/

/-- The coordinate change `(x,y) ↦ (T,n) = (3x+5y+2, 5x+15y+4)` of Paper 2. -/
def paper2NT (p : ℤ × ℤ) : ℤ × ℤ :=
  (paper2TransCoord p.1 p.2, paper2LongCoord p.1 p.2)

/-- The summand of the residue-`j` block in the `(T,n)` coordinates. -/
def paper2C2BlockTerm (j : ℤ) (z : ℤ × ℤ) (τ : ℂ) : ℂ :=
  paper2ThetaTerm j z.1 τ * paper2C2LongTerm j z.2 τ

theorem paper2C2Component_eq_tsum_block (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    paper2C2Component j τ = ∑' z : ℤ × ℤ, paper2C2BlockTerm j z τ :=
  paper2C2Component_eq_tsum_prod j hτ

theorem summable_paper2C2BlockTerm (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun z : ℤ × ℤ => paper2C2BlockTerm j z τ) :=
  summable_paper2C2Block j hτ

/-- The coordinate change is injective, so it reindexes without collision. -/
theorem paper2NT_injective : Function.Injective paper2NT := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [paper2NT, Prod.mk.injEq] at h
  obtain ⟨hx, hy⟩ := paper2Coord_injective h.2 h.1
  simp [hx, hy]

/-- The longitudinal residue class depends only on `j mod 4`. -/
theorem paper2GResidue_congr {j j' : ℤ} (h : j % 4 = j' % 4) (n : ℤ) :
    paper2GResidue j n ↔ paper2GResidue j' n := by
  unfold paper2GResidue
  omega

/-- The transverse residue class depends only on `j mod 4`. -/
theorem paper2ThetaResidue_congr {j j' : ℤ} (h : j % 4 = j' % 4) (T : ℤ) :
    paper2ThetaResidue j T ↔ paper2ThetaResidue j' T := by
  unfold paper2ThetaResidue
  omega

theorem paper2ThetaTerm_congr {j j' : ℤ} (h : j % 4 = j' % 4) (T : ℤ) (τ : ℂ) :
    paper2ThetaTerm j T τ = paper2ThetaTerm j' T τ := by
  unfold paper2ThetaTerm
  by_cases hT : paper2ThetaResidue j T
  · rw [if_pos hT, if_pos ((paper2ThetaResidue_congr h T).1 hT)]
  · rw [if_neg hT, if_neg fun hc => hT ((paper2ThetaResidue_congr h T).2 hc)]

theorem paper2C2LongTerm_congr {j j' : ℤ} (h : j % 4 = j' % 4) (n : ℤ) (τ : ℂ) :
    paper2C2LongTerm j n τ = paper2C2LongTerm j' n τ := by
  unfold paper2C2LongTerm
  by_cases hn : paper2GResidue j n
  · rw [if_pos hn, if_pos ((paper2GResidue_congr h n).1 hn)]
  · rw [if_neg hn, if_neg fun hc => hn ((paper2GResidue_congr h n).2 hc)]

/-- The block summand depends only on `j mod 4`. -/
theorem paper2C2BlockTerm_congr {j j' : ℤ} (h : j % 4 = j' % 4) (z : ℤ × ℤ) (τ : ℂ) :
    paper2C2BlockTerm j z τ = paper2C2BlockTerm j' z τ := by
  rw [paper2C2BlockTerm, paper2C2BlockTerm, paper2ThetaTerm_congr h,
    paper2C2LongTerm_congr h]

/-- Away from its own residue block a lattice point contributes nothing: the
label of a lattice point is unique modulo `4`. -/
theorem paper2C2BlockTerm_paper2NT_eq_zero {j : ℤ} (p : ℤ × ℤ) (τ : ℂ)
    (h : paper2CosetLabel p.1 p.2 % 4 ≠ j % 4) :
    paper2C2BlockTerm j (paper2NT p) τ = 0 := by
  have hres : ¬paper2GResidue j (paper2LongCoord p.1 p.2) := fun hc =>
    h (paper2CosetLabel_unique (paper2GResidue_longCoord p.1 p.2) hc)
  simp only [paper2C2BlockTerm, paper2NT, paper2C2LongTerm, if_neg hres, mul_zero]

/-- On its own residue block the coordinate change carries the full
orthogonal weight `q^{Q₀(v)} = q^{T²/8-n²/40}`. -/
theorem paper2C2BlockTerm_paper2NT (p : ℤ × ℤ) (τ : ℂ) :
    paper2C2BlockTerm (paper2CosetLabel p.1 p.2) (paper2NT p) τ
      = (paper2C2Factor (paper2LongCoord p.1 p.2) τ : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * τ *
            ((paper2TransCoord p.1 p.2 : ℂ) ^ 2 / 8 -
              (paper2LongCoord p.1 p.2 : ℂ) ^ 2 / 40)) := by
  simp only [paper2C2BlockTerm, paper2NT]
  exact paper2ThetaTerm_mul_paper2C2LongTerm _ _ _ τ
    (paper2GResidue_longCoord p.1 p.2) (paper2ThetaResidue_transCoord p.1 p.2)

/-- `(-1)^m` depends only on `m mod 4`. -/
theorem neg_one_zpow_congr {m m' : ℤ} (h : m % 4 = m' % 4) :
    ((-1 : ℂ)) ^ m = ((-1 : ℂ)) ^ m' := by
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  obtain ⟨k, hk⟩ : ∃ k : ℤ, m = m' + 2 * k := ⟨(m - m') / 2, by omega⟩
  have hsq : ((-1 : ℂ)) ^ (2 : ℤ) = 1 := by norm_num
  have h2 : ((-1 : ℂ)) ^ (2 * k) = 1 := by rw [zpow_mul, hsq, one_zpow]
  rw [hk, zpow_add₀ hne, h2, mul_one]

/-- Each lattice point contributes to exactly one of the four residue blocks,
with the character `(-1)^j` of the manuscript. -/
theorem sum_paper2C2BlockTerm_paper2NT (p : ℤ × ℤ) (τ : ℂ) :
    ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2C2BlockTerm (j : ℤ) (paper2NT p) τ
      = ((-1 : ℂ)) ^ paper2CosetLabel p.1 p.2 *
          paper2C2BlockTerm (paper2CosetLabel p.1 p.2) (paper2NT p) τ := by
  have hmem : (paper2CosetLabel p.1 p.2 % 4).toNat ∈ Finset.range 4 := by
    simp only [Finset.mem_range]
    omega
  have hcast : (((paper2CosetLabel p.1 p.2 % 4).toNat : ℤ)) % 4
      = paper2CosetLabel p.1 p.2 % 4 := by omega
  have hzero : ∀ b ∈ Finset.range 4, b ≠ (paper2CosetLabel p.1 p.2 % 4).toNat →
      (-1 : ℂ) ^ b * paper2C2BlockTerm (b : ℤ) (paper2NT p) τ = 0 := by
    intro b hb hbne
    simp only [Finset.mem_range] at hb
    have hne : paper2CosetLabel p.1 p.2 % 4 ≠ (b : ℤ) % 4 := by omega
    rw [paper2C2BlockTerm_paper2NT_eq_zero p τ hne, mul_zero]
  rw [Finset.sum_eq_single_of_mem _ hmem hzero, paper2C2BlockTerm_congr hcast]
  congr 1
  rw [← zpow_natCast ((-1 : ℂ)) ((paper2CosetLabel p.1 p.2 % 4).toNat)]
  exact neg_one_zpow_congr hcast

/-- Reindexing: a residue block summed over the `(T,n)` lattice is the same as
the same block summed over the original `(x,y)` lattice through the coordinate
change.  Injectivity gives one direction and surjectivity onto the residue
support gives the other. -/
theorem tsum_paper2C2BlockTerm_paper2NT (j : ℤ) (τ : ℂ) :
    (∑' p : ℤ × ℤ, paper2C2BlockTerm j (paper2NT p) τ)
      = ∑' z : ℤ × ℤ, paper2C2BlockTerm j z τ := by
  have hsupp : Function.support (fun z : ℤ × ℤ => paper2C2BlockTerm j z τ)
      ⊆ Set.range paper2NT := by
    intro z hz
    have hz' : paper2C2BlockTerm j z τ ≠ 0 := hz
    have hT : paper2ThetaResidue j z.1 := by
      by_contra hc
      exact hz' (by simp only [paper2C2BlockTerm, paper2ThetaTerm, if_neg hc, zero_mul])
    have hn : paper2GResidue j z.2 := by
      by_contra hc
      exact hz' (by simp only [paper2C2BlockTerm, paper2C2LongTerm, if_neg hc, mul_zero])
    obtain ⟨x, y, hx, hy⟩ := paper2Coord_surjective hn hT
    exact ⟨(x, y), by simp [paper2NT, hx, hy]⟩
  exact Function.Injective.tsum_eq (f := fun z : ℤ × ℤ => paper2C2BlockTerm j z τ)
    paper2NT_injective hsupp

/-! ## Termwise identification and the lattice-to-block bridge -/

/-- Paper 2's characteristic phase: `e^{2πi B₀(v,b)} = e^{3πi/5}(-1)^{x+y}`
for `v = (x,y)+a` and `b = (1/2,-1/10)`. -/
theorem paper2CharPhase_eq (p : ℤ × ℤ) :
    paper2CharPhase p
      = Complex.exp (3 * Real.pi * Complex.I / 5) * ((-1 : ℂ)) ^ (p.1 + p.2) := by
  rw [paper2CharPhase, neg_one_zpow_eq_exp_pi_I, ← Complex.exp_add]
  congr 1
  simp only [paper2B0]
  push_cast
  ring

/-- The lattice weight in the `(T,n)` coordinates. -/
theorem paper2LatticeNome_eq (p : ℤ × ℤ) (τ : ℂ) :
    paper2LatticeNome p τ
      = Complex.exp (2 * Real.pi * Complex.I * τ *
          ((paper2TransCoord p.1 p.2 : ℂ) ^ 2 / 8 -
            (paper2LongCoord p.1 p.2 : ℂ) ^ 2 / 40)) := by
  rw [paper2LatticeNome, paper2Q0_shift]
  congr 1
  push_cast
  ring

/-- The real Zwegers correction factor at a lattice point is the paper's
`E(-n√(Y/10)) - sgn(-n)`. -/
theorem paper2LatticeC2Factor_eq (p : ℤ × ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    zwegersErrorKernel (paper2C2KernelArg p τ.im) -
        Real.sign (paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10))
      = paper2C2Factor (paper2LongCoord p.1 p.2) τ := by
  rw [paper2C2KernelArg, paper2_kernel_argument p.1 p.2 hτ, paper2B0_c2_shift]
  rfl

/-- Termwise identification: the Zwegers `c₂` correction summand at `(x,y)` is
`e^{3πi/5}` times the `(-1)^j`-weighted residue-block summand at `(T,n)`. -/
theorem paper2LatticeC2Term_eq (p : ℤ × ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeC2Term p τ
      = Complex.exp (3 * Real.pi * Complex.I / 5) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            paper2C2BlockTerm (j : ℤ) (paper2NT p) τ := by
  rw [sum_paper2C2BlockTerm_paper2NT, paper2C2BlockTerm_paper2NT,
    paper2LatticeC2Term, paper2LatticeC2Factor_eq p hτ, paper2CharPhase_eq,
    paper2LatticeNome_eq, paper2Sign_eq_cosetLabel]
  ring

/-- The original `(x,y)`-indexed `c₂` correction series converges absolutely
on the upper half-plane. -/
theorem summable_paper2LatticeC2Term {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ => paper2LatticeC2Term p τ) := by
  have hblock : ∀ j ∈ Finset.range 4,
      Summable (fun p : ℤ × ℤ =>
        (-1 : ℂ) ^ j * paper2C2BlockTerm (j : ℤ) (paper2NT p) τ) := by
    intro j _
    have h0 : Summable (fun z : ℤ × ℤ => paper2C2BlockTerm (j : ℤ) z τ) :=
      summable_paper2C2BlockTerm (j : ℤ) hτ
    have h1 : Summable (fun p : ℤ × ℤ => paper2C2BlockTerm (j : ℤ) (paper2NT p) τ) := by
      simpa only [Function.comp_def] using h0.comp_injective paper2NT_injective
    exact h1.mul_left _
  refine ((summable_sum hblock).mul_left
    (Complex.exp (3 * Real.pi * Complex.I / 5))).congr fun p => ?_
  exact (paper2LatticeC2Term_eq p hτ).symm

/-- **Lattice-to-block bridge.**  With the manuscript's exact constant
`½e^{-3πi/5}`, the `c₂` boundary correction of Zwegers' completed series,
summed over the original shifted lattice `a + ℤ²`, equals the assembled
four-block expression `½ Σ_j (-1)^j θ_j G_j`.

This is a statement about the convergent lattice sum only.  It does not
formalize Zwegers' completion or modular transformation theorem, and it makes
no claim about `∂/∂τ̄` or `ξ₁`. -/
theorem paper2LatticeC2_tsum_eq {τ : ℂ} (hτ : 0 < τ.im) :
    (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
        ∑' p : ℤ × ℤ, paper2LatticeC2Term p τ
      = paper2C2Correction τ := by
  have hblock : ∀ j ∈ Finset.range 4,
      Summable (fun p : ℤ × ℤ =>
        (-1 : ℂ) ^ j * paper2C2BlockTerm (j : ℤ) (paper2NT p) τ) := by
    intro j _
    have h0 : Summable (fun z : ℤ × ℤ => paper2C2BlockTerm (j : ℤ) z τ) :=
      summable_paper2C2BlockTerm (j : ℤ) hτ
    have h1 : Summable (fun p : ℤ × ℤ => paper2C2BlockTerm (j : ℤ) (paper2NT p) τ) := by
      simpa only [Function.comp_def] using h0.comp_injective paper2NT_injective
    exact h1.mul_left _
  have hstep : (∑' p : ℤ × ℤ, paper2LatticeC2Term p τ)
      = Complex.exp (3 * Real.pi * Complex.I / 5) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2C2Component (j : ℤ) τ := by
    calc (∑' p : ℤ × ℤ, paper2LatticeC2Term p τ)
        = ∑' p : ℤ × ℤ, Complex.exp (3 * Real.pi * Complex.I / 5) *
            ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
              paper2C2BlockTerm (j : ℤ) (paper2NT p) τ :=
          tsum_congr fun p => paper2LatticeC2Term_eq p hτ
      _ = Complex.exp (3 * Real.pi * Complex.I / 5) *
            ∑' p : ℤ × ℤ, ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
              paper2C2BlockTerm (j : ℤ) (paper2NT p) τ :=
          (summable_sum hblock).tsum_mul_left _
      _ = Complex.exp (3 * Real.pi * Complex.I / 5) *
            ∑ j ∈ Finset.range 4, ∑' p : ℤ × ℤ, (-1 : ℂ) ^ j *
              paper2C2BlockTerm (j : ℤ) (paper2NT p) τ := by
          rw [Summable.tsum_finsetSum hblock]
      _ = Complex.exp (3 * Real.pi * Complex.I / 5) *
            ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2C2Component (j : ℤ) τ := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          have h0 : Summable (fun z : ℤ × ℤ => paper2C2BlockTerm (j : ℤ) z τ) :=
            summable_paper2C2BlockTerm (j : ℤ) hτ
          have h1 : Summable (fun p : ℤ × ℤ =>
              paper2C2BlockTerm (j : ℤ) (paper2NT p) τ) := by
            simpa only [Function.comp_def] using h0.comp_injective paper2NT_injective
          rw [h1.tsum_mul_left, tsum_paper2C2BlockTerm_paper2NT (j : ℤ) τ,
            ← paper2C2Component_eq_tsum_block (j : ℤ) hτ]
  have hphase : Complex.exp (-3 * Real.pi * Complex.I / 5) *
      Complex.exp (3 * Real.pi * Complex.I / 5) = 1 := by
    rw [← Complex.exp_add,
      show -3 * (Real.pi : ℂ) * Complex.I / 5 + 3 * (Real.pi : ℂ) * Complex.I / 5 = 0 by ring]
    exact Complex.exp_zero
  rw [hstep, paper2C2Correction]
  linear_combination
    ((1 / 2 : ℂ) * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2C2Component (j : ℤ) τ) * hphase

/-! ## The `c₁` boundary correction and its identical vanishing

At the first boundary vector `c₁ = (0,1)` the manuscript records
`P(c₁) = -5`, hence `Q₀(c₁) = -5/2`, and the pairing
`B₀(c₁,v) = 0·(x+1/2) - 5·1·(y+1/10) = -5(y+1/10)` depends on the second
coordinate alone.  The orthogonal vector `e₁ = (1,0)` satisfies
`B₀(c₁,e₁) = 0` and `|det(c₁,e₁)| = 1`, so the lattice splits unimodularly:
the summand is a product of a transverse `x`-series and a longitudinal
`y`-series.  The transverse series is exactly the odd theta of
`Ch10_Paper2_UnaryTheta` at half-period parameter `a = 1/2`, which vanishes by
the fixed-point-free pairing `x ↦ -1-x`, so the whole `c₁` correction vanishes.

As everywhere in this file, the statements below concern the convergent
lattice sum only.  Nothing here asserts Zwegers' completion theorem, the `T`
or `S` transformation law, or the `∂/∂τ̄` formula. -/

/-- Zwegers' error-kernel argument at the boundary vector `c₁ = (0,1)` for the
shifted lattice point `v = (x,y)+a`, namely `B₀(c₁,v)√Y/√(-Q₀(c₁))`. -/
def paper2C1KernelArg (p : ℤ × ℤ) (Y : ℝ) : ℝ :=
  paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * Real.sqrt Y /
    Real.sqrt (-paper2Q0 0 1)

/-- The `c₁` correction summand of Zwegers' completed indefinite theta series
at `v = (x,y)+a`:
`(E(B₀(c₁,v)√Y/√(-Q₀(c₁))) - sgn B₀(c₁,v)) e^{2πi B₀(v,b)} q^{Q₀(v)}`.
The phase and weight are literally `paper2CharPhase` and `paper2LatticeNome`,
so this and `paper2LatticeC2Term` are the two halves of one Zwegers
Definition 2.1 summand. -/
def paper2LatticeC1Term (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  ((zwegersErrorKernel (paper2C1KernelArg p τ.im) -
      Real.sign (paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) : ℝ) : ℂ) *
    (paper2CharPhase p * paper2LatticeNome p τ)

/-- The boundary vector `c₁=(0,1)` has `Q₀(c₁) = -5/2`, matching `P(c₁)=-5`. -/
theorem paper2Q0_c1 : paper2Q0 0 1 = -5 / 2 := by
  unfold paper2Q0
  norm_num

/-- The boundary vector `c₁=(0,1)` is `B₀`-orthogonal to `e₁=(1,0)`. -/
theorem paper2B0_c1_e1 : paper2B0 0 1 1 0 = 0 := by
  unfold paper2B0
  norm_num

/-- The `c₁` pairing depends on the second coordinate alone:
`B₀(c₁,v) = -5(y+1/10)`. -/
theorem paper2B0_c1_shift (x y : ℤ) :
    paper2B0 0 1 ((x : ℝ) + 1 / 2) ((y : ℝ) + 1 / 10)
      = -(5 * ((y : ℝ) + 1 / 10)) := by
  unfold paper2B0
  ring

/-- Multiplication by a positive real does not move `Real.sign`. -/
theorem sign_pos_mul {c t : ℝ} (hc : 0 < c) : Real.sign (c * t) = Real.sign t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · rw [h, mul_zero]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

theorem sign_mul_pos {t c : ℝ} (hc : 0 < c) : Real.sign (t * c) = Real.sign t := by
  rw [mul_comm]
  exact sign_pos_mul hc

/-- The `c₁` boundary sign is the sign of `-(y+1/10)`. -/
theorem sign_paper2B0_c1 (x y : ℤ) :
    Real.sign (paper2B0 0 1 ((x : ℝ) + 1 / 2) ((y : ℝ) + 1 / 10))
      = Real.sign (-((y : ℝ) + 1 / 10)) := by
  rw [paper2B0_c1_shift,
    show -(5 * ((y : ℝ) + 1 / 10)) = 5 * -((y : ℝ) + 1 / 10) by ring]
  exact sign_pos_mul (by norm_num)

/-- Zwegers' kernel argument at `c₁`, in closed form:
`B₀(c₁,v)√Y/√(-Q₀(c₁)) = -(y+1/10)√(10Y)`.  The constant enters through
`5/√(5/2) = √10`. -/
theorem paper2_c1_kernel_argument (p : ℤ × ℤ) (Y : ℝ) :
    paper2C1KernelArg p Y = -((p.2 : ℝ) + 1 / 10) * Real.sqrt (10 * Y) := by
  have hden : -paper2Q0 0 1 = 5 / 2 := by
    rw [paper2Q0_c1]
    norm_num
  have hpos : (0 : ℝ) < Real.sqrt (5 / 2) := Real.sqrt_pos.2 (by norm_num)
  have hsplit : Real.sqrt (10 * Y) = Real.sqrt 10 * Real.sqrt Y :=
    Real.sqrt_mul (by norm_num) Y
  have hkey : Real.sqrt 10 * Real.sqrt (5 / 2) = 5 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10),
      show (10 : ℝ) * (5 / 2) = 5 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [paper2C1KernelArg, paper2B0_c1_shift, hden, hsplit, div_eq_iff hpos.ne']
  linear_combination (((p.2 : ℝ) + 1 / 10) * Real.sqrt Y) * hkey

/-! ### The unimodular splitting -/

/-- The longitudinal `c₁` factor at the row `y`:
`(-1)^y (E(-(y+1/10)√(10Y)) - sgn(-(y+1/10))) q^{-5(y+1/10)²/2}`. -/
def paper2C1LongTerm (y : ℤ) (τ : ℂ) : ℂ :=
  ((-1 : ℂ)) ^ y *
    ((zwegersErrorKernel (-((y : ℝ) + 1 / 10) * Real.sqrt (10 * τ.im)) -
        Real.sign (-((y : ℝ) + 1 / 10)) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * τ * (-(5 * ((y : ℂ) + 1 / 10) ^ 2) / 2))

/-- The odd transverse theta summand at `a=1/2` is `(-1)^x q^{(x+1/2)²/2}`. -/
theorem paper2OddThetaTerm_half (τ : ℂ) (x : ℤ) :
    paper2OddThetaTerm (1 / 2) τ x
      = ((-1 : ℂ)) ^ x *
          Complex.exp (2 * Real.pi * Complex.I * τ * (1 / 2) * ((x : ℂ) + 1 / 2) ^ 2) := by
  unfold paper2OddThetaTerm
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
  rw [hhalf]

/-- The unimodular splitting of the weight at `c₁`:
`q^{Q₀(v)} = q^{(x+1/2)²/2}·q^{-5(y+1/10)²/2}`. -/
theorem paper2LatticeNome_c1_split (p : ℤ × ℤ) (τ : ℂ) :
    paper2LatticeNome p τ
      = Complex.exp (2 * Real.pi * Complex.I * τ * (1 / 2) * ((p.1 : ℂ) + 1 / 2) ^ 2) *
          Complex.exp (2 * Real.pi * Complex.I * τ *
            (-(5 * ((p.2 : ℂ) + 1 / 10) ^ 2) / 2)) := by
  rw [paper2LatticeNome, ← Complex.exp_add]
  congr 1
  simp only [paper2Q0]
  push_cast
  ring

/-- Termwise unimodular splitting: the `c₁` summand is `e^{3πi/5}` times the
product of the odd transverse theta summand and the longitudinal `c₁`
factor. -/
theorem paper2LatticeC1Term_eq (p : ℤ × ℤ) (τ : ℂ) :
    paper2LatticeC1Term p τ
      = Complex.exp (3 * Real.pi * Complex.I / 5) *
          (paper2OddThetaTerm (1 / 2) τ p.1 * paper2C1LongTerm p.2 τ) := by
  have hsign : ((-1 : ℂ)) ^ (p.1 + p.2) = ((-1 : ℂ)) ^ p.1 * ((-1 : ℂ)) ^ p.2 :=
    zpow_add₀ (by norm_num) _ _
  rw [paper2LatticeC1Term, paper2_c1_kernel_argument p τ.im, sign_paper2B0_c1 p.1 p.2,
    paper2CharPhase_eq, paper2LatticeNome_c1_split, paper2OddThetaTerm_half,
    paper2C1LongTerm, hsign]
  ring

/-! ### Absolute convergence of the longitudinal `c₁` series -/

/-- Every integer stays at distance at least `1/10` from `-1/10`, so the `c₁`
kernel argument never degenerates: unlike the `c₂` case there is no
exceptional index. -/
theorem one_tenth_le_abs_add (y : ℤ) : (1 : ℝ) / 10 ≤ |(y : ℝ) + 1 / 10| := by
  by_cases h : 0 ≤ y
  · have hy : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith
  · have hy : (y : ℝ) ≤ -1 := by exact_mod_cast (by omega : y ≤ -1)
    rw [abs_of_neg (by linarith)]
    linarith

/-- Shifted Gaussian majorant: for `c>0` and any real shift `s`, the family
`y ↦ e^{-πc(y+s)²}` is summable over `ℤ`. -/
theorem summable_exp_neg_pi_mul_shift_sq (s : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable (fun y : ℤ => Real.exp (-Real.pi * c * ((y : ℝ) + s) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun y => (Real.exp_pos _).le) ?_
    (summable_pow_mul_jacobiTheta₂_term_bound (c * |s|) hc 0)
  intro y
  simp only [pow_zero, one_mul, Int.cast_abs]
  refine Real.exp_le_exp.2 ?_
  have habs : -(|s| * |(y : ℝ)|) ≤ s * (y : ℝ) := by
    rw [← abs_mul]
    exact neg_abs_le _
  have hkey : c * (y : ℝ) ^ 2 - 2 * (c * |s|) * |(y : ℝ)| ≤ c * ((y : ℝ) + s) ^ 2 := by
    nlinarith [mul_nonneg hc.le (by linarith : (0 : ℝ) ≤ s * (y : ℝ) + |s| * |(y : ℝ)|),
      mul_nonneg hc.le (sq_nonneg s)]
  have hpi := mul_le_mul_of_nonneg_left hkey Real.pi_pos.le
  linarith

/-- The longitudinal `c₁` weight rewritten with a real scalar. -/
theorem paper2C1LongNome_eq (y : ℤ) (τ : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * τ * (-(5 * ((y : ℂ) + 1 / 10) ^ 2) / 2))
      = Complex.exp ((-(5 * Real.pi * ((y : ℝ) + 1 / 10) ^ 2) : ℝ) *
          (Complex.I * τ)) := by
  congr 1
  push_cast
  ring

/-- Exact growth of the longitudinal `c₁` weight:
`‖q^{-5(y+1/10)²/2}‖ = e^{5π(y+1/10)²Y}`. -/
theorem norm_paper2C1LongNome (y : ℤ) (τ : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * τ * (-(5 * ((y : ℂ) + 1 / 10) ^ 2) / 2))‖
      = Real.exp (5 * Real.pi * ((y : ℝ) + 1 / 10) ^ 2 * τ.im) := by
  have hre : (Complex.I * τ).re = -τ.im := by
    simp [Complex.mul_re]
  rw [paper2C1LongNome_eq, Complex.norm_exp, Complex.re_ofReal_mul, hre]
  congr 1
  ring

/-- Pointwise majorant for the longitudinal `c₁` summand.  The Mills bound
`e^{-10π(y+1/10)²Y}/(π|z|)` beats the weight growth `e^{5π(y+1/10)²Y}`, and
`|y+1/10| ≥ 1/10` bounds `|z| = |y+1/10|√(10Y)` below by `√(Y/10)` uniformly
in `y`. -/
theorem norm_paper2C1LongTerm_le (y : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖paper2C1LongTerm y τ‖
      ≤ (Real.pi * Real.sqrt (τ.im / 10))⁻¹ *
          Real.exp (-Real.pi * (5 * τ.im) * ((y : ℝ) + 1 / 10) ^ 2) := by
  have hs : 0 < Real.sqrt (τ.im / 10) := Real.sqrt_pos.2 (by positivity)
  have hπs : 0 < Real.pi * Real.sqrt (τ.im / 10) := by positivity
  have h10 : 0 < Real.sqrt (10 * τ.im) := Real.sqrt_pos.2 (by positivity)
  have hw10 : (1 : ℝ) / 10 ≤ |(y : ℝ) + 1 / 10| := one_tenth_le_abs_add y
  have hwne : ((y : ℝ) + 1 / 10) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw10
    linarith
  have hzne : -((y : ℝ) + 1 / 10) * Real.sqrt (10 * τ.im) ≠ 0 := by
    intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact hwne (by linarith)
    · exact (ne_of_gt h10) h'
  have hb := abs_zwegersErrorKernel_sub_sign_le hzne
  rw [sign_mul_pos h10] at hb
  have hzsq : (-((y : ℝ) + 1 / 10) * Real.sqrt (10 * τ.im)) ^ 2
      = ((y : ℝ) + 1 / 10) ^ 2 * (10 * τ.im) := by
    rw [mul_pow, neg_sq, Real.sq_sqrt (by positivity)]
  have hzabs : |(-((y : ℝ) + 1 / 10) * Real.sqrt (10 * τ.im))|
      = |(y : ℝ) + 1 / 10| * Real.sqrt (10 * τ.im) := by
    rw [abs_mul, abs_neg, abs_of_pos h10]
  rw [hzsq, hzabs] at hb
  have hexp : Real.exp (-Real.pi * (((y : ℝ) + 1 / 10) ^ 2 * (10 * τ.im))) *
        Real.exp (5 * Real.pi * ((y : ℝ) + 1 / 10) ^ 2 * τ.im)
      = Real.exp (-Real.pi * (5 * τ.im) * ((y : ℝ) + 1 / 10) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (10 * τ.im) = 10 * Real.sqrt (τ.im / 10) := by
    have h1 : Real.sqrt (τ.im / 10) ^ 2 = τ.im / 10 := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (10 * τ.im) ^ 2 = 10 * τ.im := Real.sq_sqrt (by positivity)
    have h3 : 0 ≤ Real.sqrt (τ.im / 10) := Real.sqrt_nonneg _
    have h4 : 0 ≤ Real.sqrt (10 * τ.im) := Real.sqrt_nonneg _
    nlinarith
  have hden : Real.pi * Real.sqrt (τ.im / 10)
      ≤ Real.pi * (|(y : ℝ) + 1 / 10| * Real.sqrt (10 * τ.im)) := by
    rw [hsqrt]
    nlinarith [mul_pos Real.pi_pos hs, hw10]
  have hinv : (Real.pi * (|(y : ℝ) + 1 / 10| * Real.sqrt (10 * τ.im)))⁻¹
      ≤ (Real.pi * Real.sqrt (τ.im / 10))⁻¹ := inv_anti₀ hπs hden
  have hone : ‖((-1 : ℂ)) ^ y‖ = 1 := by
    rw [norm_zpow]
    simp
  rw [paper2C1LongTerm, norm_mul, norm_mul, hone, one_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_paper2C1LongNome]
  calc |zwegersErrorKernel (-((y : ℝ) + 1 / 10) * Real.sqrt (10 * τ.im)) -
          Real.sign (-((y : ℝ) + 1 / 10))| *
        Real.exp (5 * Real.pi * ((y : ℝ) + 1 / 10) ^ 2 * τ.im)
      ≤ Real.exp (-Real.pi * (((y : ℝ) + 1 / 10) ^ 2 * (10 * τ.im))) /
            (Real.pi * (|(y : ℝ) + 1 / 10| * Real.sqrt (10 * τ.im))) *
          Real.exp (5 * Real.pi * ((y : ℝ) + 1 / 10) ^ 2 * τ.im) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = (Real.pi * (|(y : ℝ) + 1 / 10| * Real.sqrt (10 * τ.im)))⁻¹ *
          Real.exp (-Real.pi * (5 * τ.im) * ((y : ℝ) + 1 / 10) ^ 2) := by
        rw [← hexp, div_eq_inv_mul]
        ring
    _ ≤ (Real.pi * Real.sqrt (τ.im / 10))⁻¹ *
          Real.exp (-Real.pi * (5 * τ.im) * ((y : ℝ) + 1 / 10) ^ 2) :=
        mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le

/-- Absolute convergence of the longitudinal `c₁` series for `Im τ > 0`. -/
theorem summable_norm_paper2C1LongTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun y : ℤ => ‖paper2C1LongTerm y τ‖) := by
  have hc : 0 < 5 * τ.im := by positivity
  refine Summable.of_nonneg_of_le (fun y => norm_nonneg _)
    (fun y => norm_paper2C1LongTerm_le y hτ) ?_
  exact (summable_exp_neg_pi_mul_shift_sq (1 / 10) hc).mul_left _

theorem summable_paper2C1LongTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun y : ℤ => paper2C1LongTerm y τ) :=
  Summable.of_norm (summable_norm_paper2C1LongTerm hτ)

/-- Absolute convergence of the odd transverse theta series at `a=1/2`. -/
theorem summable_norm_paper2OddThetaTerm_half {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun x : ℤ => ‖paper2OddThetaTerm (1 / 2) τ x‖) :=
  (summable_paper2OddThetaTerm (by norm_num) hτ).norm

/-- The `(x,y)` double family of the `c₁` correction is absolutely summable. -/
theorem summable_paper2C1Block {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ =>
      paper2OddThetaTerm (1 / 2) τ p.1 * paper2C1LongTerm p.2 τ) :=
  summable_mul_of_summable_norm (R := ℂ)
    (f := fun x : ℤ => paper2OddThetaTerm (1 / 2) τ x)
    (g := fun y : ℤ => paper2C1LongTerm y τ)
    (summable_norm_paper2OddThetaTerm_half hτ) (summable_norm_paper2C1LongTerm hτ)

/-- The `c₁` correction series converges absolutely on the upper half-plane. -/
theorem summable_paper2LatticeC1Term {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ => paper2LatticeC1Term p τ) := by
  refine ((summable_paper2C1Block hτ).mul_left
    (Complex.exp (3 * Real.pi * Complex.I / 5))).congr fun p => ?_
  exact (paper2LatticeC1Term_eq p τ).symm

/-- **The `c₁` correction vanishes** (manuscript Proposition "The `c₁`
correction vanishes"), as a statement about the convergent lattice sum: the
unimodular splitting factors the sum, and the odd transverse theta factor is
zero.  This asserts nothing about Zwegers' completion or transformation
theorems. -/
theorem paper2LatticeC1_tsum_eq_zero {τ : ℂ} (hτ : 0 < τ.im) :
    ∑' p : ℤ × ℤ, paper2LatticeC1Term p τ = 0 := by
  have hfac : (∑' p : ℤ × ℤ, paper2LatticeC1Term p τ)
      = Complex.exp (3 * Real.pi * Complex.I / 5) *
          ∑' p : ℤ × ℤ, paper2OddThetaTerm (1 / 2) τ p.1 * paper2C1LongTerm p.2 τ := by
    rw [← (summable_paper2C1Block hτ).tsum_mul_left]
    exact tsum_congr fun p => paper2LatticeC1Term_eq p τ
  have hprod :
      (∑' p : ℤ × ℤ, paper2OddThetaTerm (1 / 2) τ p.1 * paper2C1LongTerm p.2 τ)
        = (∑' x : ℤ, paper2OddThetaTerm (1 / 2) τ x) *
            ∑' y : ℤ, paper2C1LongTerm y τ :=
    (tsum_mul_tsum_of_summable_norm (R := ℂ)
      (f := fun x : ℤ => paper2OddThetaTerm (1 / 2) τ x)
      (g := fun y : ℤ => paper2C1LongTerm y τ)
      (summable_norm_paper2OddThetaTerm_half hτ)
      (summable_norm_paper2C1LongTerm hτ)).symm
  rw [hfac, hprod,
    paper2OddTheta_tsum_eq_zero (a := (1 / 2 : ℝ)) (by norm_num) hτ, zero_mul, mul_zero]

/-! ## The full-lattice bridge -/

/-- The full Zwegers Definition 2.1 boundary correction at this data, namely
the `c₂` summand minus the `c₁` summand, is summable. -/
theorem summable_paper2LatticeTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ => paper2LatticeC2Term p τ - paper2LatticeC1Term p τ) :=
  (summable_paper2LatticeC2Term hτ).sub (summable_paper2LatticeC1Term hτ)

/-- **Full-lattice bridge.**  With the manuscript's exact constant
`½e^{-3πi/5}`, the complete Zwegers Definition 2.1 boundary correction — the
`c₂` summand minus the `c₁` summand — summed over the original shifted lattice
`a + ℤ²`, equals the assembled four-block expression `½ Σ_j (-1)^j θ_j G_j`.
The `c₁` half contributes nothing by `paper2LatticeC1_tsum_eq_zero`.

This is a statement about the convergent lattice sum only.  It does not
formalize Zwegers' completion or modular transformation theorem, and it makes
no claim about `∂/∂τ̄` or `ξ₁`. -/
theorem paper2Lattice_tsum_eq {τ : ℂ} (hτ : 0 < τ.im) :
    (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
        ∑' p : ℤ × ℤ, (paper2LatticeC2Term p τ - paper2LatticeC1Term p τ)
      = paper2C2Correction τ := by
  rw [Summable.tsum_sub (summable_paper2LatticeC2Term hτ)
      (summable_paper2LatticeC1Term hτ),
    paper2LatticeC1_tsum_eq_zero hτ, sub_zero]
  exact paper2LatticeC2_tsum_eq hτ

/-! ## The Wirtinger operator `∂/∂τ̄`

Mathlib has no Wirtinger derivative, no `ξ_k` operator and no harmonic-Maass
class, so `∂/∂τ̄` is defined here from the real Fréchet derivative by
`∂/∂τ̄ = ½(∂_X + i∂_Y)`, i.e. `½(Df(τ)1 + i·Df(τ)i)`.

Every real Fréchet derivative occurring below has the shape
`h ↦ (Im h)·a + b·h`; `paper2ImLin` packages that shape once, with its
operator-norm bound and its Wirtinger projection.  The projection kills the
`b`-term identically — that cancellation, computed explicitly in
`dbar_paper2ImLin`, is the statement that a holomorphic factor contributes
nothing.

As everywhere in this file, the statements below concern an explicit
convergent lattice sum.  Nothing here asserts Zwegers' completion theorem or
the `T`/`S` transformation laws of his Corollary 2.9. -/

/-- The real-linear map `h ↦ (Im h)·a + b·h` on `ℂ`. -/
noncomputable def paper2ImLin (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.imCLM.smulRight a + b • (ContinuousLinearMap.id ℝ ℂ)

@[simp] theorem paper2ImLin_apply (a b h : ℂ) :
    paper2ImLin a b h = (h.im : ℂ) * a + b * h := by
  simp [paper2ImLin, Complex.real_smul]

theorem norm_paper2ImLin_le (a b : ℂ) : ‖paper2ImLin a b‖ ≤ ‖a‖ + ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [paper2ImLin_apply]
  have him : |h.im| ≤ ‖h‖ := Complex.abs_im_le_norm h
  have hna : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
  calc ‖(h.im : ℂ) * a + b * h‖ ≤ ‖(h.im : ℂ) * a‖ + ‖b * h‖ := norm_add_le _ _
    _ = |h.im| * ‖a‖ + ‖b‖ * ‖h‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖h‖ * ‖a‖ + ‖b‖ * ‖h‖ := by nlinarith
    _ = (‖a‖ + ‖b‖) * ‖h‖ := by ring

/-- The Wirtinger projection `L ↦ ½(L 1 + i·L i)` as a continuous linear map
on `ℂ →L[ℝ] ℂ`; packaging it this way lets it pass through a `tsum`. -/
noncomputable def wirtingerBarCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) +
    Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

theorem wirtingerBarCLM_apply (L : ℂ →L[ℝ] ℂ) :
    wirtingerBarCLM L = (L 1 + Complex.I * L Complex.I) / 2 := by
  simp only [wirtingerBarCLM, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

/-- The Wirtinger derivative `∂/∂τ̄ = ½(∂_X + i∂_Y)` of a function `ℂ → ℂ`,
defined from its real Fréchet derivative. -/
noncomputable def dbar (F : ℂ → ℂ) (τ : ℂ) : ℂ :=
  wirtingerBarCLM (fderiv ℝ F τ)

theorem dbar_eq (F : ℂ → ℂ) (τ : ℂ) :
    dbar F τ = (fderiv ℝ F τ 1 + Complex.I * fderiv ℝ F τ Complex.I) / 2 := by
  rw [dbar, wirtingerBarCLM_apply]

/-- `HasFDerivAt`-keyed form, so downstream statements carry no
`Differentiable` side condition. -/
theorem dbar_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {τ : ℂ}
    (h : HasFDerivAt F L τ) : dbar F τ = (L 1 + Complex.I * L Complex.I) / 2 := by
  rw [dbar, h.fderiv, wirtingerBarCLM_apply]

/-- The Wirtinger projection of `paper2ImLin a b`: the `b`-term cancels
identically, `b + i·(b·i) = b - b = 0`.  This is the explicit form of
`∂/∂τ̄` annihilating a holomorphic factor. -/
theorem dbar_paper2ImLin (a b : ℂ) :
    (paper2ImLin a b 1 + Complex.I * paper2ImLin a b Complex.I) / 2
      = Complex.I * a / 2 := by
  rw [paper2ImLin_apply, paper2ImLin_apply]
  simp only [Complex.one_im, Complex.I_im, Complex.ofReal_zero, Complex.ofReal_one]
  linear_combination (b / 2) * Complex.I_mul_I

/-! ## The termwise real Fréchet derivative -/

/-- Real Fréchet derivative of a product `↑(k (Im z)) · g z` with `k` real
differentiable in the imaginary part and `g` holomorphic. -/
theorem hasFDerivAt_ofReal_im_mul {k : ℝ → ℝ} {k' : ℝ} {g : ℂ → ℂ} {g' : ℂ} {τ : ℂ}
    (hk : HasDerivAt k k' τ.im) (hg : HasDerivAt g g' τ) :
    HasFDerivAt (fun z : ℂ => ((k z.im : ℝ) : ℂ) * g z)
      (paper2ImLin (((k' : ℝ) : ℂ) * g τ) (((k τ.im : ℝ) : ℂ) * g')) τ := by
  have hkC : HasDerivAt (fun t : ℝ => ((k t : ℝ) : ℂ)) (((k' : ℝ) : ℂ)) τ.im :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ.im hk
  have hA : HasFDerivAt (fun z : ℂ => ((k z.im : ℝ) : ℂ))
      (Complex.imCLM.smulRight (((k' : ℝ) : ℂ))) τ := by
    refine (hkC.hasFDerivAt.comp τ Complex.imCLM.hasFDerivAt).congr_fderiv ?_
    ext h
    simp
  have hB : HasFDerivAt g
      ((ContinuousLinearMap.toSpanSingleton ℂ g').restrictScalars ℝ) τ :=
    hg.hasFDerivAt.restrictScalars ℝ
  refine (hA.mul hB).congr_fderiv ?_
  ext h
  simp [Complex.real_smul]
  ring

/-- The `Y`-derivative of the surviving `c₂` correction factor. -/
noncomputable def paper2C2FactorDeriv (p : ℤ × ℤ) (τ : ℂ) : ℝ :=
  -(paper2LongCoord p.1 p.2 : ℝ) / Real.sqrt (10 * τ.im) *
    Real.exp (-Real.pi * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 * τ.im / 10)

theorem hasDerivAt_paper2C2Factor (p : ℤ × ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun t : ℝ => paper2BoundaryCorrection (paper2LongCoord p.1 p.2 : ℝ) t)
      (paper2C2FactorDeriv p τ) τ.im :=
  (hasDerivAt_paper2BoundaryError (paper2LongCoord p.1 p.2 : ℝ) τ.im hτ).sub_const _

/-- The holomorphic logarithmic rate `2πi Q₀(v)` of the lattice weight. -/
noncomputable def paper2LatticeNomeRate (p : ℤ × ℤ) : ℂ :=
  2 * Real.pi * Complex.I *
    ((paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ) : ℂ)

theorem hasDerivAt_paper2LatticeNome (p : ℤ × ℤ) (τ : ℂ) :
    HasDerivAt (fun z : ℂ => paper2LatticeNome p z)
      (paper2LatticeNome p τ * paper2LatticeNomeRate p) τ := by
  have h1 : HasDerivAt
      (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.I * z *
        ((paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ) : ℂ))
      (paper2LatticeNomeRate p) τ := by
    have h := ((hasDerivAt_id τ).const_mul (2 * (Real.pi : ℂ) * Complex.I)).mul_const
      (((paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ) : ℂ))
    simpa [paper2LatticeNomeRate] using h
  simpa [paper2LatticeNome] using h1.cexp

/-- The real Fréchet derivative of the `c₂` summand at a lattice point. -/
noncomputable def paper2C2Fderiv (p : ℤ × ℤ) (τ : ℂ) : ℂ →L[ℝ] ℂ :=
  paper2ImLin
    (((paper2C2FactorDeriv p τ : ℝ) : ℂ) *
      (paper2CharPhase p * paper2LatticeNome p τ))
    (((paper2C2Factor (paper2LongCoord p.1 p.2) τ : ℝ) : ℂ) *
      (paper2CharPhase p * (paper2LatticeNome p τ * paper2LatticeNomeRate p)))

/-- Termwise real Fréchet differentiability of the `c₂` summand on the upper
half-plane. -/
theorem hasFDerivAt_paper2LatticeC2Term (p : ℤ × ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasFDerivAt (fun z : ℂ => paper2LatticeC2Term p z) (paper2C2Fderiv p τ) τ := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun z : ℂ => paper2LatticeC2Term p z) =ᶠ[nhds τ]
      fun z : ℂ => ((paper2BoundaryCorrection (paper2LongCoord p.1 p.2 : ℝ) z.im : ℝ) : ℂ) *
        (paper2CharPhase p * paper2LatticeNome p z) := by
    filter_upwards [hopen.mem_nhds hτ] with z hz
    rw [paper2LatticeC2Term, paper2LatticeC2Factor_eq p hz, paper2C2Factor]
  have hg : HasDerivAt (fun z : ℂ => paper2CharPhase p * paper2LatticeNome p z)
      (paper2CharPhase p * (paper2LatticeNome p τ * paper2LatticeNomeRate p)) τ :=
    (hasDerivAt_paper2LatticeNome p τ).const_mul _
  exact (hasFDerivAt_ofReal_im_mul (hasDerivAt_paper2C2Factor p hτ) hg).congr_of_eventuallyEq hev

/-! ## Norms of the individual factors -/

theorem norm_paper2CharPhase (p : ℤ × ℤ) : ‖paper2CharPhase p‖ = 1 := by
  rw [paper2CharPhase_eq, norm_mul, norm_zpow]
  have h1 : ‖Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5)‖ = 1 := by
    rw [show 3 * (Real.pi : ℂ) * Complex.I / 5 = ((3 * Real.pi / 5 : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.norm_exp, Complex.re_ofReal_mul, Complex.I_re, mul_zero, Real.exp_zero]
  rw [h1, one_mul]
  simp

theorem norm_paper2LatticeNome (p : ℤ × ℤ) (τ : ℂ) :
    ‖paper2LatticeNome p τ‖
      = Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) *
          τ.im) := by
  have hre : (Complex.I * τ).re = -τ.im := by simp [Complex.mul_re]
  rw [paper2LatticeNome,
    show 2 * (Real.pi : ℂ) * Complex.I * τ *
        ((paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ) : ℂ)
      = ((2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ) : ℂ) *
          (Complex.I * τ) by push_cast; ring,
    Complex.norm_exp, Complex.re_ofReal_mul, hre]
  congr 1
  ring

/-- The longitudinal coordinate `n = 5x+15y+4` is congruent to `4` modulo `5`
and therefore never zero.  This removes the only possible degeneracy in the
`c₂` derivative bound. -/
theorem paper2LongCoord_ne_zero (x y : ℤ) : paper2LongCoord x y ≠ 0 := by
  unfold paper2LongCoord
  omega

theorem one_le_abs_paper2LongCoord (x y : ℤ) :
    (1 : ℝ) ≤ |(paper2LongCoord x y : ℝ)| := by
  rcases lt_or_gt_of_ne (paper2LongCoord_ne_zero x y) with h | h
  · have hle : (paper2LongCoord x y : ℝ) ≤ -1 := by
      exact_mod_cast (by omega : paper2LongCoord x y ≤ -1)
    rw [abs_of_neg (by linarith)]
    linarith
  · have hle : (1 : ℝ) ≤ (paper2LongCoord x y : ℝ) := by
      exact_mod_cast (by omega : (1 : ℤ) ≤ paper2LongCoord x y)
    rw [abs_of_pos (by linarith)]
    linarith

/-! ## The uniform majorant on a strip -/

/-- Gaussian moments over `ℤ`: for `c>0` and every `k`, the family
`m ↦ |m|^k e^{-πc m²}` is summable. -/
theorem summable_abs_pow_mul_exp_neg_pi_mul_sq {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Summable (fun m : ℤ => |(m : ℝ)| ^ k * Real.exp (-Real.pi * c * (m : ℝ) ^ 2)) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) hc k).congr fun m => ?_
  simp only [Int.cast_abs, mul_zero, zero_mul, sub_zero]
  congr 2
  ring

/-- The uniform majorant for the termwise derivative, in the `(T,n)`
coordinates. -/
noncomputable def paper2C2FderivBoundNT (Y₀ : ℝ) (z : ℤ × ℤ) : ℝ :=
  (|(z.2 : ℝ)| / Real.sqrt (10 * Y₀) +
      2 / Real.sqrt (Y₀ / 10) * ((z.1 : ℝ) ^ 2 / 8 + (z.2 : ℝ) ^ 2 / 40)) *
    (Real.exp (-Real.pi * (Y₀ / 20) * (z.2 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (Y₀ / 4) * (z.1 : ℝ) ^ 2))

/-- The uniform majorant, indexed by the original lattice. -/
noncomputable def paper2C2FderivBound (Y₀ : ℝ) (p : ℤ × ℤ) : ℝ :=
  paper2C2FderivBoundNT Y₀ (paper2NT p)

theorem summable_paper2C2FderivBoundNT {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun z : ℤ × ℤ => paper2C2FderivBoundNT Y₀ z) := by
  have ha : 0 < Y₀ / 20 := by positivity
  have hb : 0 < Y₀ / 4 := by positivity
  have h1 : Summable (fun z : ℤ × ℤ =>
      (|(z.1 : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 4) * (z.1 : ℝ) ^ 2)) *
        ((Real.sqrt (10 * Y₀))⁻¹ *
          (|(z.2 : ℝ)| ^ 1 * Real.exp (-Real.pi * (Y₀ / 20) * (z.2 : ℝ) ^ 2)))) :=
    Summable.mul_of_nonneg
      (f := fun m : ℤ => |(m : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 4) * (m : ℝ) ^ 2))
      (g := fun m : ℤ => (Real.sqrt (10 * Y₀))⁻¹ *
        (|(m : ℝ)| ^ 1 * Real.exp (-Real.pi * (Y₀ / 20) * (m : ℝ) ^ 2)))
      (summable_abs_pow_mul_exp_neg_pi_mul_sq hb 0)
      ((summable_abs_pow_mul_exp_neg_pi_mul_sq ha 1).mul_left (Real.sqrt (10 * Y₀))⁻¹)
      (fun m => by positivity) (fun m => by positivity)
  have h2 : Summable (fun z : ℤ × ℤ =>
      (2 / Real.sqrt (Y₀ / 10) / 8 *
          (|(z.1 : ℝ)| ^ 2 * Real.exp (-Real.pi * (Y₀ / 4) * (z.1 : ℝ) ^ 2))) *
        (|(z.2 : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 20) * (z.2 : ℝ) ^ 2))) :=
    Summable.mul_of_nonneg
      (f := fun m : ℤ => 2 / Real.sqrt (Y₀ / 10) / 8 *
        (|(m : ℝ)| ^ 2 * Real.exp (-Real.pi * (Y₀ / 4) * (m : ℝ) ^ 2)))
      (g := fun m : ℤ => |(m : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 20) * (m : ℝ) ^ 2))
      ((summable_abs_pow_mul_exp_neg_pi_mul_sq hb 2).mul_left (2 / Real.sqrt (Y₀ / 10) / 8))
      (summable_abs_pow_mul_exp_neg_pi_mul_sq ha 0)
      (fun m => by positivity) (fun m => by positivity)
  have h3 : Summable (fun z : ℤ × ℤ =>
      (|(z.1 : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 4) * (z.1 : ℝ) ^ 2)) *
        (2 / Real.sqrt (Y₀ / 10) / 40 *
          (|(z.2 : ℝ)| ^ 2 * Real.exp (-Real.pi * (Y₀ / 20) * (z.2 : ℝ) ^ 2)))) :=
    Summable.mul_of_nonneg
      (f := fun m : ℤ => |(m : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 4) * (m : ℝ) ^ 2))
      (g := fun m : ℤ => 2 / Real.sqrt (Y₀ / 10) / 40 *
        (|(m : ℝ)| ^ 2 * Real.exp (-Real.pi * (Y₀ / 20) * (m : ℝ) ^ 2)))
      (summable_abs_pow_mul_exp_neg_pi_mul_sq hb 0)
      ((summable_abs_pow_mul_exp_neg_pi_mul_sq ha 2).mul_left (2 / Real.sqrt (Y₀ / 10) / 40))
      (fun m => by positivity) (fun m => by positivity)
  refine ((h1.add h2).add h3).congr fun z => ?_
  simp only [paper2C2FderivBoundNT, pow_zero, pow_one, one_mul, sq_abs]
  ring

theorem summable_paper2C2FderivBound {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun p : ℤ × ℤ => paper2C2FderivBound Y₀ p) :=
  (summable_paper2C2FderivBoundNT hY₀).comp_injective paper2NT_injective

/-- The uniform-on-a-strip operator-norm bound.  The Mills bound and the
weight growth combine to the Gaussian `e^{-πYn²/20-πYT²/4}`; the factor `|n|`
from the kernel derivative and the factor `|Q₀(v)| ≤ T²/8+n²/40` from the
holomorphic rate are polynomial, and `|n| ≥ 1` removes the only possible
degeneracy. -/
theorem norm_paper2C2Fderiv_le {Y₀ : ℝ} (hY₀ : 0 < Y₀) (p : ℤ × ℤ) {τ : ℂ}
    (hτ : Y₀ < τ.im) : ‖paper2C2Fderiv p τ‖ ≤ paper2C2FderivBound Y₀ p := by
  have hY : 0 < τ.im := hY₀.trans hτ
  have hQ : paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)
      = (paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
        (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40 := paper2Q0_shift p.1 p.2
  have hn1 : (1 : ℝ) ≤ |(paper2LongCoord p.1 p.2 : ℝ)| := one_le_abs_paper2LongCoord p.1 p.2
  have hnne : ((paper2LongCoord p.1 p.2 : ℝ)) ≠ 0 :=
    Int.cast_ne_zero.2 (paper2LongCoord_ne_zero p.1 p.2)
  have hs10 : 0 < Real.sqrt (10 * τ.im) := Real.sqrt_pos.2 (by positivity)
  have hsY : 0 < Real.sqrt (τ.im / 10) := Real.sqrt_pos.2 (by positivity)
  have hs10' : 0 < Real.sqrt (10 * Y₀) := Real.sqrt_pos.2 (by positivity)
  have hsY' : 0 < Real.sqrt (Y₀ / 10) := Real.sqrt_pos.2 (by positivity)
  have hexpsplit : Real.exp (-Real.pi * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 * τ.im / 10) *
        Real.exp (-(2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
          (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40)) * τ.im)
      = Real.exp (-Real.pi * (τ.im / 20) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2) *
        Real.exp (-Real.pi * (τ.im / 4) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hQabs : |(paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
        (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40|
      ≤ (paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 +
        (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg ((paper2TransCoord p.1 p.2 : ℝ)),
        sq_nonneg ((paper2LongCoord p.1 p.2 : ℝ))]
  have hrate : ‖paper2LatticeNomeRate p‖
      = 2 * Real.pi * |(paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
          (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40| := by
    rw [paper2LatticeNomeRate, hQ,
      show (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          ((((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
            (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40 : ℝ)) : ℂ)
        = ((2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
            (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hA : ‖((paper2C2FactorDeriv p τ : ℝ) : ℂ) *
        (paper2CharPhase p * paper2LatticeNome p τ)‖
      = |(paper2LongCoord p.1 p.2 : ℝ)| / Real.sqrt (10 * τ.im) *
        (Real.exp (-Real.pi * (τ.im / 20) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2) *
          Real.exp (-Real.pi * (τ.im / 4) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_paper2CharPhase,
      one_mul, norm_paper2LatticeNome, hQ, paper2C2FactorDeriv, abs_mul, abs_div, abs_neg,
      abs_of_pos (Real.exp_pos _), abs_of_pos hs10, mul_assoc, hexpsplit]
  have hden : Real.pi * (1 * Real.sqrt (τ.im / 10))
      ≤ Real.pi * (|(paper2LongCoord p.1 p.2 : ℝ)| * Real.sqrt (τ.im / 10)) := by
    nlinarith [mul_pos Real.pi_pos hsY, hn1]
  have hKabs : |paper2C2Factor (paper2LongCoord p.1 p.2) τ|
      ≤ Real.exp (-Real.pi * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 * τ.im / 10) /
          (Real.pi * (1 * Real.sqrt (τ.im / 10))) := by
    refine (abs_paper2BoundaryCorrection_le hnne hY).trans ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hden) (Real.exp_pos _).le
  have hB : ‖((paper2C2Factor (paper2LongCoord p.1 p.2) τ : ℝ) : ℂ) *
        (paper2CharPhase p * (paper2LatticeNome p τ * paper2LatticeNomeRate p))‖
      ≤ 2 / Real.sqrt (τ.im / 10) *
          ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 +
            (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40) *
        (Real.exp (-Real.pi * (τ.im / 20) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2) *
          Real.exp (-Real.pi * (τ.im / 4) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2)) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_paper2CharPhase, one_mul, norm_paper2LatticeNome, hQ, hrate]
    have hstep : |paper2C2Factor (paper2LongCoord p.1 p.2) τ| *
          (Real.exp (-(2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
              (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40)) * τ.im) *
            (2 * Real.pi * |(paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
              (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40|))
        ≤ Real.exp (-Real.pi * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 * τ.im / 10) /
            (Real.pi * (1 * Real.sqrt (τ.im / 10))) *
          (Real.exp (-(2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 -
              (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40)) * τ.im) *
            (2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 +
              (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40))) := by
      refine mul_le_mul hKabs ?_ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hQabs (by positivity)) (Real.exp_pos _).le
    refine hstep.trans (le_of_eq ?_)
    rw [← hexpsplit]
    field_simp
  have e1 : Real.exp (-Real.pi * (τ.im / 20) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2)
      ≤ Real.exp (-Real.pi * (Y₀ / 20) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2) := by
    refine Real.exp_le_exp.2 ?_
    have h3 : 0 ≤ Real.pi * (τ.im - Y₀) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_nonneg _)
    linarith
  have e2 : Real.exp (-Real.pi * (τ.im / 4) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2)
      ≤ Real.exp (-Real.pi * (Y₀ / 4) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2) := by
    refine Real.exp_le_exp.2 ?_
    have h3 : 0 ≤ Real.pi * (τ.im - Y₀) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_nonneg _)
    linarith
  have c1 : |(paper2LongCoord p.1 p.2 : ℝ)| / Real.sqrt (10 * τ.im)
      ≤ |(paper2LongCoord p.1 p.2 : ℝ)| / Real.sqrt (10 * Y₀) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ hs10' (Real.sqrt_le_sqrt (by linarith))) (abs_nonneg _)
  have c2 : 2 / Real.sqrt (τ.im / 10) ≤ 2 / Real.sqrt (Y₀ / 10) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ hsY' (Real.sqrt_le_sqrt (by linarith))) (by norm_num)
  calc ‖paper2C2Fderiv p τ‖
      ≤ ‖((paper2C2FactorDeriv p τ : ℝ) : ℂ) *
            (paper2CharPhase p * paper2LatticeNome p τ)‖ +
          ‖((paper2C2Factor (paper2LongCoord p.1 p.2) τ : ℝ) : ℂ) *
            (paper2CharPhase p *
              (paper2LatticeNome p τ * paper2LatticeNomeRate p))‖ :=
        norm_paper2ImLin_le _ _
    _ ≤ (|(paper2LongCoord p.1 p.2 : ℝ)| / Real.sqrt (10 * τ.im) +
          2 / Real.sqrt (τ.im / 10) *
            ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 +
              (paper2LongCoord p.1 p.2 : ℝ) ^ 2 / 40)) *
        (Real.exp (-Real.pi * (τ.im / 20) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2) *
          Real.exp (-Real.pi * (τ.im / 4) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2)) := by
        rw [hA]
        linarith [hB]
    _ ≤ paper2C2FderivBound Y₀ p := by
        simp only [paper2C2FderivBound, paper2C2FderivBoundNT, paper2NT]
        refine mul_le_mul (add_le_add c1 (mul_le_mul_of_nonneg_right c2 (by positivity)))
          (mul_le_mul e1 e2 (Real.exp_pos _).le (Real.exp_pos _).le)
          (by positivity) (by positivity)

/-! ## Differentiation under the sum, and the Wirtinger projection -/

theorem summable_paper2C2Fderiv {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ => paper2C2Fderiv p τ) :=
  (summable_paper2C2FderivBound (show (0 : ℝ) < τ.im / 2 by positivity)).of_norm_bounded
    fun p => norm_paper2C2Fderiv_le (by positivity) p (by linarith)

/-- Differentiation under the sum, on the strip `{Y₀ < Im τ}`. -/
theorem hasFDerivAt_tsum_paper2LatticeC2Term_strip {Y₀ : ℝ} (hY₀ : 0 < Y₀) {τ : ℂ}
    (hτ : Y₀ < τ.im) :
    HasFDerivAt (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeC2Term p z)
      (∑' p : ℤ × ℤ, paper2C2Fderiv p τ) τ := by
  have hopen : IsOpen {z : ℂ | Y₀ < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected {z : ℂ | Y₀ < z.im} :=
    (convex_halfSpace_im_gt (r := Y₀)).isPreconnected
  exact hasFDerivAt_tsum_of_isPreconnected (summable_paper2C2FderivBound hY₀) hopen hconn
    (fun p z hz => hasFDerivAt_paper2LatticeC2Term p (hY₀.trans hz))
    (fun p z hz => norm_paper2C2Fderiv_le hY₀ p hz) hτ
    (summable_paper2LatticeC2Term (hY₀.trans hτ)) hτ

/-- Differentiation under the sum on the whole upper half-plane. -/
theorem hasFDerivAt_tsum_paper2LatticeC2Term {τ : ℂ} (hτ : 0 < τ.im) :
    HasFDerivAt (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeC2Term p z)
      (∑' p : ℤ × ℤ, paper2C2Fderiv p τ) τ :=
  hasFDerivAt_tsum_paper2LatticeC2Term_strip
    (show (0 : ℝ) < τ.im / 2 by positivity) (by linarith)

/-- **The anti-holomorphic derivative of the `c₂` correction series.**  The
holomorphic weight `q^{Q₀(v)}` contributes nothing, so only the `Y`-derivative
of the error-kernel factor survives, termwise.

This is a statement about the explicit convergent lattice sum; it does not
formalize Zwegers' completion theorem or the `T`/`S` transformation laws. -/
theorem dbar_tsum_paper2LatticeC2Term {τ : ℂ} (hτ : 0 < τ.im) :
    dbar (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeC2Term p z) τ
      = ∑' p : ℤ × ℤ, Complex.I * (((paper2C2FactorDeriv p τ : ℝ) : ℂ) *
          (paper2CharPhase p * paper2LatticeNome p τ)) / 2 := by
  rw [dbar, (hasFDerivAt_tsum_paper2LatticeC2Term hτ).fderiv,
    ContinuousLinearMap.map_tsum wirtingerBarCLM (summable_paper2C2Fderiv hτ)]
  refine tsum_congr fun p => ?_
  rw [wirtingerBarCLM_apply, paper2C2Fderiv, dbar_paper2ImLin]

/-- The same statement with the kernel derivative expanded, matching the
manuscript's `-in/(2√(10Y)) e^{-πn²Y/10}` factor. -/
theorem dbar_tsum_paper2LatticeC2Term_explicit {τ : ℂ} (hτ : 0 < τ.im) :
    dbar (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeC2Term p z) τ
      = ∑' p : ℤ × ℤ,
          -Complex.I * (paper2LongCoord p.1 p.2 : ℂ) /
              (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)) *
            ((Real.exp (-Real.pi * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 * τ.im / 10) : ℝ) : ℂ) *
            (paper2CharPhase p * paper2LatticeNome p τ) := by
  rw [dbar_tsum_paper2LatticeC2Term hτ]
  refine tsum_congr fun p => ?_
  have hs10 : (0 : ℝ) < Real.sqrt (10 * τ.im) := Real.sqrt_pos.2 (by positivity)
  have hs10' : ((Real.sqrt (10 * τ.im) : ℝ) : ℂ) ≠ 0 := by
    simpa using hs10.ne'
  rw [paper2C2FactorDeriv]
  push_cast
  field_simp

/-! ## The `T`-transformation of the lattice sum

For this explicit lattice sum the `T`-law is elementary and needs no Zwegers
input.  Under `τ ↦ τ+1` the imaginary part is unchanged, so both the
error-kernel argument and the characteristic phase are unchanged; only the
weight `q^{Q₀(v)}` moves.  Since `(x+1/2)² = (x²+x) + 1/4` with `x²+x` even
and `5(y+1/10)² = (5y²+y) + 1/20` with `5y²+y` even, `Q₀(v) - 1/10` is an
integer for *every* lattice point, so the weight acquires the single constant
factor `e^{πi/5}`.

These statements are proved directly from the lattice sum and do **not**
invoke Zwegers' Corollary 2.9.  The `S`-transformation law is not claimed
here, and nothing below asserts Zwegers' completion theorem. -/

theorem paper2_even_sq_add (x : ℤ) : Even (x ^ 2 + x) := by
  rcases Int.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨2 * k ^ 2 + k, by subst hk; ring⟩
  · exact ⟨2 * k ^ 2 + 3 * k + 1, by subst hk; ring⟩

theorem paper2_even_five_sq_add (y : ℤ) : Even (5 * y ^ 2 + y) := by
  rcases Int.even_or_odd y with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨10 * k ^ 2 + k, by subst hk; ring⟩
  · exact ⟨10 * k ^ 2 + 11 * k + 3, by subst hk; ring⟩

/-- For every lattice point `Q₀(v) - 1/10` is an integer. -/
theorem paper2Q0_shift_sub_int (x y : ℤ) :
    ∃ k : ℤ, paper2Q0 ((x : ℝ) + 1 / 2) ((y : ℝ) + 1 / 10) = (k : ℝ) + 1 / 10 := by
  obtain ⟨a, ha⟩ := paper2_even_sq_add x
  obtain ⟨b, hb⟩ := paper2_even_five_sq_add y
  have ha' : ((x : ℝ)) ^ 2 + (x : ℝ) = (a : ℝ) + (a : ℝ) := by exact_mod_cast ha
  have hb' : 5 * ((y : ℝ)) ^ 2 + (y : ℝ) = (b : ℝ) + (b : ℝ) := by exact_mod_cast hb
  refine ⟨a - b, ?_⟩
  unfold paper2Q0
  push_cast
  linear_combination (1 / 2 : ℝ) * ha' - (1 / 2 : ℝ) * hb'

/-- Under `τ ↦ τ+1` the lattice weight acquires the constant factor
`e^{πi/5}`, uniformly in the lattice point. -/
theorem paper2LatticeNome_add_one (p : ℤ × ℤ) (τ : ℂ) :
    paper2LatticeNome p (τ + 1)
      = Complex.exp (Real.pi * Complex.I / 5) * paper2LatticeNome p τ := by
  obtain ⟨k, hk⟩ := paper2Q0_shift_sub_int p.1 p.2
  rw [paper2LatticeNome, paper2LatticeNome, hk,
    show 2 * (Real.pi : ℂ) * Complex.I * (τ + 1) * (((k : ℝ) + 1 / 10 : ℝ) : ℂ)
      = Real.pi * Complex.I / 5 +
          2 * (Real.pi : ℂ) * Complex.I * τ * (((k : ℝ) + 1 / 10 : ℝ) : ℂ) +
          (k : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem paper2LatticeC2Term_add_one (p : ℤ × ℤ) (τ : ℂ) :
    paper2LatticeC2Term p (τ + 1)
      = Complex.exp (Real.pi * Complex.I / 5) * paper2LatticeC2Term p τ := by
  have him : (τ + 1).im = τ.im := by simp
  rw [paper2LatticeC2Term, paper2LatticeC2Term, him, paper2LatticeNome_add_one]
  ring

theorem paper2LatticeC1Term_add_one (p : ℤ × ℤ) (τ : ℂ) :
    paper2LatticeC1Term p (τ + 1)
      = Complex.exp (Real.pi * Complex.I / 5) * paper2LatticeC1Term p τ := by
  have him : (τ + 1).im = τ.im := by simp
  rw [paper2LatticeC1Term, paper2LatticeC1Term, him, paper2LatticeNome_add_one]
  ring

/-- **`T`-transformation of the `c₂` correction series**, proved directly from
the lattice sum without Zwegers' Corollary 2.9. -/
theorem paper2LatticeC2_tsum_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' p : ℤ × ℤ, paper2LatticeC2Term p (τ + 1))
      = Complex.exp (Real.pi * Complex.I / 5) *
          ∑' p : ℤ × ℤ, paper2LatticeC2Term p τ := by
  rw [← (summable_paper2LatticeC2Term hτ).tsum_mul_left]
  exact tsum_congr fun p => paper2LatticeC2Term_add_one p τ

/-- **`T`-transformation of the full Zwegers Definition 2.1 boundary
correction**, again directly from the lattice sum. -/
theorem paper2Lattice_tsum_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' p : ℤ × ℤ, (paper2LatticeC2Term p (τ + 1) - paper2LatticeC1Term p (τ + 1)))
      = Complex.exp (Real.pi * Complex.I / 5) *
          ∑' p : ℤ × ℤ, (paper2LatticeC2Term p τ - paper2LatticeC1Term p τ) := by
  rw [← (summable_paper2LatticeTerm hτ).tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [paper2LatticeC2Term_add_one, paper2LatticeC1Term_add_one]
  ring

/-! ## The four-block form of the boundary derivative

The termwise `∂/∂τ̄` of the previous section is rewritten here into the
manuscript's `Σ_j (-1)^j θ_j(τ) conj(g_j(τ))`.  Two ingredients: the phase
identity `e^{-πn²Y/10} q^{-n²/40} = conj(q^{n²/40})`, and the same
`(T,n)`-reindexing used for the lattice-to-block bridge.

As everywhere in this file, these are statements about an explicit convergent
lattice sum.  Nothing here asserts Zwegers' completion theorem or his `S`
transformation law. -/

/-- The phase identity behind the shadow:
`e^{-πn²Y/10}·q^{-n²/40} = conj(q^{n²/40})` with `τ = X + iY`.  Both sides are
computed as single complex exponentials; no absolute value is used. -/
theorem exp_mul_paper2LongNome_eq_conj (n : ℤ) (τ : ℂ) :
    ((Real.exp (-Real.pi * (n : ℝ) ^ 2 * τ.im / 10) : ℝ) : ℂ) * paper2LongNome n τ
      = (starRingEnd ℂ)
          (Complex.exp (2 * Real.pi * Complex.I * τ * ((n : ℂ) ^ 2 / 40))) := by
  have hconj : (starRingEnd ℂ) τ = τ - 2 * Complex.I * (τ.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [Complex.ofReal_exp, paper2LongNome, ← Complex.exp_add, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_div₀, map_ofNat, map_pow, map_intCast, Complex.conj_I,
    Complex.conj_ofReal, hconj]
  push_cast
  linear_combination
    (-((Real.pi : ℂ) * (n : ℂ) ^ 2 * (τ.im : ℂ) / 10)) * Complex.I_sq

/-- The longitudinal Jacobi summand is the nome `q^{n²/40}`. -/
theorem jacobiTheta₂_term_eq_longPositiveNome (n : ℤ) (τ : ℂ) :
    jacobiTheta₂_term n 0 (τ / 20)
      = Complex.exp (2 * Real.pi * Complex.I * τ * ((n : ℂ) ^ 2 / 40)) := by
  rw [jacobiTheta₂_term]
  congr 1
  ring

/-- The longitudinal shadow summand depends only on `j mod 4`. -/
theorem paper2GTerm_congr {j j' : ℤ} (h : j % 4 = j' % 4) (n : ℤ) (τ : ℂ) :
    paper2GTerm j n τ = paper2GTerm j' n τ := by
  unfold paper2GTerm
  by_cases hn : paper2GResidue j n
  · rw [if_pos hn, if_pos ((paper2GResidue_congr h n).1 hn)]
  · rw [if_neg hn, if_neg fun hc => hn ((paper2GResidue_congr h n).2 hc)]

/-- The residue-`j` shadow block summand `θ_j`-term times the conjugated
`g_j`-term, in the `(T,n)` coordinates. -/
def paper2ShadowBlockTerm (j : ℤ) (z : ℤ × ℤ) (τ : ℂ) : ℂ :=
  paper2ThetaTerm j z.1 τ * (starRingEnd ℂ) (paper2GTerm j z.2 τ)

theorem paper2ShadowBlockTerm_congr {j j' : ℤ} (h : j % 4 = j' % 4) (z : ℤ × ℤ) (τ : ℂ) :
    paper2ShadowBlockTerm j z τ = paper2ShadowBlockTerm j' z τ := by
  rw [paper2ShadowBlockTerm, paper2ShadowBlockTerm, paper2ThetaTerm_congr h,
    paper2GTerm_congr h]

theorem paper2ShadowBlockTerm_paper2NT_eq_zero {j : ℤ} (p : ℤ × ℤ) (τ : ℂ)
    (h : paper2CosetLabel p.1 p.2 % 4 ≠ j % 4) :
    paper2ShadowBlockTerm j (paper2NT p) τ = 0 := by
  have hres : ¬paper2GResidue j (paper2LongCoord p.1 p.2) := fun hc =>
    h (paper2CosetLabel_unique (paper2GResidue_longCoord p.1 p.2) hc)
  simp only [paper2ShadowBlockTerm, paper2NT, paper2GTerm, if_neg hres, map_zero, mul_zero]

/-- On its own residue block the shadow summand is the transverse Jacobi term
times `n·conj(q^{n²/40})`. -/
theorem paper2ShadowBlockTerm_paper2NT (p : ℤ × ℤ) (τ : ℂ) :
    paper2ShadowBlockTerm (paper2CosetLabel p.1 p.2) (paper2NT p) τ
      = jacobiTheta₂_term (paper2TransCoord p.1 p.2) 0 (τ / 4) *
          ((paper2LongCoord p.1 p.2 : ℂ) *
            (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * τ *
              ((paper2LongCoord p.1 p.2 : ℂ) ^ 2 / 40)))) := by
  simp only [paper2ShadowBlockTerm, paper2NT, paper2ThetaTerm,
    if_pos (paper2ThetaResidue_transCoord p.1 p.2), paper2GTerm,
    if_pos (paper2GResidue_longCoord p.1 p.2), jacobiTheta₂_term_eq_longPositiveNome,
    map_mul, map_intCast]

/-- Each lattice point contributes to exactly one shadow block. -/
theorem sum_paper2ShadowBlockTerm_paper2NT (p : ℤ × ℤ) (τ : ℂ) :
    ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ
      = ((-1 : ℂ)) ^ paper2CosetLabel p.1 p.2 *
          paper2ShadowBlockTerm (paper2CosetLabel p.1 p.2) (paper2NT p) τ := by
  have hmem : (paper2CosetLabel p.1 p.2 % 4).toNat ∈ Finset.range 4 := by
    simp only [Finset.mem_range]
    omega
  have hcast : (((paper2CosetLabel p.1 p.2 % 4).toNat : ℤ)) % 4
      = paper2CosetLabel p.1 p.2 % 4 := by omega
  have hzero : ∀ b ∈ Finset.range 4, b ≠ (paper2CosetLabel p.1 p.2 % 4).toNat →
      (-1 : ℂ) ^ b * paper2ShadowBlockTerm (b : ℤ) (paper2NT p) τ = 0 := by
    intro b hb hbne
    simp only [Finset.mem_range] at hb
    have hne : paper2CosetLabel p.1 p.2 % 4 ≠ (b : ℤ) % 4 := by omega
    rw [paper2ShadowBlockTerm_paper2NT_eq_zero p τ hne, mul_zero]
  rw [Finset.sum_eq_single_of_mem _ hmem hzero, paper2ShadowBlockTerm_congr hcast]
  congr 1
  rw [← zpow_natCast ((-1 : ℂ)) ((paper2CosetLabel p.1 p.2 % 4).toNat)]
  exact neg_one_zpow_congr hcast

theorem summable_norm_conj_paper2GTerm (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖(starRingEnd ℂ) (paper2GTerm j n τ)‖) := by
  refine ((summable_paper2GTerm j hτ).norm).congr fun n => ?_
  rw [RCLike.norm_conj]

theorem summable_paper2ShadowBlock (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun z : ℤ × ℤ => paper2ShadowBlockTerm j z τ) :=
  summable_mul_of_summable_norm (R := ℂ)
    (f := fun T : ℤ => paper2ThetaTerm j T τ)
    (g := fun n : ℤ => (starRingEnd ℂ) (paper2GTerm j n τ))
    (summable_norm_paper2ThetaTerm j hτ) (summable_norm_conj_paper2GTerm j hτ)

/-- Each shadow block sums to `θ_j(τ)·conj(g_j(τ))`. -/
theorem tsum_paper2ShadowBlockTerm_eq (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' z : ℤ × ℤ, paper2ShadowBlockTerm j z τ)
      = paper2ThetaComponent j τ * (starRingEnd ℂ) (paper2GComponent j τ) := by
  rw [paper2ThetaComponent, paper2GComponent, RCLike.conj_tsum]
  exact (tsum_mul_tsum_of_summable_norm (R := ℂ)
    (f := fun T : ℤ => paper2ThetaTerm j T τ)
    (g := fun n : ℤ => (starRingEnd ℂ) (paper2GTerm j n τ))
    (summable_norm_paper2ThetaTerm j hτ) (summable_norm_conj_paper2GTerm j hτ)).symm

theorem tsum_paper2ShadowBlockTerm_paper2NT (j : ℤ) (τ : ℂ) :
    (∑' p : ℤ × ℤ, paper2ShadowBlockTerm j (paper2NT p) τ)
      = ∑' z : ℤ × ℤ, paper2ShadowBlockTerm j z τ := by
  have hsupp : Function.support (fun z : ℤ × ℤ => paper2ShadowBlockTerm j z τ)
      ⊆ Set.range paper2NT := by
    intro z hz
    have hz' : paper2ShadowBlockTerm j z τ ≠ 0 := hz
    have hT : paper2ThetaResidue j z.1 := by
      by_contra hc
      exact hz' (by simp only [paper2ShadowBlockTerm, paper2ThetaTerm, if_neg hc, zero_mul])
    have hn : paper2GResidue j z.2 := by
      by_contra hc
      exact hz' (by
        simp only [paper2ShadowBlockTerm, paper2GTerm, if_neg hc, map_zero, mul_zero])
    obtain ⟨x, y, hx, hy⟩ := paper2Coord_surjective hn hT
    exact ⟨(x, y), by simp [paper2NT, hx, hy]⟩
  exact Function.Injective.tsum_eq (f := fun z : ℤ × ℤ => paper2ShadowBlockTerm j z τ)
    paper2NT_injective hsupp

/-- Termwise: the `∂/∂τ̄` summand is the constant `-ie^{3πi/5}/(2√(10Y))`
times the `(-1)^j`-weighted shadow block summand. -/
theorem paper2LatticeC2Shadow_term (p : ℤ × ℤ) (τ : ℂ) :
    -Complex.I * (paper2LongCoord p.1 p.2 : ℂ) /
          (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)) *
        ((Real.exp (-Real.pi * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 * τ.im / 10) : ℝ) : ℂ) *
        (paper2CharPhase p * paper2LatticeNome p τ)
      = -(Complex.I * Complex.exp (3 * Real.pi * Complex.I / 5) /
            (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ := by
  rw [sum_paper2ShadowBlockTerm_paper2NT, paper2ShadowBlockTerm_paper2NT,
    paper2CharPhase_eq, paper2Sign_eq_cosetLabel, paper2LatticeNome_eq,
    ← jacobiTheta₂_term_mul_paper2LongNome, ← exp_mul_paper2LongNome_eq_conj]
  ring

/-- **The manuscript's `∂/∂τ̄` formula for the `c₂` series.**  Statement about
the explicit convergent lattice sum; Zwegers' completion theorem is not
formalized. -/
theorem dbar_tsum_paper2LatticeC2Term_blocks {τ : ℂ} (hτ : 0 < τ.im) :
    dbar (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeC2Term p z) τ
      = -(Complex.I * Complex.exp (3 * Real.pi * Complex.I / 5) /
            (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)))
        * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2ThetaComponent (j : ℤ) τ *
            (starRingEnd ℂ) (paper2GComponent (j : ℤ) τ) := by
  have hblock : ∀ j ∈ Finset.range 4,
      Summable (fun p : ℤ × ℤ =>
        (-1 : ℂ) ^ j * paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ) := by
    intro j _
    have h0 : Summable (fun z : ℤ × ℤ => paper2ShadowBlockTerm (j : ℤ) z τ) :=
      summable_paper2ShadowBlock (j : ℤ) hτ
    have h1 : Summable (fun p : ℤ × ℤ => paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ) := by
      simpa only [Function.comp_def] using h0.comp_injective paper2NT_injective
    exact h1.mul_left _
  rw [dbar_tsum_paper2LatticeC2Term_explicit hτ]
  calc (∑' p : ℤ × ℤ,
        -Complex.I * (paper2LongCoord p.1 p.2 : ℂ) /
              (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)) *
            ((Real.exp (-Real.pi * (paper2LongCoord p.1 p.2 : ℝ) ^ 2 * τ.im / 10) : ℝ) : ℂ) *
            (paper2CharPhase p * paper2LatticeNome p τ))
      = ∑' p : ℤ × ℤ, -(Complex.I * Complex.exp (3 * Real.pi * Complex.I / 5) /
            (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ :=
        tsum_congr fun p => paper2LatticeC2Shadow_term p τ
    _ = -(Complex.I * Complex.exp (3 * Real.pi * Complex.I / 5) /
            (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
          ∑' p : ℤ × ℤ, ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ :=
        (summable_sum hblock).tsum_mul_left _
    _ = -(Complex.I * Complex.exp (3 * Real.pi * Complex.I / 5) /
            (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
          ∑ j ∈ Finset.range 4, ∑' p : ℤ × ℤ, (-1 : ℂ) ^ j *
            paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ := by
        rw [Summable.tsum_finsetSum hblock]
    _ = -(Complex.I * Complex.exp (3 * Real.pi * Complex.I / 5) /
            (2 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2ThetaComponent (j : ℤ) τ *
            (starRingEnd ℂ) (paper2GComponent (j : ℤ) τ) := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have h0 : Summable (fun z : ℤ × ℤ => paper2ShadowBlockTerm (j : ℤ) z τ) :=
          summable_paper2ShadowBlock (j : ℤ) hτ
        have h1 : Summable (fun p : ℤ × ℤ =>
            paper2ShadowBlockTerm (j : ℤ) (paper2NT p) τ) := by
          simpa only [Function.comp_def] using h0.comp_injective paper2NT_injective
        rw [h1.tsum_mul_left, tsum_paper2ShadowBlockTerm_paper2NT,
          tsum_paper2ShadowBlockTerm_eq (j : ℤ) hτ, ← mul_assoc]

/-! ## The normalized lattice sum, its `∂/∂τ̄`, and `⟨T⟩`-quasiperiodicity -/

/-- The lattice-side **boundary correction**: the explicit sum over the
shifted lattice of the `(E - sgn)` halves of Zwegers' Definition 2.1 summand
at this paper's data `a=(1/2,1/10)`, `b=(1/2,-1/10)`, `c₂=(-5,3)`, `c₁=(0,1)`,
normalized by the manuscript's constant `½e^{-3πi/5}`.

Splitting `(E₂-E₁) = (E₂-sgn₂) - (E₁-sgn₁) + (sgn₂-sgn₁)` shows that this is
Zwegers' `Θ` *minus its sign part*, i.e. exactly the nonholomorphic boundary
correction; `paper2Lattice_tsum_eq` identifies it with the four-block
expression `paper2C2Correction`.  It is deliberately **not** called a
completed theta: this is a **definition** of a lattice sum and nothing more.
Zwegers' completion theorem is not formalized anywhere in this repository,
nothing identifies this object with `q^{1/10}B(q)` or with its completion,
and no harmonic Maass property is claimed. -/
noncomputable def paper2LatticeCorrection (τ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
    ∑' p : ℤ × ℤ, (paper2LatticeC2Term p τ - paper2LatticeC1Term p τ)

/-- On the upper half-plane the `c₁` half contributes nothing, so the
normalized object agrees there with a constant multiple of the `c₂` series.
This is an identity of *functions on an open set*, which is what licenses
differentiating it; a vanishing `tsum` at one point would not. -/
theorem paper2LatticeCorrection_eq {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeCorrection τ
      = (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
          ∑' p : ℤ × ℤ, paper2LatticeC2Term p τ := by
  rw [paper2LatticeCorrection,
    Summable.tsum_sub (summable_paper2LatticeC2Term hτ) (summable_paper2LatticeC1Term hτ),
    paper2LatticeC1_tsum_eq_zero hτ, sub_zero]

theorem hasFDerivAt_paper2LatticeCorrection {τ : ℂ} (hτ : 0 < τ.im) :
    HasFDerivAt paper2LatticeCorrection
      (((1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5)) •
        (∑' p : ℤ × ℤ, paper2C2Fderiv p τ)) τ := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : paper2LatticeCorrection =ᶠ[nhds τ]
      fun z : ℂ => (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
        ∑' p : ℤ × ℤ, paper2LatticeC2Term p z := by
    filter_upwards [hopen.mem_nhds hτ] with z hz
    exact paper2LatticeCorrection_eq hz
  exact ((hasFDerivAt_tsum_paper2LatticeC2Term hτ).const_mul _).congr_of_eventuallyEq hev

/-- **The manuscript's `eq:dbar-exact`**, for the explicit normalized lattice
sum.  Zwegers' completion theorem is not formalized, so this says nothing
about the completion of `q^{1/10}B(q)`. -/
theorem paper2_dbar_latticeCorrection {τ : ℂ} (hτ : 0 < τ.im) :
    dbar paper2LatticeCorrection τ
      = -(Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)))
        * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2ThetaComponent (j : ℤ) τ *
            (starRingEnd ℂ) (paper2GComponent (j : ℤ) τ) := by
  have hphase : Complex.exp (-3 * (Real.pi : ℂ) * Complex.I / 5) *
      Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5) = 1 := by
    rw [← Complex.exp_add,
      show -3 * (Real.pi : ℂ) * Complex.I / 5 + 3 * (Real.pi : ℂ) * Complex.I / 5 = 0 by ring]
    exact Complex.exp_zero
  have hd : dbar paper2LatticeCorrection τ
      = (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
        dbar (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeC2Term p z) τ := by
    rw [dbar_of_hasFDerivAt (hasFDerivAt_paper2LatticeCorrection hτ),
      dbar_of_hasFDerivAt (hasFDerivAt_tsum_paper2LatticeC2Term hτ)]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    ring
  rw [hd, dbar_tsum_paper2LatticeC2Term_blocks hτ, ← mul_assoc]
  congr 1
  linear_combination (-(Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)))) * hphase

/-- `⟨T⟩`-quasiperiodicity with multiplier `e^{πi/5}`, proved directly from
the lattice sum.  This detects the multiplier only: for `T = [[1,1],[0,1]]`
the automorphy factor `(cτ+d)^{-k}` equals `1` at every weight, so nothing
here is a weight-one statement, and Zwegers' Corollary 2.9 is not used. -/
theorem paper2LatticeCorrection_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeCorrection (τ + 1)
      = Complex.exp (Real.pi * Complex.I / 5) * paper2LatticeCorrection τ := by
  rw [paper2LatticeCorrection, paper2LatticeCorrection, paper2Lattice_tsum_add_one hτ]
  ring

theorem paper2LatticeCorrection_add_nat {τ : ℂ} (hτ : 0 < τ.im) (m : ℕ) :
    paper2LatticeCorrection (τ + m)
      = Complex.exp ((m : ℂ) * (Real.pi * Complex.I / 5)) * paper2LatticeCorrection τ := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hk : (0 : ℝ) < (τ + (k : ℂ)).im := by simpa using hτ
      have hstep : τ + ((k + 1 : ℕ) : ℂ) = (τ + (k : ℂ)) + 1 := by push_cast; ring
      rw [hstep, paper2LatticeCorrection_add_one hk, ih, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- Genuine periodicity under `τ ↦ τ+10`, since the multiplier has order `10`.
Again a multiplier statement, not a weight statement. -/
theorem paper2LatticeCorrection_add_ten {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeCorrection (τ + 10) = paper2LatticeCorrection τ := by
  have h := paper2LatticeCorrection_add_nat hτ 10
  norm_num at h
  rw [h, show (10 : ℂ) * ((Real.pi : ℂ) * Complex.I / 5) = 2 * (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_two_pi_mul_I, one_mul]

/-! ## The `ξ₁` layer

`ξ₁` is the standard Bruinier–Funke operator in weight one, and `Δ₁` its
associated Laplacian.  `xi1 paper2LatticeCorrection` is a *scalar-valued*
function; writing its value as a sum of four components does not make it a
vector-valued modular object, and no representation law is claimed.  Nothing
is proved about `Delta1` in this file. -/

/-- The Bruinier–Funke operator in weight one, `ξ₁ f = 2iY·conj(∂f/∂τ̄)`. -/
noncomputable def xi1 (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  2 * Complex.I * (τ.im : ℂ) * (starRingEnd ℂ) (dbar f τ)

/-- The weight-one Laplacian `Δ₁ = -ξ₁ ∘ ξ₁`.  Only the definition is given
here; nothing is proved about it in this file. -/
noncomputable def Delta1 (f : ℂ → ℂ) (τ : ℂ) : ℂ := -xi1 (xi1 f) τ

/-- **The manuscript's `eq:xi-exact`**, for the explicit normalized lattice
sum.  The value is scalar; no vector-valued or modular claim is made, and
Zwegers' completion theorem is not formalized. -/
theorem paper2_xi1_latticeCorrection {τ : ℂ} (hτ : 0 < τ.im) :
    xi1 paper2LatticeCorrection τ
      = -(((Real.sqrt τ.im / (2 * Real.sqrt 10) : ℝ)) : ℂ)
        * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) τ) * paper2GComponent (j : ℤ) τ := by
  have hIhelp : ∀ w v : ℂ, 2 * Complex.I * w * (Complex.I / v) = -(2 * w / v) := by
    intro w v
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (2 * w * v⁻¹) * Complex.I_mul_I
  have hkey : τ.im / (2 * Real.sqrt (10 * τ.im)) = Real.sqrt τ.im / (2 * Real.sqrt 10) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10),
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (-2 * Real.sqrt 10) * Real.mul_self_sqrt hτ.le
  have hc : (starRingEnd ℂ) (-(Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))))
      = Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)) := by
    simp only [map_neg, map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hS : (starRingEnd ℂ) (∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
        paper2ThetaComponent (j : ℤ) τ * (starRingEnd ℂ) (paper2GComponent (j : ℤ) τ))
      = ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
          (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) τ) * paper2GComponent (j : ℤ) τ := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
  rw [xi1, paper2_dbar_latticeCorrection hτ, map_mul, hc, hS, ← mul_assoc, hIhelp]
  congr 1
  rw [← hkey]
  push_cast
  ring

/-! ## Holomorphic `τ`-derivatives of the unary theta components

Mathlib has no `τ`-derivative API for `jacobiTheta₂` or `jacobiTheta₂_term`
(only the elliptic variable `z` is covered), so the two components are
differentiated here by the same route as the lattice sum: termwise, with a
polynomial-times-Gaussian majorant uniform on a strip.  These are genuine
`HasDerivAt` statements over `ℂ`; the components are holomorphic.

As everywhere in this file, all statements concern explicit convergent series.
Nothing asserts Zwegers' completion theorem or his `S` transformation law. -/

/-- The transverse Jacobi summand is the nome `q^{T²/8}`. -/
theorem jacobiTheta₂_term_eq_transNome (T : ℤ) (τ : ℂ) :
    jacobiTheta₂_term T 0 (τ / 4)
      = Complex.exp (2 * Real.pi * Complex.I * τ * ((T : ℂ) ^ 2 / 8)) := by
  rw [jacobiTheta₂_term]
  congr 1
  ring

/-- `d/dτ q^{c} = q^{c}·(2πic)`. -/
theorem hasDerivAt_paper2Nome (c : ℂ) (τ : ℂ) :
    HasDerivAt (fun t : ℂ => Complex.exp (2 * Real.pi * Complex.I * t * c))
      (Complex.exp (2 * Real.pi * Complex.I * τ * c) * (2 * Real.pi * Complex.I * c)) τ := by
  have h1 : HasDerivAt (fun t : ℂ => 2 * (Real.pi : ℂ) * Complex.I * t * c)
      (2 * (Real.pi : ℂ) * Complex.I * c) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (2 * (Real.pi : ℂ) * Complex.I)).mul_const c
  exact h1.cexp

theorem norm_transNome (T : ℤ) (τ : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * τ * ((T : ℂ) ^ 2 / 8))‖
      = Real.exp (-Real.pi * (τ.im / 4) * (T : ℝ) ^ 2) := by
  have hre : (Complex.I * τ).re = -τ.im := by simp [Complex.mul_re]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * τ * ((T : ℂ) ^ 2 / 8)
      = ((2 * Real.pi * ((T : ℝ) ^ 2 / 8) : ℝ) : ℂ) * (Complex.I * τ) by push_cast; ring,
    Complex.norm_exp, Complex.re_ofReal_mul, hre]
  congr 1
  ring

theorem norm_longPositiveNome (n : ℤ) (τ : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * τ * ((n : ℂ) ^ 2 / 40))‖
      = Real.exp (-Real.pi * (τ.im / 20) * (n : ℝ) ^ 2) := by
  have hre : (Complex.I * τ).re = -τ.im := by simp [Complex.mul_re]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * τ * ((n : ℂ) ^ 2 / 40)
      = ((2 * Real.pi * ((n : ℝ) ^ 2 / 40) : ℝ) : ℂ) * (Complex.I * τ) by push_cast; ring,
    Complex.norm_exp, Complex.re_ofReal_mul, hre]
  congr 1
  ring

/-- Termwise `τ`-derivative of the transverse summand. -/
noncomputable def paper2ThetaTermDeriv (j T : ℤ) (τ : ℂ) : ℂ :=
  if paper2ThetaResidue j T then
    Complex.exp (2 * Real.pi * Complex.I * τ * ((T : ℂ) ^ 2 / 8)) *
      (2 * Real.pi * Complex.I * ((T : ℂ) ^ 2 / 8))
  else 0

/-- Termwise `τ`-derivative of the longitudinal summand. -/
noncomputable def paper2GTermDeriv (j n : ℤ) (τ : ℂ) : ℂ :=
  if paper2GResidue j n then
    (n : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * τ * ((n : ℂ) ^ 2 / 40)) *
      (2 * Real.pi * Complex.I * ((n : ℂ) ^ 2 / 40)))
  else 0

/-- The `τ`-derivative series of the transverse component. -/
noncomputable def paper2ThetaComponentDeriv (j : ℤ) (τ : ℂ) : ℂ :=
  ∑' T : ℤ, paper2ThetaTermDeriv j T τ

/-- The `τ`-derivative series of the longitudinal component. -/
noncomputable def paper2GComponentDeriv (j : ℤ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, paper2GTermDeriv j n τ

theorem hasDerivAt_paper2ThetaTerm (j T : ℤ) (τ : ℂ) :
    HasDerivAt (fun t : ℂ => paper2ThetaTerm j T t) (paper2ThetaTermDeriv j T τ) τ := by
  by_cases h : paper2ThetaResidue j T
  · simp only [paper2ThetaTerm, paper2ThetaTermDeriv, if_pos h,
      jacobiTheta₂_term_eq_transNome]
    exact hasDerivAt_paper2Nome ((T : ℂ) ^ 2 / 8) τ
  · simp only [paper2ThetaTerm, paper2ThetaTermDeriv, if_neg h]
    exact hasDerivAt_const τ 0

theorem hasDerivAt_paper2GTerm (j n : ℤ) (τ : ℂ) :
    HasDerivAt (fun t : ℂ => paper2GTerm j n t) (paper2GTermDeriv j n τ) τ := by
  by_cases h : paper2GResidue j n
  · simp only [paper2GTerm, paper2GTermDeriv, if_pos h,
      jacobiTheta₂_term_eq_longPositiveNome]
    exact (hasDerivAt_paper2Nome ((n : ℂ) ^ 2 / 40) τ).const_mul _
  · simp only [paper2GTerm, paper2GTermDeriv, if_neg h]
    exact hasDerivAt_const τ 0

theorem norm_paper2ThetaTermDeriv_le (j T : ℤ) {Y₀ : ℝ} {τ : ℂ} (hτ : Y₀ < τ.im) :
    ‖paper2ThetaTermDeriv j T τ‖
      ≤ Real.pi / 4 * ((T : ℝ) ^ 2 * Real.exp (-Real.pi * (Y₀ / 4) * (T : ℝ) ^ 2)) := by
  by_cases h : paper2ThetaResidue j T
  · have hrate : ‖2 * (Real.pi : ℂ) * Complex.I * ((T : ℂ) ^ 2 / 8)‖
        = Real.pi / 4 * (T : ℝ) ^ 2 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((T : ℂ) ^ 2 / 8)
          = ((Real.pi * (T : ℝ) ^ 2 / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      ring
    have hexp : Real.exp (-Real.pi * (τ.im / 4) * (T : ℝ) ^ 2)
        ≤ Real.exp (-Real.pi * (Y₀ / 4) * (T : ℝ) ^ 2) := by
      refine Real.exp_le_exp.2 ?_
      have h3 : 0 ≤ Real.pi * (τ.im - Y₀) * (T : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_nonneg _)
      linarith
    rw [paper2ThetaTermDeriv, if_pos h, norm_mul, norm_transNome, hrate]
    calc Real.exp (-Real.pi * (τ.im / 4) * (T : ℝ) ^ 2) * (Real.pi / 4 * (T : ℝ) ^ 2)
        ≤ Real.exp (-Real.pi * (Y₀ / 4) * (T : ℝ) ^ 2) * (Real.pi / 4 * (T : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = Real.pi / 4 * ((T : ℝ) ^ 2 * Real.exp (-Real.pi * (Y₀ / 4) * (T : ℝ) ^ 2)) := by ring
  · rw [paper2ThetaTermDeriv, if_neg h, norm_zero]
    positivity

theorem norm_paper2GTermDeriv_le (j n : ℤ) {Y₀ : ℝ} {τ : ℂ} (hτ : Y₀ < τ.im) :
    ‖paper2GTermDeriv j n τ‖
      ≤ Real.pi / 20 * (|(n : ℝ)| ^ 3 * Real.exp (-Real.pi * (Y₀ / 20) * (n : ℝ) ^ 2)) := by
  by_cases h : paper2GResidue j n
  · have hcast : ‖((n : ℤ) : ℂ)‖ = |(n : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    have hrate : ‖2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 / 40)‖
        = Real.pi / 20 * (n : ℝ) ^ 2 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) ^ 2 / 40)
          = ((Real.pi * (n : ℝ) ^ 2 / 20 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      ring
    have hexp : Real.exp (-Real.pi * (τ.im / 20) * (n : ℝ) ^ 2)
        ≤ Real.exp (-Real.pi * (Y₀ / 20) * (n : ℝ) ^ 2) := by
      refine Real.exp_le_exp.2 ?_
      have h3 : 0 ≤ Real.pi * (τ.im - Y₀) * (n : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (sq_nonneg _)
      linarith
    have habs : |(n : ℝ)| ^ 3 = |(n : ℝ)| * (n : ℝ) ^ 2 := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, sq_abs]
      ring
    rw [paper2GTermDeriv, if_pos h, norm_mul, norm_mul, hcast, norm_longPositiveNome, hrate,
      habs]
    calc |(n : ℝ)| * (Real.exp (-Real.pi * (τ.im / 20) * (n : ℝ) ^ 2) *
            (Real.pi / 20 * (n : ℝ) ^ 2))
        ≤ |(n : ℝ)| * (Real.exp (-Real.pi * (Y₀ / 20) * (n : ℝ) ^ 2) *
            (Real.pi / 20 * (n : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = Real.pi / 20 * (|(n : ℝ)| * (n : ℝ) ^ 2 *
            Real.exp (-Real.pi * (Y₀ / 20) * (n : ℝ) ^ 2)) := by ring
  · rw [paper2GTermDeriv, if_neg h, norm_zero]
    positivity

theorem summable_paper2ThetaDerivBound {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun T : ℤ =>
      Real.pi / 4 * ((T : ℝ) ^ 2 * Real.exp (-Real.pi * (Y₀ / 4) * (T : ℝ) ^ 2))) := by
  refine ((summable_abs_pow_mul_exp_neg_pi_mul_sq
    (show (0 : ℝ) < Y₀ / 4 by positivity) 2).mul_left (Real.pi / 4)).congr fun T => ?_
  rw [sq_abs]

theorem summable_paper2GDerivBound {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun n : ℤ =>
      Real.pi / 20 * (|(n : ℝ)| ^ 3 * Real.exp (-Real.pi * (Y₀ / 20) * (n : ℝ) ^ 2))) :=
  (summable_abs_pow_mul_exp_neg_pi_mul_sq (show (0 : ℝ) < Y₀ / 20 by positivity) 3).mul_left _

/-- The transverse component is holomorphic on the upper half-plane, with the
termwise derivative series. -/
theorem hasDerivAt_paper2ThetaComponent (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun t : ℂ => paper2ThetaComponent j t) (paper2ThetaComponentDeriv j τ) τ := by
  have hY₀ : (0 : ℝ) < τ.im / 2 := by positivity
  have hmem : τ.im / 2 < τ.im := by linarith
  have hopen : IsOpen {z : ℂ | τ.im / 2 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected {z : ℂ | τ.im / 2 < z.im} :=
    (convex_halfSpace_im_gt (r := τ.im / 2)).isPreconnected
  exact hasDerivAt_tsum_of_isPreconnected (summable_paper2ThetaDerivBound hY₀) hopen hconn
    (fun T z _ => hasDerivAt_paper2ThetaTerm j T z)
    (fun T z hz => norm_paper2ThetaTermDeriv_le j T hz) hmem
    (summable_paper2ThetaTerm j hτ) hmem

/-- The longitudinal component is holomorphic on the upper half-plane, with the
termwise derivative series. -/
theorem hasDerivAt_paper2GComponent (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun t : ℂ => paper2GComponent j t) (paper2GComponentDeriv j τ) τ := by
  have hY₀ : (0 : ℝ) < τ.im / 2 := by positivity
  have hmem : τ.im / 2 < τ.im := by linarith
  have hopen : IsOpen {z : ℂ | τ.im / 2 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected {z : ℂ | τ.im / 2 < z.im} :=
    (convex_halfSpace_im_gt (r := τ.im / 2)).isPreconnected
  exact hasDerivAt_tsum_of_isPreconnected (summable_paper2GDerivBound hY₀) hopen hconn
    (fun n z _ => hasDerivAt_paper2GTerm j n z)
    (fun n z hz => norm_paper2GTermDeriv_le j n hz) hmem
    (summable_paper2GTerm j hτ) hmem

/-! ## `dbar` calculus: sums, products, holomorphic and anti-holomorphic factors -/

theorem dbar_congr_of_eventuallyEq {f g : ℂ → ℂ} {τ : ℂ} (h : f =ᶠ[nhds τ] g) :
    dbar f τ = dbar g τ := by
  rw [dbar, dbar, h.fderiv_eq]

/-- `∂/∂τ̄` annihilates a holomorphic function. -/
theorem dbar_of_hasDerivAt {f : ℂ → ℂ} {f' : ℂ} {τ : ℂ} (h : HasDerivAt f f' τ) :
    dbar f τ = 0 := by
  rw [dbar_of_hasFDerivAt (h.hasFDerivAt.restrictScalars ℝ)]
  simp only [ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]
  linear_combination (f' / 2) * Complex.I_mul_I

/-- `∂/∂τ̄` of the conjugate of a holomorphic function is the conjugate of its
derivative. -/
theorem dbar_conj_of_hasDerivAt {f : ℂ → ℂ} {f' : ℂ} {τ : ℂ} (h : HasDerivAt f f' τ) :
    dbar (fun t : ℂ => (starRingEnd ℂ) (f t)) τ = (starRingEnd ℂ) f' := by
  have hF : HasFDerivAt (fun t : ℂ => (starRingEnd ℂ) (f t))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ)) τ :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp τ (h.hasFDerivAt.restrictScalars ℝ)
  rw [dbar_of_hasFDerivAt hF]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, Complex.conj_I]
  linear_combination (-((starRingEnd ℂ) f') / 2) * Complex.I_mul_I

theorem dbar_const_mul {f : ℂ → ℂ} {τ : ℂ} (c : ℂ) (hf : DifferentiableAt ℝ f τ) :
    dbar (fun z : ℂ => c * f z) τ = c * dbar f τ := by
  rw [dbar_of_hasFDerivAt (hf.hasFDerivAt.const_mul c), dbar_eq]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

theorem dbar_mul {f g : ℂ → ℂ} {τ : ℂ} (hf : DifferentiableAt ℝ f τ)
    (hg : DifferentiableAt ℝ g τ) :
    dbar (fun z : ℂ => f z * g z) τ = f τ * dbar g τ + g τ * dbar f τ := by
  have hfg : HasFDerivAt (fun z : ℂ => f z * g z)
      (f τ • fderiv ℝ g τ + g τ • fderiv ℝ f τ) τ := hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [dbar_of_hasFDerivAt hfg, dbar_eq, dbar_eq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring

theorem dbar_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {τ : ℂ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (f i) τ) :
    dbar (fun z : ℂ => ∑ i ∈ s, f i z) τ = ∑ i ∈ s, dbar (f i) τ := by
  have hsum : HasFDerivAt (fun z : ℂ => ∑ i ∈ s, f i z) (∑ i ∈ s, fderiv ℝ (f i) τ) τ :=
    HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt
  rw [dbar_of_hasFDerivAt hsum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (dbar_eq (f i) τ).symm

/-- The real Fréchet derivative of `z ↦ √(Im z)`, the only non-holomorphic
factor in `ξ₁`. -/
theorem hasFDerivAt_ofReal_sqrt_im {τ : ℂ} (hτ : 0 < τ.im) :
    HasFDerivAt (fun z : ℂ => ((Real.sqrt z.im : ℝ) : ℂ))
      (paper2ImLin (((1 / (2 * Real.sqrt τ.im) : ℝ) : ℂ)) 0) τ := by
  have hk : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt τ.im)) τ.im :=
    Real.hasDerivAt_sqrt hτ.ne'
  have hg : HasDerivAt (fun _ : ℂ => (1 : ℂ)) 0 τ := hasDerivAt_const τ 1
  simpa using hasFDerivAt_ofReal_im_mul hk hg

/-- `∂/∂τ̄ √Y = i/(4√Y)`: the `∂̄Y = i/2` chain rule. -/
theorem dbar_ofReal_sqrt_im {τ : ℂ} (hτ : 0 < τ.im) :
    dbar (fun z : ℂ => ((Real.sqrt z.im : ℝ) : ℂ)) τ
      = Complex.I / (4 * ((Real.sqrt τ.im : ℝ) : ℂ)) := by
  have hs : ((Real.sqrt τ.im : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hτ).ne'
  rw [dbar_of_hasFDerivAt (hasFDerivAt_ofReal_sqrt_im hτ), dbar_paper2ImLin]
  push_cast
  field_simp
  norm_num

/-! ## The `∂/∂τ̄` of `ξ₁` applied to the lattice correction -/

/-- The four-block shadow value `S(τ) = Σ_j (-1)^j conj(θ_j(τ))·g_j(τ)`. -/
noncomputable def paper2ShadowSum (τ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
    (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) τ) * paper2GComponent (j : ℤ) τ

/-- The differentiated block value `P(τ) = Σ_j (-1)^j conj(θ_j'(τ))·g_j(τ)`. -/
noncomputable def paper2ShadowSumDeriv (τ : ℂ) : ℂ :=
  ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
    (starRingEnd ℂ) (paper2ThetaComponentDeriv (j : ℤ) τ) * paper2GComponent (j : ℤ) τ

theorem differentiableAt_conj_paper2ThetaComponent (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℝ (fun z : ℂ => (starRingEnd ℂ) (paper2ThetaComponent j z)) τ :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp τ
    ((hasDerivAt_paper2ThetaComponent j hτ).hasFDerivAt.restrictScalars ℝ)).differentiableAt

theorem differentiableAt_paper2GComponent (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℝ (fun z : ℂ => paper2GComponent j z) τ :=
  ((hasDerivAt_paper2GComponent j hτ).hasFDerivAt.restrictScalars ℝ).differentiableAt

theorem differentiableAt_paper2ShadowSum {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℝ paper2ShadowSum τ := by
  show DifferentiableAt ℝ (fun z : ℂ => ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
    (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) z) * paper2GComponent (j : ℤ) z) τ
  refine DifferentiableAt.fun_sum fun j _ => ?_
  exact ((differentiableAt_conj_paper2ThetaComponent (j : ℤ) hτ).const_mul _).mul
    (differentiableAt_paper2GComponent (j : ℤ) hτ)

/-- `∂/∂τ̄ S = P`: `g_j` is holomorphic so it is annihilated, and
`conj(θ_j)` is anti-holomorphic with `∂̄ conj(θ_j) = conj(θ_j')`. -/
theorem dbar_paper2ShadowSum {τ : ℂ} (hτ : 0 < τ.im) :
    dbar paper2ShadowSum τ = paper2ShadowSumDeriv τ := by
  show dbar (fun z : ℂ => ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
    (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) z) * paper2GComponent (j : ℤ) z) τ
      = paper2ShadowSumDeriv τ
  rw [dbar_finsetSum (Finset.range 4)
      (fun j : ℕ => fun z : ℂ => (-1 : ℂ) ^ j *
        (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) z) * paper2GComponent (j : ℤ) z)
      (fun j _ => ((differentiableAt_conj_paper2ThetaComponent (j : ℤ) hτ).const_mul _).mul
        (differentiableAt_paper2GComponent (j : ℤ) hτ)),
    paper2ShadowSumDeriv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dbar_mul ((differentiableAt_conj_paper2ThetaComponent (j : ℤ) hτ).const_mul _)
      (differentiableAt_paper2GComponent (j : ℤ) hτ),
    dbar_const_mul _ (differentiableAt_conj_paper2ThetaComponent (j : ℤ) hτ),
    dbar_of_hasDerivAt (hasDerivAt_paper2GComponent (j : ℤ) hτ),
    dbar_conj_of_hasDerivAt (hasDerivAt_paper2ThetaComponent (j : ℤ) hτ)]
  ring

/-- **The `∂/∂τ̄` of `ξ₁` applied to the lattice correction.**  The `√Y`
factor of `ξ₁` is carried, and contributes the first term; the second comes
from the anti-holomorphic `conj(θ_j)` factors.

Statement about an explicit convergent lattice sum; Zwegers' completion
theorem is not formalized and no modular property is claimed. -/
theorem paper2_dbar_xi1_latticeCorrection {τ : ℂ} (hτ : 0 < τ.im) :
    dbar (xi1 paper2LatticeCorrection) τ
      = -(Complex.I / (8 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)))
          * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
              (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) τ) * paper2GComponent (j : ℤ) τ
        - (((Real.sqrt τ.im / (2 * Real.sqrt 10) : ℝ)) : ℂ)
          * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
              (starRingEnd ℂ) (paper2ThetaComponentDeriv (j : ℤ) τ) *
              paper2GComponent (j : ℤ) τ := by
  have h10 : ((Real.sqrt 10 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 10)).ne'
  have hs : ((Real.sqrt τ.im : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hτ).ne'
  have hsplit : ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)
      = ((Real.sqrt 10 : ℝ) : ℂ) * ((Real.sqrt τ.im : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : xi1 paper2LatticeCorrection =ᶠ[nhds τ]
      fun z : ℂ => ((-(1 / (2 * Real.sqrt 10)) : ℝ) : ℂ) * ((Real.sqrt z.im : ℝ) : ℂ) *
        paper2ShadowSum z := by
    filter_upwards [hopen.mem_nhds hτ] with z hz
    rw [paper2_xi1_latticeCorrection hz]
    show _ = _ * _ * paper2ShadowSum z
    rw [paper2ShadowSum]
    push_cast
    ring
  have hscalar : DifferentiableAt ℝ
      (fun z : ℂ => ((-(1 / (2 * Real.sqrt 10)) : ℝ) : ℂ) * ((Real.sqrt z.im : ℝ) : ℂ)) τ :=
    ((hasFDerivAt_ofReal_sqrt_im hτ).differentiableAt).const_mul _
  rw [dbar_congr_of_eventuallyEq hev,
    dbar_mul hscalar (differentiableAt_paper2ShadowSum hτ),
    dbar_paper2ShadowSum hτ,
    dbar_const_mul _ ((hasFDerivAt_ofReal_sqrt_im hτ).differentiableAt),
    dbar_ofReal_sqrt_im hτ, hsplit]
  show _ = _ * paper2ShadowSum τ - _ * paper2ShadowSumDeriv τ
  rw [paper2ShadowSum, paper2ShadowSumDeriv]
  push_cast
  field_simp
  ring

/-! ## The witness point `τ₀ = 2i`

At `τ₀ = 2i` every nome `q^r` is the positive real `e^{-4πr}`, so all four
transverse components, all four longitudinal components and the four
differentiated transverse components collapse to real series (the last up to
the constant factor `πi/4`).  The whole boundary derivative therefore becomes
`i` times a single real number.

As everywhere in this file these are statements about explicit convergent
series; nothing asserts Zwegers' completion theorem or his `S` law. -/

/-- Real transverse summand at `τ₀ = 2i`: `e^{-πT²/2}` on the residue class. -/
noncomputable def paper2ThetaRealTerm (j T : ℤ) : ℝ :=
  if paper2ThetaResidue j T then Real.exp (-(Real.pi * (T : ℝ) ^ 2 / 2)) else 0

/-- Real differentiated transverse summand at `τ₀ = 2i`. -/
noncomputable def paper2ARealTerm (j T : ℤ) : ℝ :=
  if paper2ThetaResidue j T then (T : ℝ) ^ 2 * Real.exp (-(Real.pi * (T : ℝ) ^ 2 / 2)) else 0

/-- Real longitudinal summand at `τ₀ = 2i`: `n e^{-πn²/10}` on the class. -/
noncomputable def paper2GRealTerm (j n : ℤ) : ℝ :=
  if paper2GResidue j n then (n : ℝ) * Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 10)) else 0

/-- The combined kernel summand `(2πT²-1)e^{-πT²/2}` on the class. -/
noncomputable def paper2URealTerm (j T : ℤ) : ℝ :=
  if paper2ThetaResidue j T then
    (2 * Real.pi * (T : ℝ) ^ 2 - 1) * Real.exp (-(Real.pi * (T : ℝ) ^ 2 / 2)) else 0

noncomputable def paper2ThetaRealSum (j : ℤ) : ℝ := ∑' T : ℤ, paper2ThetaRealTerm j T
noncomputable def paper2ARealSum (j : ℤ) : ℝ := ∑' T : ℤ, paper2ARealTerm j T
noncomputable def paper2GRealSum (j : ℤ) : ℝ := ∑' n : ℤ, paper2GRealTerm j n
noncomputable def paper2URealSum (j : ℤ) : ℝ := ∑' T : ℤ, paper2URealTerm j T

theorem summable_paper2ThetaRealTerm (j : ℤ) : Summable (paper2ThetaRealTerm j) := by
  refine (summable_abs_pow_mul_exp_neg_pi_mul_sq
    (show (0 : ℝ) < 1 / 2 by norm_num) 0).of_norm_bounded fun T => ?_
  rw [paper2ThetaRealTerm]
  by_cases h : paper2ThetaResidue j T
  · rw [if_pos h, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, one_mul,
      show -Real.pi * (1 / 2) * (T : ℝ) ^ 2 = -(Real.pi * (T : ℝ) ^ 2 / 2) by ring]
  · rw [if_neg h, norm_zero]
    positivity

theorem summable_paper2ARealTerm (j : ℤ) : Summable (paper2ARealTerm j) := by
  refine (summable_abs_pow_mul_exp_neg_pi_mul_sq
    (show (0 : ℝ) < 1 / 2 by norm_num) 2).of_norm_bounded fun T => ?_
  rw [paper2ARealTerm]
  by_cases h : paper2ThetaResidue j T
  · rw [if_pos h, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), sq_abs,
      show -Real.pi * (1 / 2) * (T : ℝ) ^ 2 = -(Real.pi * (T : ℝ) ^ 2 / 2) by ring,
      abs_of_nonneg (sq_nonneg ((T : ℝ)))]
  · rw [if_neg h, norm_zero]
    positivity

theorem summable_paper2GRealTerm (j : ℤ) : Summable (paper2GRealTerm j) := by
  refine (summable_abs_pow_mul_exp_neg_pi_mul_sq
    (show (0 : ℝ) < 1 / 10 by norm_num) 1).of_norm_bounded fun n => ?_
  rw [paper2GRealTerm]
  by_cases h : paper2GResidue j n
  · rw [if_pos h, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), pow_one,
      show -Real.pi * (1 / 10) * (n : ℝ) ^ 2 = -(Real.pi * (n : ℝ) ^ 2 / 10) by ring]
  · rw [if_neg h, norm_zero]
    positivity

theorem summable_paper2URealTerm (j : ℤ) : Summable (paper2URealTerm j) := by
  have h : ∀ T : ℤ, paper2URealTerm j T
      = 2 * Real.pi * paper2ARealTerm j T - paper2ThetaRealTerm j T := by
    intro T
    rw [paper2URealTerm, paper2ARealTerm, paper2ThetaRealTerm]
    by_cases hT : paper2ThetaResidue j T
    · rw [if_pos hT, if_pos hT, if_pos hT]; ring
    · rw [if_neg hT, if_neg hT, if_neg hT]; ring
  exact (((summable_paper2ARealTerm j).mul_left (2 * Real.pi)).sub
    (summable_paper2ThetaRealTerm j)).congr fun T => (h T).symm

/-- `U_j = 2πA_j - θ_j(2i)`: the combined kernel is the difference of the two
transverse series. -/
theorem paper2URealSum_eq (j : ℤ) :
    paper2URealSum j = 2 * Real.pi * paper2ARealSum j - paper2ThetaRealSum j := by
  rw [paper2URealSum, paper2ARealSum, paper2ThetaRealSum,
    ← (summable_paper2ARealTerm j).tsum_mul_left,
    ← Summable.tsum_sub ((summable_paper2ARealTerm j).mul_left (2 * Real.pi))
      (summable_paper2ThetaRealTerm j)]
  refine tsum_congr fun T => ?_
  rw [paper2URealTerm, paper2ARealTerm, paper2ThetaRealTerm]
  by_cases hT : paper2ThetaResidue j T
  · rw [if_pos hT, if_pos hT, if_pos hT]; ring
  · rw [if_neg hT, if_neg hT, if_neg hT]; ring

/-- Positivity of the combined kernel away from `T = 0`, and its value at
`T = 0`.  This is what makes the witness estimate elementary. -/
theorem paper2_kernel_pos {T : ℤ} (hT : T ≠ 0) :
    0 < 2 * Real.pi * (T : ℝ) ^ 2 - 1 := by
  have h1 : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ T ^ 2 := by
      rcases lt_or_gt_of_ne hT with h | h <;> nlinarith
    exact_mod_cast this
  nlinarith [Real.pi_gt_three]

@[simp] theorem paper2_kernel_zero : 2 * Real.pi * ((0 : ℤ) : ℝ) ^ 2 - 1 = -1 := by
  norm_num

/-! ### Collapse of the components at `τ₀ = 2i` -/

theorem paper2ThetaTerm_two_I (j T : ℤ) :
    paper2ThetaTerm j T (2 * Complex.I) = ((paper2ThetaRealTerm j T : ℝ) : ℂ) := by
  rw [paper2ThetaRealTerm]
  by_cases h : paper2ThetaResidue j T
  · rw [paper2ThetaTerm, if_pos h, if_pos h, jacobiTheta₂_term_eq_transNome,
      Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination ((Real.pi : ℂ) * (T : ℂ) ^ 2 / 2) * Complex.I_sq
  · rw [paper2ThetaTerm, if_neg h, if_neg h, Complex.ofReal_zero]

theorem paper2GTerm_two_I (j n : ℤ) :
    paper2GTerm j n (2 * Complex.I) = ((paper2GRealTerm j n : ℝ) : ℂ) := by
  rw [paper2GRealTerm]
  by_cases h : paper2GResidue j n
  · rw [paper2GTerm, if_pos h, if_pos h, jacobiTheta₂_term_eq_longPositiveNome,
      Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_intCast]
    congr 2
    push_cast
    linear_combination ((Real.pi : ℂ) * (n : ℂ) ^ 2 / 10) * Complex.I_sq
  · rw [paper2GTerm, if_neg h, if_neg h, Complex.ofReal_zero]

theorem paper2ThetaTermDeriv_two_I (j T : ℤ) :
    paper2ThetaTermDeriv j T (2 * Complex.I)
      = (Real.pi * Complex.I / 4) * ((paper2ARealTerm j T : ℝ) : ℂ) := by
  rw [paper2ARealTerm]
  by_cases h : paper2ThetaResidue j T
  · rw [paper2ThetaTermDeriv, if_pos h, if_pos h, Complex.ofReal_mul, Complex.ofReal_exp,
      show ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (2 * Complex.I) * ((T : ℂ) ^ 2 / 8))
        = ((-(Real.pi * (T : ℝ) ^ 2 / 2) : ℝ) : ℂ) by
        push_cast; linear_combination ((Real.pi : ℂ) * (T : ℂ) ^ 2 / 2) * Complex.I_sq]
    push_cast
    ring
  · rw [paper2ThetaTermDeriv, if_neg h, if_neg h, Complex.ofReal_zero, mul_zero]

theorem paper2ThetaComponent_two_I (j : ℤ) :
    paper2ThetaComponent j (2 * Complex.I) = ((paper2ThetaRealSum j : ℝ) : ℂ) := by
  have h := ContinuousLinearMap.map_tsum Complex.ofRealCLM (summable_paper2ThetaRealTerm j)
  simp only [Complex.ofRealCLM_apply] at h
  rw [paper2ThetaComponent, paper2ThetaRealSum, h]
  exact tsum_congr fun T => paper2ThetaTerm_two_I j T

theorem paper2GComponent_two_I (j : ℤ) :
    paper2GComponent j (2 * Complex.I) = ((paper2GRealSum j : ℝ) : ℂ) := by
  have h := ContinuousLinearMap.map_tsum Complex.ofRealCLM (summable_paper2GRealTerm j)
  simp only [Complex.ofRealCLM_apply] at h
  rw [paper2GComponent, paper2GRealSum, h]
  exact tsum_congr fun n => paper2GTerm_two_I j n

theorem paper2ThetaComponentDeriv_two_I (j : ℤ) :
    paper2ThetaComponentDeriv j (2 * Complex.I)
      = (Real.pi * Complex.I / 4) * ((paper2ARealSum j : ℝ) : ℂ) := by
  have hAc : Summable (fun T : ℤ => ((paper2ARealTerm j T : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.summable (summable_paper2ARealTerm j))
  calc paper2ThetaComponentDeriv j (2 * Complex.I)
      = ∑' T : ℤ, (Real.pi * Complex.I / 4) * ((paper2ARealTerm j T : ℝ) : ℂ) :=
        tsum_congr fun T => paper2ThetaTermDeriv_two_I j T
    _ = (Real.pi * Complex.I / 4) * ∑' T : ℤ, ((paper2ARealTerm j T : ℝ) : ℂ) :=
        hAc.tsum_mul_left _
    _ = (Real.pi * Complex.I / 4) * ((paper2ARealSum j : ℝ) : ℂ) := by
        have h := ContinuousLinearMap.map_tsum Complex.ofRealCLM (summable_paper2ARealTerm j)
        simp only [Complex.ofRealCLM_apply] at h
        rw [paper2ARealSum, h]

/-! ### The single real number the derivative collapses to -/

noncomputable def paper2WitnessS : ℝ :=
  ∑ j ∈ Finset.range 4, (-1 : ℝ) ^ j * paper2ThetaRealSum (j : ℤ) * paper2GRealSum (j : ℤ)

noncomputable def paper2WitnessP : ℝ :=
  ∑ j ∈ Finset.range 4, (-1 : ℝ) ^ j * paper2ARealSum (j : ℤ) * paper2GRealSum (j : ℤ)

/-- The real number `W` with `∂̄(ξ₁·)(2i) = i·W`. -/
noncomputable def paper2WitnessW : ℝ :=
  (2 * Real.pi * paper2WitnessP - paper2WitnessS) / (16 * Real.sqrt 5)

/-- `2πP - S` as a single `(-1)^j`-weighted sum of kernel blocks. -/
theorem paper2Witness_two_pi_P_sub_S :
    2 * Real.pi * paper2WitnessP - paper2WitnessS
      = ∑ j ∈ Finset.range 4,
          (-1 : ℝ) ^ j * paper2URealSum (j : ℤ) * paper2GRealSum (j : ℤ) := by
  rw [paper2WitnessP, paper2WitnessS, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [paper2URealSum_eq]
  ring

/-- **The witness reduction.**  At `τ₀ = 2i` the whole boundary derivative of
`ξ₁` collapses to `i` times one real number.  Statement about an explicit
convergent lattice sum. -/
theorem paper2_dbar_xi1_two_I :
    dbar (xi1 paper2LatticeCorrection) (2 * Complex.I)
      = Complex.I * ((paper2WitnessW : ℝ) : ℂ) := by
  have him : (2 * Complex.I).im = 2 := by simp
  have hτ : (0 : ℝ) < (2 * Complex.I).im := by rw [him]; norm_num
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h5c : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h5.ne'
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h10 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq20 : Real.sqrt (10 * (2 : ℝ)) = 2 * Real.sqrt 5 := by
    rw [show (10 : ℝ) * 2 = 2 ^ 2 * 5 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hsq2 : Real.sqrt 2 / (2 * Real.sqrt 10) = 1 / (2 * Real.sqrt 5) := by
    rw [h10]
    field_simp
  have hS : (∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
        (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) (2 * Complex.I)) *
        paper2GComponent (j : ℤ) (2 * Complex.I))
      = ((paper2WitnessS : ℝ) : ℂ) := by
    rw [paper2WitnessS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [paper2ThetaComponent_two_I, paper2GComponent_two_I, Complex.conj_ofReal]
    push_cast
    ring
  have hP : (∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
        (starRingEnd ℂ) (paper2ThetaComponentDeriv (j : ℤ) (2 * Complex.I)) *
        paper2GComponent (j : ℤ) (2 * Complex.I))
      = -((Real.pi : ℂ) * Complex.I / 4) * ((paper2WitnessP : ℝ) : ℂ) := by
    rw [paper2WitnessP, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [paper2ThetaComponentDeriv_two_I, paper2GComponent_two_I]
    simp only [map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [paper2_dbar_xi1_latticeCorrection hτ, hS, hP, him, hsq20, hsq2, paper2WitnessW]
  push_cast
  field_simp
  ring

/-! ### `Δ₁` at the witness point, and the reduction to one real inequality -/

/-- At `τ₀ = 2i` the weight-one Laplacian of the lattice correction is the
real number `-4W`.  Together with `paper2_dbar_xi1_two_I` this reduces the
whole non-harmonicity question to `W ≠ 0`, i.e. to a single real inequality.

Statement about an explicit convergent lattice sum; it is not a statement
about `q^{1/10}B(q)` or about any completion of it. -/
theorem paper2_delta1_two_I :
    Delta1 paper2LatticeCorrection (2 * Complex.I)
      = ((-(4 * paper2WitnessW) : ℝ) : ℂ) := by
  have him : (2 * Complex.I).im = 2 := by simp
  rw [Delta1, xi1, paper2_dbar_xi1_two_I, him]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  linear_combination (4 * ((paper2WitnessW : ℝ) : ℂ)) * Complex.I_mul_I

/-- Away from the class of `T ≡ 0 (mod 4)` the combined kernel is
nonnegative termwise: `2πT² - 1 > 0` for `T ≠ 0`. -/
theorem paper2URealTerm_nonneg {j : ℤ} (hj : j % 4 ≠ 2) (T : ℤ) :
    0 ≤ paper2URealTerm j T := by
  rw [paper2URealTerm]
  by_cases h : paper2ThetaResidue j T
  · rw [if_pos h]
    have hT : T ≠ 0 := by
      intro h0
      subst h0
      simp only [paper2ThetaResidue] at h
      omega
    exact le_of_lt (mul_pos (paper2_kernel_pos hT) (Real.exp_pos _))
  · rw [if_neg h]

/-- Hence `U_j > 0` for the three residue classes that avoid `T = 0`. -/
theorem paper2URealSum_pos {j : ℤ} (hj : j % 4 ≠ 2) : 0 < paper2URealSum j := by
  have hres : paper2ThetaResidue j ((3 * j + 2) % 4) := by
    simp only [paper2ThetaResidue]
    omega
  have hne : ((3 * j + 2) % 4 : ℤ) ≠ 0 := by omega
  refine (summable_paper2URealTerm j).tsum_pos (paper2URealTerm_nonneg hj)
    ((3 * j + 2) % 4) ?_
  rw [paper2URealTerm, if_pos hres]
  exact mul_pos (paper2_kernel_pos hne) (Real.exp_pos _)

theorem paper2WitnessW_ne_zero_iff :
    paper2WitnessW ≠ 0 ↔ 2 * Real.pi * paper2WitnessP - paper2WitnessS ≠ 0 := by
  have h5 : (16 : ℝ) * Real.sqrt 5 ≠ 0 := by positivity
  rw [paper2WitnessW, div_ne_zero_iff]
  simp [h5]

/-- The `∂̄(ξ₁·)` non-vanishing at `τ₀ = 2i` is *equivalent* to the single
real inequality `2πP - S ≠ 0`. -/
theorem paper2_dbar_xi1_two_I_ne_zero_iff :
    dbar (xi1 paper2LatticeCorrection) (2 * Complex.I) ≠ 0
      ↔ 2 * Real.pi * paper2WitnessP - paper2WitnessS ≠ 0 := by
  rw [paper2_dbar_xi1_two_I, ← paper2WitnessW_ne_zero_iff]
  constructor
  · intro h hW
    exact h (by rw [hW, Complex.ofReal_zero, mul_zero])
  · intro h hc
    exact h (by
      rcases mul_eq_zero.1 hc with hI | hW
      · exact absurd hI Complex.I_ne_zero
      · exact Complex.ofReal_eq_zero.1 hW)

/-- Likewise for `Δ₁`: the weight-one harmonicity of this explicit function
fails at `τ₀ = 2i` exactly when `2πP - S ≠ 0`. -/
theorem paper2_delta1_two_I_ne_zero_iff :
    Delta1 paper2LatticeCorrection (2 * Complex.I) ≠ 0
      ↔ 2 * Real.pi * paper2WitnessP - paper2WitnessS ≠ 0 := by
  rw [paper2_delta1_two_I, ← paper2WitnessW_ne_zero_iff, ne_eq, ne_eq,
    Complex.ofReal_eq_zero]
  constructor
  · intro h hW
    exact h (by rw [hW, mul_zero, neg_zero])
  · intro h hc
    exact h (by linarith [hc])

/-! ## A geometric tail bound, and the elementary numeric facts

Everything below is elementary: a ratio-test tail bound for
`Σ m^k e^{-πcm²}`, the two-sided bounds `3 < π ≤ 4`, and the lower bound
`13 ≤ e³` from four terms of the exponential series.  No numeric evaluation of
`exp` is used anywhere.

As everywhere in this file these are statements about explicit convergent
series; nothing asserts Zwegers' completion theorem or his `S` law. -/

theorem paper2_exp_neg_le {x a : ℝ} (ha : 0 < a) (h : a ≤ Real.exp x) :
    Real.exp (-x) ≤ 1 / a := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le ha h

/-- `13 ≤ e³`, from `1 + 3 + 3²/2! + 3³/3!`. -/
theorem paper2_exp_three : (13 : ℝ) ≤ Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem paper2_exp_pi : (13 : ℝ) ≤ Real.exp Real.pi :=
  paper2_exp_three.trans (Real.exp_le_exp.2 Real.pi_gt_three.le)

/-- `29/8 ≤ e^{π/2}`, from `1 + x + x²/2` at `x = 3/2`. -/
theorem paper2_exp_pi_half : (29 / 8 : ℝ) ≤ Real.exp (Real.pi / 2) := by
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have h2 : Real.exp (3 / 2) ≤ Real.exp (Real.pi / 2) :=
    Real.exp_le_exp.2 (by linarith [Real.pi_gt_three])
  norm_num at h
  linarith

theorem paper2_one_add_le_two_pow (m : ℕ) : (1 : ℝ) + m ≤ (2 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ n ih =>
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      push_cast
      push_cast at ih
      linarith

/-- **Geometric tail bound.**  If the ratio `2^k e^{-2πcN}` is at most `½`
then the tail from `N` on is at most twice its first term.  The proof is the
ratio test: `(N+i)^k ≤ N^k(2^k)^i` and `e^{-πc(N+i)²} ≤ e^{-πcN²}e^{-2πcNi}`. -/
theorem paper2_geometric_tail {c : ℝ} (hc : 0 < c) (k N : ℕ) (hN : 1 ≤ N)
    (hr : (2 : ℝ) ^ k * Real.exp (-Real.pi * c * (2 * (N : ℝ))) ≤ 1 / 2) :
    ∑' i : ℕ, ((N : ℝ) + i) ^ k * Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2)
      ≤ 2 * ((N : ℝ) ^ k * Real.exp (-Real.pi * c * (N : ℝ) ^ 2)) := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpc : 0 < Real.pi * c := by positivity
  set r : ℝ := (2 : ℝ) ^ k * Real.exp (-Real.pi * c * (2 * (N : ℝ))) with hrdef
  set A : ℝ := (N : ℝ) ^ k * Real.exp (-Real.pi * c * (N : ℝ) ^ 2) with hAdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r < 1 := lt_of_le_of_lt hr (by norm_num)
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hpt : ∀ i : ℕ, ((N : ℝ) + i) ^ k * Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2)
      ≤ A * r ^ i := by
    intro i
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hb : ((N : ℝ) + i) ≤ (N : ℝ) * (1 + i) := by nlinarith
    have hpow : ((N : ℝ) + i) ^ k ≤ (N : ℝ) ^ k * ((2 : ℝ) ^ k) ^ i := by
      calc ((N : ℝ) + i) ^ k ≤ ((N : ℝ) * (1 + i)) ^ k := by gcongr
        _ = (N : ℝ) ^ k * (1 + (i : ℝ)) ^ k := by rw [mul_pow]
        _ ≤ (N : ℝ) ^ k * ((2 : ℝ) ^ i) ^ k := by
            gcongr
            exact paper2_one_add_le_two_pow i
        _ = (N : ℝ) ^ k * ((2 : ℝ) ^ k) ^ i := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hexp : Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2)
        ≤ Real.exp (-Real.pi * c * (N : ℝ) ^ 2) *
          (Real.exp (-Real.pi * c * (2 * (N : ℝ)))) ^ i := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [sq_nonneg (i : ℝ)]
    calc ((N : ℝ) + i) ^ k * Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2)
        ≤ ((N : ℝ) ^ k * ((2 : ℝ) ^ k) ^ i) *
            (Real.exp (-Real.pi * c * (N : ℝ) ^ 2) *
              (Real.exp (-Real.pi * c * (2 * (N : ℝ)))) ^ i) :=
          mul_le_mul hpow hexp (by positivity) (by positivity)
      _ = A * r ^ i := by rw [hAdef, hrdef, mul_pow]; ring
  have hgeo : Summable (fun i : ℕ => A * r ^ i) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left A
  have hsum : Summable (fun i : ℕ => ((N : ℝ) + i) ^ k *
      Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2)) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hpt hgeo
  calc ∑' i : ℕ, ((N : ℝ) + i) ^ k * Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2)
      ≤ ∑' i : ℕ, A * r ^ i := hsum.tsum_le_tsum hpt hgeo
    _ = A * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ 2 * A := by
        have h1 : (1 : ℝ) / 2 ≤ 1 - r := by linarith
        have h2 : (1 - r)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
        nlinarith

/-- The `ℤ`-indexed majorant supported on `|m| ≥ N`. -/
noncomputable def paper2TailMaj (B c : ℝ) (k N : ℕ) (m : ℤ) : ℝ :=
  if (N : ℤ) ≤ |m| then B * |(m : ℝ)| ^ k * Real.exp (-Real.pi * c * (m : ℝ) ^ 2) else 0

theorem paper2TailMaj_nonneg {B c : ℝ} (hB : 0 ≤ B) (k N : ℕ) (m : ℤ) :
    0 ≤ paper2TailMaj B c k N m := by
  rw [paper2TailMaj]
  split
  · positivity
  · exact le_rfl

theorem summable_paper2TailMaj {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (k N : ℕ) :
    Summable (paper2TailMaj B c k N) := by
  refine Summable.of_nonneg_of_le (paper2TailMaj_nonneg hB k N) (fun m => ?_)
    ((summable_abs_pow_mul_exp_neg_pi_mul_sq hc k).mul_left B)
  rw [paper2TailMaj]
  split
  · exact le_of_eq (by ring)
  · positivity

/-- The full `ℤ`-sum of the majorant: two copies of the `ℕ`-tail, each at most
twice its first term. -/
theorem paper2TailMaj_tsum_le {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (k N : ℕ) (hN : 1 ≤ N)
    (hr : (2 : ℝ) ^ k * Real.exp (-Real.pi * c * (2 * (N : ℝ))) ≤ 1 / 2) :
    ∑' m : ℤ, paper2TailMaj B c k N m
      ≤ 4 * (B * ((N : ℝ) ^ k * Real.exp (-Real.pi * c * (N : ℝ) ^ 2))) := by
  have hsum := summable_paper2TailMaj hB hc k N
  have hnat : Summable (fun n : ℕ => paper2TailMaj B c k N (n : ℤ)) := by
    simpa only [Function.comp_def] using hsum.comp_injective Nat.cast_injective
  have heven : ∀ n : ℕ, paper2TailMaj B c k N (-(n : ℤ)) = paper2TailMaj B c k N (n : ℤ) := by
    intro n
    simp [paper2TailMaj]
  have hnat' : Summable (fun n : ℕ => paper2TailMaj B c k N (-(n : ℤ))) :=
    hnat.congr fun n => (heven n).symm
  have hz0 : ¬((N : ℤ) ≤ |(0 : ℤ)|) := by
    simp only [abs_zero]
    omega
  have hz : paper2TailMaj B c k N 0 = 0 := by rw [paper2TailMaj, if_neg hz0]
  have hsplit : ∑' m : ℤ, paper2TailMaj B c k N m
      = 2 * ∑' n : ℕ, paper2TailMaj B c k N (n : ℤ) := by
    rw [Summable.tsum_of_nat_of_neg hnat hnat', hz, tsum_congr heven]
    ring
  have hre : ∑' n : ℕ, paper2TailMaj B c k N (n : ℤ)
      = B * ∑' i : ℕ, ((N : ℝ) + i) ^ k * Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2) := by
    have hinj : Function.Injective (fun i : ℕ => N + i) := by
      intro a b h
      have h' : N + a = N + b := h
      omega
    have hsupp : Function.support (fun n : ℕ => paper2TailMaj B c k N (n : ℤ))
        ⊆ Set.range (fun i : ℕ => N + i) := by
      intro n hn
      have hNn : N ≤ n := by
        by_contra hlt
        refine hn ?_
        show paper2TailMaj B c k N (n : ℤ) = 0
        have hnl : ¬((N : ℤ) ≤ |(n : ℤ)|) := by
          rw [abs_of_nonneg (Int.natCast_nonneg n)]
          omega
        rw [paper2TailMaj, if_neg hnl]
      exact ⟨n - N, by show N + (n - N) = n; omega⟩
    rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    have hcast : ((((N + i : ℕ) : ℤ)) : ℝ) = (N : ℝ) + i := by push_cast; ring
    have hle : (N : ℤ) ≤ |((N + i : ℕ) : ℤ)| := by
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      omega
    have habs : |(((N + i : ℕ) : ℤ) : ℝ)| = (N : ℝ) + i := by
      rw [hcast, abs_of_nonneg (by positivity)]
    show paper2TailMaj B c k N ((N + i : ℕ) : ℤ)
        = B * (((N : ℝ) + i) ^ k * Real.exp (-Real.pi * c * ((N : ℝ) + i) ^ 2))
    rw [paper2TailMaj, if_pos hle, habs, hcast]
    ring
  rw [hsplit, hre]
  have hT := paper2_geometric_tail hc k N hN hr
  have := mul_le_mul_of_nonneg_left hT hB
  linarith

/-- **Tail bound over `ℤ`.**  Any family dominated by the majorant has
`|∑' m, F m| ≤ 4·B·N^k·e^{-πcN²}`. -/
theorem paper2_int_tail_bound {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (k N : ℕ) (hN : 1 ≤ N)
    (hr : (2 : ℝ) ^ k * Real.exp (-Real.pi * c * (2 * (N : ℝ))) ≤ 1 / 2)
    {F : ℤ → ℝ} (hmaj : ∀ m : ℤ, |F m| ≤ paper2TailMaj B c k N m) :
    |∑' m : ℤ, F m| ≤ 4 * (B * ((N : ℝ) ^ k * Real.exp (-Real.pi * c * (N : ℝ) ^ 2))) := by
  have hmajsum := summable_paper2TailMaj hB hc k N
  have habs : Summable (fun m : ℤ => |F m|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hmaj hmajsum
  have hnorm : Summable (fun m : ℤ => ‖F m‖) := by
    simpa only [Real.norm_eq_abs] using habs
  calc |∑' m : ℤ, F m| = ‖∑' m : ℤ, F m‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' m : ℤ, ‖F m‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' m : ℤ, |F m| := by simp only [Real.norm_eq_abs]
    _ ≤ ∑' m : ℤ, paper2TailMaj B c k N m := habs.tsum_le_tsum hmaj hmajsum
    _ ≤ 4 * (B * ((N : ℝ) ^ k * Real.exp (-Real.pi * c * (N : ℝ) ^ 2))) :=
        paper2TailMaj_tsum_le hB hc k N hN hr

/-! ### The seven estimates at the witness point -/

theorem paper2_exp_half_eq (T : ℤ) :
    Real.exp (-(Real.pi * (T : ℝ) ^ 2 / 2)) = Real.exp (-Real.pi * (1 / 2) * (T : ℝ) ^ 2) := by
  congr 1
  ring

theorem paper2_exp_tenth_eq (n : ℤ) :
    Real.exp (-(Real.pi * (n : ℝ) ^ 2 / 10)) = Real.exp (-Real.pi * (1 / 10) * (n : ℝ) ^ 2) := by
  congr 1
  ring

theorem paper2_exp_ge_four {x : ℝ} (hx : 12 / 5 ≤ x) : (4 : ℝ) ≤ Real.exp x := by
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 12 / 5)
  have h2 : Real.exp (12 / 5) ≤ Real.exp x := Real.exp_le_exp.2 hx
  norm_num at h
  linarith

theorem paper2_exp_ge_thirteen {x : ℝ} (hx : 3 ≤ x) : (13 : ℝ) ≤ Real.exp x :=
  paper2_exp_three.trans (Real.exp_le_exp.2 hx)

/-- Longitudinal bound: on a class whose smallest element has `|n| ≥ N`,
`|g_j(2i)| ≤ 4N e^{-πN²/10}`. -/
theorem paper2_abs_GRealSum_le (j : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hres : ∀ n : ℤ, paper2GResidue j n → (N : ℤ) ≤ |n|)
    (hr : (2 : ℝ) ^ 1 * Real.exp (-Real.pi * (1 / 10) * (2 * (N : ℝ))) ≤ 1 / 2) :
    |paper2GRealSum j|
      ≤ 4 * (1 * ((N : ℝ) ^ 1 * Real.exp (-Real.pi * (1 / 10) * (N : ℝ) ^ 2))) := by
  refine paper2_int_tail_bound (B := 1) (c := 1 / 10) (by norm_num) (by norm_num) 1 N hN hr
    (fun n => ?_)
  rw [paper2GRealTerm, paper2TailMaj]
  by_cases h : paper2GResidue j n
  · rw [if_pos h, if_pos (hres n h), abs_mul, abs_of_pos (Real.exp_pos _), pow_one, one_mul,
      paper2_exp_tenth_eq]
  · rw [if_neg h, abs_zero]
    split
    · positivity
    · exact le_rfl

/-- Transverse bound away from `T = 0`: the kernel weight is at most
`(2π+1)T²`. -/
theorem paper2_abs_URealTerm_le {j : ℤ} {T : ℤ} (hT : (1 : ℤ) ≤ |T|) :
    |paper2URealTerm j T| ≤ (2 * Real.pi + 1) * |(T : ℝ)| ^ 2 *
      Real.exp (-Real.pi * (1 / 2) * (T : ℝ) ^ 2) := by
  have hT1 : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ T ^ 2 := by
      rcases abs_cases T with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith
    exact_mod_cast h1
  rw [paper2URealTerm]
  by_cases h : paper2ThetaResidue j T
  · rw [if_pos h, abs_mul, abs_of_pos (Real.exp_pos _), paper2_exp_half_eq, sq_abs]
    have hker : |2 * Real.pi * (T : ℝ) ^ 2 - 1| ≤ (2 * Real.pi + 1) * (T : ℝ) ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [Real.pi_gt_three]
    exact mul_le_mul_of_nonneg_right hker (Real.exp_pos _).le
  · rw [if_neg h, abs_zero]
    positivity

/-- `13^n ≤ e^x` whenever `3n ≤ x`, from `13 ≤ e³`. -/
theorem paper2_exp_pow_ge (n : ℕ) {x : ℝ} (hx : 3 * (n : ℝ) ≤ x) : (13 : ℝ) ^ n ≤ Real.exp x := by
  have h1 : (13 : ℝ) ^ n ≤ Real.exp 3 ^ n := by
    gcongr
    exact paper2_exp_three
  have h2 : Real.exp 3 ^ n = Real.exp ((n : ℝ) * 3) := (Real.exp_nat_mul 3 n).symm
  have h3 : Real.exp ((n : ℝ) * 3) ≤ Real.exp x := Real.exp_le_exp.2 (by linarith)
  linarith [h1, h2 ▸ h3]

/-- `|U_0| ≤ 1`: the class `T ≡ 2 (4)` starts at `|T| = 2`, and
`16(2π+1)e^{-2π} ≤ 144/169 < 1`. -/
theorem paper2_abs_URealSum_zero_le : |paper2URealSum 0| ≤ 1 := by
  have hpi4 := Real.pi_le_four
  have hpi3 := Real.pi_gt_three
  have h169 : (169 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have h := paper2_exp_pow_ge 2 (x := 2 * Real.pi) (by push_cast; linarith)
    norm_num at h
    linarith
  have hle : Real.exp (-(2 * Real.pi)) ≤ 1 / 169 := paper2_exp_neg_le (by norm_num) h169
  have hrw : -Real.pi * (1 / 2) * (2 * ((2 : ℕ) : ℝ)) = -(2 * Real.pi) := by push_cast; ring
  have hrw2 : -Real.pi * (1 / 2) * ((2 : ℕ) : ℝ) ^ 2 = -(2 * Real.pi) := by push_cast; ring
  have hr : (2 : ℝ) ^ 2 * Real.exp (-Real.pi * (1 / 2) * (2 * ((2 : ℕ) : ℝ))) ≤ 1 / 2 := by
    rw [hrw]
    linarith
  have hmaj : ∀ T : ℤ, |paper2URealTerm 0 T| ≤ paper2TailMaj (2 * Real.pi + 1) (1 / 2) 2 2 T := by
    intro T
    by_cases h : paper2ThetaResidue 0 T
    · have hT : (2 : ℤ) ≤ |T| := by
        simp only [paper2ThetaResidue] at h
        rcases abs_cases T with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      rw [paper2TailMaj, if_pos (by exact_mod_cast hT)]
      exact paper2_abs_URealTerm_le (le_trans (by norm_num) hT)
    · rw [paper2URealTerm, if_neg h, abs_zero, paper2TailMaj]
      split
      · positivity
      · exact le_rfl
  have hbound := paper2_int_tail_bound (B := 2 * Real.pi + 1) (c := 1 / 2)
    (by linarith) (by norm_num) 2 2 (by norm_num) hr hmaj
  rw [hrw2] at hbound
  push_cast at hbound
  rw [paper2URealSum]
  nlinarith [Real.exp_pos (-(2 * Real.pi))]

/-- A uniform crude bound `|U_j| ≤ 11`, enough for the two negligible
blocks. -/
theorem paper2_abs_URealSum_le (j : ℤ) : |paper2URealSum j| ≤ 11 := by
  have hpi4 := Real.pi_le_four
  have hpi3 := Real.pi_gt_three
  have hle2 : Real.exp (-(Real.pi / 2)) ≤ 8 / 29 := by
    have h := paper2_exp_neg_le (by norm_num : (0 : ℝ) < 29 / 8) paper2_exp_pi_half
    norm_num at h
    exact h
  have hle1 : Real.exp (-Real.pi) ≤ 1 / 13 := paper2_exp_neg_le (by norm_num) paper2_exp_pi
  have hrw : -Real.pi * (1 / 2) * (2 * ((1 : ℕ) : ℝ)) = -Real.pi := by push_cast; ring
  have hrw2 : -Real.pi * (1 / 2) * ((1 : ℕ) : ℝ) ^ 2 = -(Real.pi / 2) := by push_cast; ring
  have hr : (2 : ℝ) ^ 2 * Real.exp (-Real.pi * (1 / 2) * (2 * ((1 : ℕ) : ℝ))) ≤ 1 / 2 := by
    rw [hrw]
    linarith
  have hmaj : ∀ T : ℤ, |(if T = 0 then 0 else paper2URealTerm j T)|
      ≤ paper2TailMaj (2 * Real.pi + 1) (1 / 2) 2 1 T := by
    intro T
    by_cases hT0 : T = 0
    · rw [if_pos hT0, abs_zero, paper2TailMaj]
      split
      · positivity
      · exact le_rfl
    · have hT : (1 : ℤ) ≤ |T| := by
        rcases abs_cases T with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      rw [if_neg hT0, paper2TailMaj, if_pos (by exact_mod_cast hT)]
      exact paper2_abs_URealTerm_le hT
  have hbound := paper2_int_tail_bound (B := 2 * Real.pi + 1) (c := 1 / 2)
    (by linarith) (by norm_num) 2 1 (by norm_num) hr hmaj
  rw [hrw2] at hbound
  push_cast at hbound
  have hzero : |paper2URealTerm j 0| ≤ 1 := by
    rw [paper2URealTerm]
    split
    · norm_num
    · norm_num
  have hpeel := (summable_paper2URealTerm j).tsum_eq_add_tsum_ite (0 : ℤ)
  rw [paper2URealSum, hpeel]
  rw [abs_le]
  have h0 := abs_le.1 hzero
  have h1 := abs_le.1 hbound
  constructor <;> nlinarith [Real.exp_pos (-(Real.pi / 2))]

/-- `U_3 ≥ (2π-1)e^{-π/2}`: keep only the `T = -1` term of a nonnegative
series.  No tail bound is needed. -/
theorem paper2_URealSum_three_ge :
    (2 * Real.pi - 1) * Real.exp (-(Real.pi / 2)) ≤ paper2URealSum 3 := by
  have hres : paper2ThetaResidue 3 (-1) := by decide
  have hval : paper2URealTerm 3 (-1) = (2 * Real.pi - 1) * Real.exp (-(Real.pi / 2)) := by
    rw [paper2URealTerm, if_pos hres]
    norm_num
  rw [paper2URealSum, ← hval]
  exact (summable_paper2URealTerm 3).le_tsum (-1)
    (fun i _ => paper2URealTerm_nonneg (by decide) i)

/-- `-g_3(2i) ≥ (99/100)e^{-π/10}`: peel `n = -1` and bound the rest, which
lives on `|n| ≥ 19`, by `76e^{-361π/10}`. -/
theorem paper2_GRealSum_three_le :
    paper2GRealSum 3 ≤ -(99 / 100) * Real.exp (-(Real.pi / 10)) := by
  have hpi3 := Real.pi_gt_three
  have hres : paper2GResidue 3 (-1) := by decide
  have hval : paper2GRealTerm 3 (-1) = -Real.exp (-(Real.pi / 10)) := by
    rw [paper2GRealTerm, if_pos hres]
    norm_num
  have hrw : -Real.pi * (1 / 10) * (2 * ((19 : ℕ) : ℝ)) = -(19 * Real.pi / 5) := by
    push_cast; ring
  have hrw2 : -Real.pi * (1 / 10) * ((19 : ℕ) : ℝ) ^ 2 = -(361 * Real.pi / 10) := by
    push_cast; ring
  have hr : (2 : ℝ) ^ 1 * Real.exp (-Real.pi * (1 / 10) * (2 * ((19 : ℕ) : ℝ))) ≤ 1 / 2 := by
    rw [hrw]
    have h4 : (4 : ℝ) ≤ Real.exp (19 * Real.pi / 5) := paper2_exp_ge_four (by linarith)
    have := paper2_exp_neg_le (by norm_num : (0 : ℝ) < 4) h4
    norm_num
    linarith
  have hmaj : ∀ n : ℤ, |(if n = -1 then 0 else paper2GRealTerm 3 n)|
      ≤ paper2TailMaj 1 (1 / 10) 1 19 n := by
    intro n
    by_cases hn1 : n = -1
    · rw [if_pos hn1, abs_zero, paper2TailMaj]
      split
      · positivity
      · exact le_rfl
    · rw [if_neg hn1]
      by_cases h : paper2GResidue 3 n
      · have hn : (19 : ℤ) ≤ |n| := by
          simp only [paper2GResidue] at h
          rcases abs_cases n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        rw [paper2GRealTerm, if_pos h, paper2TailMaj, if_pos (by exact_mod_cast hn),
          abs_mul, abs_of_pos (Real.exp_pos _), pow_one, one_mul, paper2_exp_tenth_eq]
      · rw [paper2GRealTerm, if_neg h, abs_zero, paper2TailMaj]
        split
        · positivity
        · exact le_rfl
  have hbound := paper2_int_tail_bound (B := 1) (c := 1 / 10)
    (by norm_num) (by norm_num) 1 19 (by norm_num) hr hmaj
  rw [hrw2] at hbound
  push_cast at hbound
  have hfac : Real.exp (-(361 * Real.pi / 10))
      = Real.exp (-(Real.pi / 10)) * Real.exp (-(36 * Real.pi)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbig : (28561 : ℝ) ≤ Real.exp (36 * Real.pi) := by
    have h := paper2_exp_pow_ge 4 (x := 36 * Real.pi) (by push_cast; linarith)
    norm_num at h
    linarith
  have hsmall : Real.exp (-(36 * Real.pi)) ≤ 1 / 28561 :=
    paper2_exp_neg_le (by norm_num) hbig
  have hpeel := (summable_paper2GRealTerm 3).tsum_eq_add_tsum_ite (-1 : ℤ)
  rw [paper2GRealSum, hpeel, hval]
  rw [hfac] at hbound
  have hR := abs_le.1 hbound
  nlinarith [Real.exp_pos (-(Real.pi / 10)), Real.exp_pos (-(36 * Real.pi))]

/-! ### The final inequality and the two headline corollaries -/

/-- **The witness inequality.**  `2πP - S > 0` at `τ₀ = 2i`.  The `j = 3`
block alone contributes at least `(99/100)(2π-1)e^{-3π/5}`, and the other
three blocks are bounded crudely by `16e^{-8π/5} + 396e^{-81π/10} +
264e^{-18π/5}`; after dividing by `e^{-3π/5}` the comparison needs only
`3 < π ≤ 4` and `13 ≤ e³`. -/
theorem paper2_two_pi_P_sub_S_pos :
    0 < 2 * Real.pi * paper2WitnessP - paper2WitnessS := by
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  -- the three negligible longitudinal blocks
  have hG0 : |paper2GRealSum 0| ≤ 16 * Real.exp (-(8 * Real.pi / 5)) := by
    have h := paper2_abs_GRealSum_le 0 4 (by norm_num)
      (fun n hn => by
        simp only [paper2GResidue] at hn
        rcases abs_cases n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
      (by
        rw [show -Real.pi * (1 / 10) * (2 * ((4 : ℕ) : ℝ)) = -(4 * Real.pi / 5) by
          push_cast; ring]
        have h4 : (4 : ℝ) ≤ Real.exp (4 * Real.pi / 5) := paper2_exp_ge_four (by linarith)
        have := paper2_exp_neg_le (by norm_num : (0 : ℝ) < 4) h4
        norm_num
        linarith)
    rw [show -Real.pi * (1 / 10) * ((4 : ℕ) : ℝ) ^ 2 = -(8 * Real.pi / 5) by
      push_cast; ring] at h
    push_cast at h
    linarith
  have hG1 : |paper2GRealSum 1| ≤ 36 * Real.exp (-(81 * Real.pi / 10)) := by
    have h := paper2_abs_GRealSum_le 1 9 (by norm_num)
      (fun n hn => by
        simp only [paper2GResidue] at hn
        rcases abs_cases n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
      (by
        rw [show -Real.pi * (1 / 10) * (2 * ((9 : ℕ) : ℝ)) = -(9 * Real.pi / 5) by
          push_cast; ring]
        have h4 : (4 : ℝ) ≤ Real.exp (9 * Real.pi / 5) := paper2_exp_ge_four (by linarith)
        have := paper2_exp_neg_le (by norm_num : (0 : ℝ) < 4) h4
        norm_num
        linarith)
    rw [show -Real.pi * (1 / 10) * ((9 : ℕ) : ℝ) ^ 2 = -(81 * Real.pi / 10) by
      push_cast; ring] at h
    push_cast at h
    linarith
  have hG2 : |paper2GRealSum 2| ≤ 24 * Real.exp (-(18 * Real.pi / 5)) := by
    have h := paper2_abs_GRealSum_le 2 6 (by norm_num)
      (fun n hn => by
        simp only [paper2GResidue] at hn
        rcases abs_cases n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
      (by
        rw [show -Real.pi * (1 / 10) * (2 * ((6 : ℕ) : ℝ)) = -(6 * Real.pi / 5) by
          push_cast; ring]
        have h4 : (4 : ℝ) ≤ Real.exp (6 * Real.pi / 5) := paper2_exp_ge_four (by linarith)
        have := paper2_exp_neg_le (by norm_num : (0 : ℝ) < 4) h4
        norm_num
        linarith)
    rw [show -Real.pi * (1 / 10) * ((6 : ℕ) : ℝ) ^ 2 = -(18 * Real.pi / 5) by
      push_cast; ring] at h
    push_cast at h
    linarith
  -- the leading block
  have hU3 := paper2_URealSum_three_ge
  have hG3 := paper2_GRealSum_three_le
  have hlead : (99 / 100) * (2 * Real.pi - 1) * Real.exp (-(3 * Real.pi / 5))
      ≤ -(paper2URealSum 3 * paper2GRealSum 3) := by
    have hUpos : (0 : ℝ) < (2 * Real.pi - 1) * Real.exp (-(Real.pi / 2)) :=
      mul_pos (by linarith) (Real.exp_pos _)
    have hfac : Real.exp (-(3 * Real.pi / 5))
        = Real.exp (-(Real.pi / 2)) * Real.exp (-(Real.pi / 10)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : (99 / 100) * Real.exp (-(Real.pi / 10)) ≤ -paper2GRealSum 3 := by linarith
    have h3 : (0 : ℝ) ≤ (99 / 100) * Real.exp (-(Real.pi / 10)) := by positivity
    rw [hfac]
    calc (99 / 100) * (2 * Real.pi - 1) *
          (Real.exp (-(Real.pi / 2)) * Real.exp (-(Real.pi / 10)))
        = ((2 * Real.pi - 1) * Real.exp (-(Real.pi / 2))) *
            ((99 / 100) * Real.exp (-(Real.pi / 10))) := by ring
      _ ≤ paper2URealSum 3 * -paper2GRealSum 3 :=
          mul_le_mul hU3 h2 h3 (le_trans hUpos.le hU3)
      _ = -(paper2URealSum 3 * paper2GRealSum 3) := by ring
  -- the three subtracted blocks
  have hb0 : |paper2URealSum 0 * paper2GRealSum 0| ≤ 16 * Real.exp (-(8 * Real.pi / 5)) := by
    rw [abs_mul]
    calc |paper2URealSum 0| * |paper2GRealSum 0|
        ≤ 1 * (16 * Real.exp (-(8 * Real.pi / 5))) :=
          mul_le_mul paper2_abs_URealSum_zero_le hG0 (abs_nonneg _) (by norm_num)
      _ = 16 * Real.exp (-(8 * Real.pi / 5)) := by ring
  have hb1 : |paper2URealSum 1 * paper2GRealSum 1| ≤ 396 * Real.exp (-(81 * Real.pi / 10)) := by
    rw [abs_mul]
    calc |paper2URealSum 1| * |paper2GRealSum 1|
        ≤ 11 * (36 * Real.exp (-(81 * Real.pi / 10))) :=
          mul_le_mul (paper2_abs_URealSum_le 1) hG1 (abs_nonneg _) (by norm_num)
      _ = 396 * Real.exp (-(81 * Real.pi / 10)) := by ring
  have hb2 : |paper2URealSum 2 * paper2GRealSum 2| ≤ 264 * Real.exp (-(18 * Real.pi / 5)) := by
    rw [abs_mul]
    calc |paper2URealSum 2| * |paper2GRealSum 2|
        ≤ 11 * (24 * Real.exp (-(18 * Real.pi / 5))) :=
          mul_le_mul (paper2_abs_URealSum_le 2) hG2 (abs_nonneg _) (by norm_num)
      _ = 264 * Real.exp (-(18 * Real.pi / 5)) := by ring
  -- the numeric comparison
  have he1 : Real.exp (-Real.pi) ≤ 1 / 13 := paper2_exp_neg_le (by norm_num) paper2_exp_pi
  have he3 : Real.exp (-(3 * Real.pi)) ≤ 1 / 2197 := by
    refine paper2_exp_neg_le (by norm_num) ?_
    have h := paper2_exp_pow_ge 3 (x := 3 * Real.pi) (by push_cast; linarith)
    norm_num at h
    linarith
  have he15 : Real.exp (-(15 * Real.pi / 2)) ≤ 1 / 2197 := by
    refine paper2_exp_neg_le (by norm_num) ?_
    have h := paper2_exp_pow_ge 3 (x := 15 * Real.pi / 2) (by push_cast; linarith)
    norm_num at h
    linarith
  have hbr : 0 < (99 / 100) * (2 * Real.pi - 1) - 16 * Real.exp (-Real.pi)
      - 396 * Real.exp (-(15 * Real.pi / 2)) - 264 * Real.exp (-(3 * Real.pi)) := by
    linarith
  have hf1 : Real.exp (-(8 * Real.pi / 5))
      = Real.exp (-(3 * Real.pi / 5)) * Real.exp (-Real.pi) := by
    rw [← Real.exp_add]; congr 1; ring
  have hf2 : Real.exp (-(81 * Real.pi / 10))
      = Real.exp (-(3 * Real.pi / 5)) * Real.exp (-(15 * Real.pi / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hf3 : Real.exp (-(18 * Real.pi / 5))
      = Real.exp (-(3 * Real.pi / 5)) * Real.exp (-(3 * Real.pi)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 < Real.exp (-(3 * Real.pi / 5)) := Real.exp_pos _
  have hkey : 0 < (99 / 100) * (2 * Real.pi - 1) * Real.exp (-(3 * Real.pi / 5))
      - 16 * Real.exp (-(8 * Real.pi / 5)) - 396 * Real.exp (-(81 * Real.pi / 10))
      - 264 * Real.exp (-(18 * Real.pi / 5)) := by
    rw [hf1, hf2, hf3]
    nlinarith [mul_pos hpos hbr]
  have hexp : ∑ j ∈ Finset.range 4,
        (-1 : ℝ) ^ j * paper2URealSum (j : ℤ) * paper2GRealSum (j : ℤ)
      = paper2URealSum 0 * paper2GRealSum 0 - paper2URealSum 1 * paper2GRealSum 1
        + paper2URealSum 2 * paper2GRealSum 2 - paper2URealSum 3 * paper2GRealSum 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  rw [paper2Witness_two_pi_P_sub_S, hexp]
  have e0 := abs_le.1 hb0
  have e1 := abs_le.1 hb1
  have e2 := abs_le.1 hb2
  linarith [hlead, e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, hkey]

/-- **`∂̄(ξ₁·)` does not vanish at `τ₀ = 2i`.**  A statement about this
explicit convergent lattice sum: it says this function fails the weight-one
harmonicity PDE at one point, which disproves harmonicity globally.  It is
**not** a statement that `q^{1/10}B(q)` has no harmonic completion, and not
yet a statement about `F̂`; Zwegers' completion theorem is not formalized. -/
theorem paper2_dbar_xi1_two_I_ne_zero :
    dbar (xi1 paper2LatticeCorrection) (2 * Complex.I) ≠ 0 :=
  paper2_dbar_xi1_two_I_ne_zero_iff.2 (ne_of_gt paper2_two_pi_P_sub_S_pos)

/-- **`Δ₁` does not vanish at `τ₀ = 2i`**, so this explicit function is not
weight-one harmonic.  Same scope caveat: it is not a statement about
`q^{1/10}B(q)` or about `F̂`, and Zwegers' completion theorem is not
formalized here. -/
theorem paper2_delta1_two_I_ne_zero :
    Delta1 paper2LatticeCorrection (2 * Complex.I) ≠ 0 :=
  paper2_delta1_two_I_ne_zero_iff.2 (ne_of_gt paper2_two_pi_P_sub_S_pos)

/-! ## The sign half, and Zwegers' Definition 2.1 object itself

The kernel split `(E₂ - E₁) = (E₂ - sgn₂) - (E₁ - sgn₁) + (sgn₂ - sgn₁)` has a
third piece, the *sign* series, whose coefficients do not depend on `τ`.
Adding it to the boundary correction gives Zwegers' completed indefinite theta
`ϑ_{a,b}^{c₂,c₁}` at this data, normalized by the manuscript's `½e^{-3πi/5}`.

The sign series is supported on the two thin slabs, where
`Q₀(v) ≥ (n²+T²)/100`, so it converges locally uniformly and is holomorphic;
hence it is annihilated by `∂/∂τ̄` and every `∂̄`, `ξ₁`, `Δ₁` statement about
the correction transfers verbatim to the completed object.

Nothing here proves that this object is the completion of `q^{1/10}B(q)`:
that is the separate sign-kernel bridge, and Zwegers' completion theorem is
still not formalized anywhere in this repository. -/

/-- The sign difference `sgn B₀(c₂,v) - sgn B₀(c₁,v)` of Zwegers'
Definition 2.1. -/
noncomputable def paper2SignDiff (p : ℤ × ℤ) : ℝ :=
  Real.sign (paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) -
    Real.sign (paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10))

/-- The sign half of the Definition 2.1 summand: the same phase and weight as
`paper2LatticeC2Term` and `paper2LatticeC1Term`, with `sgn₂ - sgn₁` in place of
the error kernels. -/
noncomputable def paper2LatticeSgnTerm (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  ((paper2SignDiff p : ℝ) : ℂ) * (paper2CharPhase p * paper2LatticeNome p τ)

/-- Its `τ`-derivative; the coefficients are `τ`-independent. -/
noncomputable def paper2LatticeSgnTermDeriv (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  ((paper2SignDiff p : ℝ) : ℂ) *
    (paper2CharPhase p * (paper2LatticeNome p τ * paper2LatticeNomeRate p))

/-- **Zwegers' completed indefinite theta at this paper's data**, normalized by
`½e^{-3πi/5}`: the full Definition 2.1 sum `(E₂ - E₁)`, obtained by adding the
sign half back to the boundary correction.

This is a definition of that lattice sum.  Nothing here identifies it with the
completion of `q^{1/10}B(q)`; Zwegers' completion theorem and his `S` law are
not formalized in this repository. -/
noncomputable def paper2LatticeTheta (τ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
    ∑' p : ℤ × ℤ,
      (paper2LatticeC2Term p τ - paper2LatticeC1Term p τ + paper2LatticeSgnTerm p τ)

theorem paper2_sign_ne_imp {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Real.sign a ≠ Real.sign b) : a * b < 0 := by
  rcases lt_trichotomy a 0 with ha' | ha' | ha'
  · rcases lt_trichotomy b 0 with hb' | hb' | hb'
    · exact absurd (by rw [Real.sign_of_neg ha', Real.sign_of_neg hb']) h
    · exact absurd hb' hb
    · exact mul_neg_of_neg_of_pos ha' hb'
  · exact absurd ha' ha
  · rcases lt_trichotomy b 0 with hb' | hb' | hb'
    · exact mul_neg_of_pos_of_neg ha' hb'
    · exact absurd hb' hb
    · exact absurd (by rw [Real.sign_of_pos ha', Real.sign_of_pos hb']) h

theorem paper2SignDiff_abs_le (p : ℤ × ℤ) : |paper2SignDiff p| ≤ 2 := by
  rw [paper2SignDiff]
  rcases Real.sign_apply_eq (paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) with
    h1 | h1 | h1 <;>
  rcases Real.sign_apply_eq (paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) with
    h2 | h2 | h2 <;>
  rw [h1, h2] <;> norm_num

/-- **The thin-slab support bound.**  Where the sign difference is nonzero,
`n·(10y+1) < 0`, hence `9n² < 25T²`, hence `Q₀(v) ≥ (n²+T²)/100`. -/
theorem paper2SignDiff_support (p : ℤ × ℤ) (h : paper2SignDiff p ≠ 0) :
    (paper2LongCoord p.1 p.2 : ℝ) ^ 2 + (paper2TransCoord p.1 p.2 : ℝ) ^ 2
      ≤ 100 * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) := by
  have hne : Real.sign (paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10))
      ≠ Real.sign (paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) :=
    fun hc => h (by rw [paper2SignDiff, hc, sub_self])
  have hn0 : ((paper2LongCoord p.1 p.2 : ℤ) : ℝ) ≠ 0 :=
    Int.cast_ne_zero.2 (paper2LongCoord_ne_zero p.1 p.2)
  have hc2 := paper2B0_c2_shift p.1 p.2
  have hc1 := paper2B0_c1_shift p.1 p.2
  have hy0 : (5 * ((p.2 : ℝ) + 1 / 10)) ≠ 0 := by
    intro hc
    have h1 : ((10 * p.2 + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    have h2 : (10 * p.2 + 1 : ℤ) = 0 := by exact_mod_cast h1
    omega
  rw [hc2, hc1] at hne
  have hprod := paper2_sign_ne_imp (neg_ne_zero.2 hn0) (neg_ne_zero.2 hy0) hne
  have hsign : ((paper2LongCoord p.1 p.2 : ℤ) : ℝ) *
      (3 * ((paper2LongCoord p.1 p.2 : ℤ) : ℝ) - 5 * ((paper2TransCoord p.1 p.2 : ℤ) : ℝ)) < 0 := by
    have hlin : 3 * ((paper2LongCoord p.1 p.2 : ℤ) : ℝ)
        - 5 * ((paper2TransCoord p.1 p.2 : ℤ) : ℝ) = 20 * (p.2 : ℝ) + 2 := by
      simp only [paper2LongCoord, paper2TransCoord]
      push_cast
      ring
    rw [hlin]
    nlinarith [hprod]
  have hn2 : 0 < ((paper2LongCoord p.1 p.2 : ℤ) : ℝ) ^ 2 := by positivity
  have hkey : 9 * ((paper2LongCoord p.1 p.2 : ℤ) : ℝ) ^ 2
      < 25 * ((paper2TransCoord p.1 p.2 : ℤ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (5 * ((paper2TransCoord p.1 p.2 : ℤ) : ℝ)
      - 3 * ((paper2LongCoord p.1 p.2 : ℤ) : ℝ)), hsign]
  rw [paper2Q0_shift]
  nlinarith [hkey, hn2]

/-! ### Majorants for the sign series -/

noncomputable def paper2SgnBoundNT (Y₀ : ℝ) (z : ℤ × ℤ) : ℝ :=
  2 * (Real.exp (-Real.pi * (Y₀ / 50) * (z.1 : ℝ) ^ 2) *
    Real.exp (-Real.pi * (Y₀ / 50) * (z.2 : ℝ) ^ 2))

noncomputable def paper2SgnBound (Y₀ : ℝ) (p : ℤ × ℤ) : ℝ :=
  paper2SgnBoundNT Y₀ (paper2NT p)

noncomputable def paper2SgnDerivBoundNT (Y₀ : ℝ) (z : ℤ × ℤ) : ℝ :=
  (Real.pi / 2) * ((z.1 : ℝ) ^ 2 * Real.exp (-Real.pi * (Y₀ / 50) * (z.1 : ℝ) ^ 2)) *
    Real.exp (-Real.pi * (Y₀ / 50) * (z.2 : ℝ) ^ 2)

noncomputable def paper2SgnDerivBound (Y₀ : ℝ) (p : ℤ × ℤ) : ℝ :=
  paper2SgnDerivBoundNT Y₀ (paper2NT p)

theorem summable_paper2SgnBoundNT {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun z : ℤ × ℤ => paper2SgnBoundNT Y₀ z) := by
  have hc : (0 : ℝ) < Y₀ / 50 := by positivity
  have h := Summable.mul_of_nonneg
    (f := fun m : ℤ => |(m : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 50) * (m : ℝ) ^ 2))
    (g := fun m : ℤ => |(m : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 50) * (m : ℝ) ^ 2))
    (summable_abs_pow_mul_exp_neg_pi_mul_sq hc 0)
    (summable_abs_pow_mul_exp_neg_pi_mul_sq hc 0)
    (fun m => by positivity) (fun m => by positivity)
  refine (h.mul_left 2).congr fun z => ?_
  simp only [paper2SgnBoundNT, pow_zero, one_mul]

theorem summable_paper2SgnDerivBoundNT {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun z : ℤ × ℤ => paper2SgnDerivBoundNT Y₀ z) := by
  have hc : (0 : ℝ) < Y₀ / 50 := by positivity
  have h := Summable.mul_of_nonneg
    (f := fun m : ℤ => Real.pi / 2 *
      (|(m : ℝ)| ^ 2 * Real.exp (-Real.pi * (Y₀ / 50) * (m : ℝ) ^ 2)))
    (g := fun m : ℤ => |(m : ℝ)| ^ 0 * Real.exp (-Real.pi * (Y₀ / 50) * (m : ℝ) ^ 2))
    ((summable_abs_pow_mul_exp_neg_pi_mul_sq hc 2).mul_left (Real.pi / 2))
    (summable_abs_pow_mul_exp_neg_pi_mul_sq hc 0)
    (fun m => by positivity) (fun m => by positivity)
  refine h.congr fun z => ?_
  simp only [paper2SgnDerivBoundNT, pow_zero, one_mul, sq_abs]

theorem summable_paper2SgnBound {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun p : ℤ × ℤ => paper2SgnBound Y₀ p) :=
  (summable_paper2SgnBoundNT hY₀).comp_injective paper2NT_injective

theorem summable_paper2SgnDerivBound {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    Summable (fun p : ℤ × ℤ => paper2SgnDerivBound Y₀ p) :=
  (summable_paper2SgnDerivBoundNT hY₀).comp_injective paper2NT_injective

/-- Uniform bound for the sign summand on a strip. -/
theorem norm_paper2LatticeSgnTerm_le {Y₀ : ℝ} (hY₀ : 0 < Y₀) (p : ℤ × ℤ) {τ : ℂ}
    (hτ : Y₀ < τ.im) : ‖paper2LatticeSgnTerm p τ‖ ≤ paper2SgnBound Y₀ p := by
  by_cases h : paper2SignDiff p = 0
  · rw [paper2LatticeSgnTerm, h, Complex.ofReal_zero, zero_mul, norm_zero, paper2SgnBound,
      paper2SgnBoundNT]
    positivity
  · have hsup := paper2SignDiff_support p h
    have hsq1 : (0 : ℝ) ≤ (paper2LongCoord p.1 p.2 : ℝ) ^ 2 := sq_nonneg _
    have hsq2 : (0 : ℝ) ≤ (paper2TransCoord p.1 p.2 : ℝ) ^ 2 := sq_nonneg _
    have hQ0 : 0 ≤ paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) := by linarith
    have hexp : Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im)
        ≤ Real.exp (-Real.pi * (Y₀ / 50) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2) *
          Real.exp (-Real.pi * (Y₀ / 50) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hb : Real.pi * (Y₀ / 50) * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2
            + (paper2LongCoord p.1 p.2 : ℝ) ^ 2)
          ≤ Real.pi * (Y₀ / 50) *
            (100 * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hd : 2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * Y₀
          ≤ 2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * τ.im :=
        mul_le_mul_of_nonneg_left hτ.le (mul_nonneg (by positivity) hQ0)
      linarith
    rw [paper2LatticeSgnTerm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_paper2CharPhase, one_mul, norm_paper2LatticeNome, paper2SgnBound, paper2SgnBoundNT,
      paper2NT]
    calc |paper2SignDiff p| *
          Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im)
        ≤ 2 * Real.exp (-(2 * Real.pi *
            paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im) :=
          mul_le_mul_of_nonneg_right (paper2SignDiff_abs_le p) (Real.exp_pos _).le
      _ ≤ 2 * (Real.exp (-Real.pi * (Y₀ / 50) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2) *
            Real.exp (-Real.pi * (Y₀ / 50) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)

theorem summable_paper2LatticeSgnTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ => paper2LatticeSgnTerm p τ) :=
  (summable_paper2SgnBound (show (0 : ℝ) < τ.im / 2 by positivity)).of_norm_bounded
    fun p => norm_paper2LatticeSgnTerm_le (by positivity) p (by linarith)

/-! ### Holomorphy of the sign series

The coefficients `paper2SignDiff` and `paper2CharPhase` do not depend on `τ`,
so each summand is a constant multiple of the nome and the whole series is
holomorphic where it converges locally uniformly. -/

theorem hasDerivAt_paper2LatticeSgnTerm (p : ℤ × ℤ) (τ : ℂ) :
    HasDerivAt (fun z : ℂ => paper2LatticeSgnTerm p z) (paper2LatticeSgnTermDeriv p τ) τ :=
  ((hasDerivAt_paper2LatticeNome p τ).const_mul (paper2CharPhase p)).const_mul
    ((paper2SignDiff p : ℝ) : ℂ)

theorem norm_paper2LatticeNomeRate (p : ℤ × ℤ) :
    ‖paper2LatticeNomeRate p‖ = 2 * Real.pi * |paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)| := by
  have h : paper2LatticeNomeRate p = ((2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ) : ℂ) * Complex.I := by
    rw [paper2LatticeNomeRate]
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_mul, abs_of_pos Real.pi_pos]
  norm_num

theorem norm_paper2LatticeSgnTermDeriv_le {Y₀ : ℝ} (hY₀ : 0 < Y₀) (p : ℤ × ℤ) {τ : ℂ}
    (hτ : Y₀ < τ.im) : ‖paper2LatticeSgnTermDeriv p τ‖ ≤ paper2SgnDerivBound Y₀ p := by
  by_cases h : paper2SignDiff p = 0
  · rw [paper2LatticeSgnTermDeriv, h, Complex.ofReal_zero, zero_mul, norm_zero,
      paper2SgnDerivBound, paper2SgnDerivBoundNT]
    positivity
  · have hsup := paper2SignDiff_support p h
    have hsq1 : (0 : ℝ) ≤ (paper2LongCoord p.1 p.2 : ℝ) ^ 2 := sq_nonneg _
    have hsq2 : (0 : ℝ) ≤ (paper2TransCoord p.1 p.2 : ℝ) ^ 2 := sq_nonneg _
    have hQ0 : 0 ≤ paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) := by linarith
    have habs : |paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)| = paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) := abs_of_nonneg hQ0
    have hQle : paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) ≤ (paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8 := by
      rw [paper2Q0_shift]
      linarith
    have hexp : Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im) ≤ Real.exp (-Real.pi * (Y₀ / 50) * (paper2TransCoord p.1 p.2 : ℝ) ^ 2) * Real.exp (-Real.pi * (Y₀ / 50) * (paper2LongCoord p.1 p.2 : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hb : Real.pi * (Y₀ / 50) * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 + (paper2LongCoord p.1 p.2 : ℝ) ^ 2)
          ≤ Real.pi * (Y₀ / 50) * (100 * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hd : 2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * Y₀ ≤ 2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * τ.im :=
        mul_le_mul_of_nonneg_left hτ.le (mul_nonneg (by positivity) hQ0)
      linarith
    rw [paper2LatticeSgnTermDeriv, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_paper2CharPhase, one_mul, norm_paper2LatticeNome,
      norm_paper2LatticeNomeRate, paper2SgnDerivBound, paper2SgnDerivBoundNT, paper2NT]
    have h1 : 2 * Real.pi * |paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)| ≤ 2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8) := by
      rw [habs]
      nlinarith [Real.pi_pos, hQle]
    have h2 : Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im) * (2 * Real.pi * |paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)|) ≤ Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im) * (2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have hA : |paper2SignDiff p| * (Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im) * (2 * Real.pi * |paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)|))
        ≤ 2 * (Real.exp (-(2 * Real.pi * paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) * τ.im) * (2 * Real.pi * ((paper2TransCoord p.1 p.2 : ℝ) ^ 2 / 8))) :=
      mul_le_mul (paper2SignDiff_abs_le p) h2 (by positivity) (by norm_num)
    have hC := mul_le_mul_of_nonneg_left hexp
      (show (0 : ℝ) ≤ Real.pi / 2 * (paper2TransCoord p.1 p.2 : ℝ) ^ 2 by positivity)
    linarith

theorem hasDerivAt_tsum_paper2LatticeSgnTerm {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeSgnTerm p z)
      (∑' p : ℤ × ℤ, paper2LatticeSgnTermDeriv p τ) τ := by
  have hY₀ : (0 : ℝ) < τ.im / 2 := by positivity
  have hmem : τ.im / 2 < τ.im := by linarith
  have hopen : IsOpen {z : ℂ | τ.im / 2 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected {z : ℂ | τ.im / 2 < z.im} :=
    (convex_halfSpace_im_gt (r := τ.im / 2)).isPreconnected
  exact hasDerivAt_tsum_of_isPreconnected (summable_paper2SgnDerivBound hY₀) hopen hconn
    (fun p z _ => hasDerivAt_paper2LatticeSgnTerm p z)
    (fun p z hz => norm_paper2LatticeSgnTermDeriv_le hY₀ p hz) hmem
    (summable_paper2LatticeSgnTerm hτ) hmem

/-- **The sign series is annihilated by `∂/∂τ̄`.** -/
theorem dbar_tsum_paper2LatticeSgnTerm {τ : ℂ} (hτ : 0 < τ.im) :
    dbar (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeSgnTerm p z) τ = 0 :=
  dbar_of_hasDerivAt (hasDerivAt_tsum_paper2LatticeSgnTerm hτ)

theorem differentiableAt_tsum_paper2LatticeSgnTerm {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℝ (fun z : ℂ => ∑' p : ℤ × ℤ, paper2LatticeSgnTerm p z) τ :=
  (((hasDerivAt_tsum_paper2LatticeSgnTerm hτ).hasFDerivAt).restrictScalars ℝ).differentiableAt

theorem dbar_add {f g : ℂ → ℂ} {τ : ℂ} (hf : DifferentiableAt ℝ f τ)
    (hg : DifferentiableAt ℝ g τ) :
    dbar (fun z : ℂ => f z + g z) τ = dbar f τ + dbar g τ := by
  have h : HasFDerivAt (fun z : ℂ => f z + g z) (fderiv ℝ f τ + fderiv ℝ g τ) τ :=
    hf.hasFDerivAt.add hg.hasFDerivAt
  rw [dbar_of_hasFDerivAt h, dbar_eq, dbar_eq]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-! ### The decomposition and the transfer to `F̂` -/

theorem summable_paper2LatticeThetaTerm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun p : ℤ × ℤ =>
      paper2LatticeC2Term p τ - paper2LatticeC1Term p τ + paper2LatticeSgnTerm p τ) :=
  (summable_paper2LatticeTerm hτ).add (summable_paper2LatticeSgnTerm hτ)

/-- **The decomposition.**  Zwegers' Definition 2.1 object is the sign series
plus the boundary correction, with the same normalization. -/
theorem paper2LatticeTheta_eq {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta τ
      = (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
          (∑' p : ℤ × ℤ, paper2LatticeSgnTerm p τ) + paper2LatticeCorrection τ := by
  rw [paper2LatticeTheta, paper2LatticeCorrection,
    (summable_paper2LatticeTerm hτ).tsum_add (summable_paper2LatticeSgnTerm hτ)]
  ring

theorem differentiableAt_paper2LatticeTheta {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℝ paper2LatticeTheta τ := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : paper2LatticeTheta =ᶠ[nhds τ] fun z : ℂ =>
      (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
        (∑' p : ℤ × ℤ, paper2LatticeSgnTerm p z) + paper2LatticeCorrection z := by
    filter_upwards [hopen.mem_nhds hτ] with z hz using paper2LatticeTheta_eq hz
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev)
  exact ((differentiableAt_tsum_paper2LatticeSgnTerm hτ).const_mul _).add
    (hasFDerivAt_paper2LatticeCorrection hτ).differentiableAt

/-- **The transfer.**  `∂/∂τ̄` does not see the sign half, so it agrees on the
completed object and on the boundary correction. -/
theorem paper2_dbar_latticeTheta {τ : ℂ} (hτ : 0 < τ.im) :
    dbar paper2LatticeTheta τ = dbar paper2LatticeCorrection τ := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : paper2LatticeTheta =ᶠ[nhds τ] fun z : ℂ =>
      (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
        (∑' p : ℤ × ℤ, paper2LatticeSgnTerm p z) + paper2LatticeCorrection z := by
    filter_upwards [hopen.mem_nhds hτ] with z hz using paper2LatticeTheta_eq hz
  rw [dbar_congr_of_eventuallyEq hev,
    dbar_add ((differentiableAt_tsum_paper2LatticeSgnTerm hτ).const_mul _)
      (hasFDerivAt_paper2LatticeCorrection hτ).differentiableAt,
    dbar_const_mul _ (differentiableAt_tsum_paper2LatticeSgnTerm hτ),
    dbar_tsum_paper2LatticeSgnTerm hτ, mul_zero, zero_add]

theorem paper2_xi1_latticeTheta {τ : ℂ} (hτ : 0 < τ.im) :
    xi1 paper2LatticeTheta τ = xi1 paper2LatticeCorrection τ := by
  rw [xi1, xi1, paper2_dbar_latticeTheta hτ]

/-- The `Δ₁` transfer.  This needs the `ξ₁` transfer to hold on a whole
neighbourhood, not just at the point, because the outer `ξ₁` differentiates;
that is why the previous lemma is proved for every `τ` in the half-plane. -/
theorem paper2_delta1_latticeTheta {τ : ℂ} (hτ : 0 < τ.im) :
    Delta1 paper2LatticeTheta τ = Delta1 paper2LatticeCorrection τ := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : xi1 paper2LatticeTheta =ᶠ[nhds τ] xi1 paper2LatticeCorrection := by
    filter_upwards [hopen.mem_nhds hτ] with z hz using paper2_xi1_latticeTheta hz
  rw [Delta1, Delta1, xi1, xi1, dbar_congr_of_eventuallyEq hev]

/-! ### The headline results, restated for Zwegers' object -/

/-- **`eq:dbar-exact` for the completed indefinite theta itself.** -/
theorem paper2_dbar_latticeTheta_exact {τ : ℂ} (hτ : 0 < τ.im) :
    dbar paper2LatticeTheta τ
      = -(Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ)))
        * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j * paper2ThetaComponent (j : ℤ) τ *
            (starRingEnd ℂ) (paper2GComponent (j : ℤ) τ) :=
  (paper2_dbar_latticeTheta hτ).trans (paper2_dbar_latticeCorrection hτ)

/-- **`eq:xi-exact` for the completed indefinite theta itself.** -/
theorem paper2_xi1_latticeTheta_exact {τ : ℂ} (hτ : 0 < τ.im) :
    xi1 paper2LatticeTheta τ
      = -(((Real.sqrt τ.im / (2 * Real.sqrt 10) : ℝ)) : ℂ)
        * ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) τ) * paper2GComponent (j : ℤ) τ :=
  (paper2_xi1_latticeTheta hτ).trans (paper2_xi1_latticeCorrection hτ)

/-- **Zwegers' Definition 2.1 object at this data is not weight-one harmonic.**
`Δ₁` fails to vanish at `τ₀ = 2i`, so it fails the harmonicity PDE, so it is
not a harmonic Maass form of weight one.

This is a statement about that explicit convergent lattice sum.  It is not a
statement that `q^{1/10}B(q)` has no harmonic completion: the identification of
this object with a completion of `q^{1/10}B(q)` is the separate sign-kernel
bridge, and Zwegers' completion theorem is not formalized here. -/
theorem paper2_delta1_latticeTheta_two_I_ne_zero :
    Delta1 paper2LatticeTheta (2 * Complex.I) ≠ 0 := by
  have hτ : (0 : ℝ) < (2 * Complex.I).im := by simp
  rw [paper2_delta1_latticeTheta hτ]
  exact paper2_delta1_two_I_ne_zero

theorem paper2_dbar_xi1_latticeTheta_two_I_ne_zero :
    dbar (xi1 paper2LatticeTheta) (2 * Complex.I) ≠ 0 := by
  have hτ : (0 : ℝ) < (2 * Complex.I).im := by simp
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : xi1 paper2LatticeTheta =ᶠ[nhds (2 * Complex.I)] xi1 paper2LatticeCorrection := by
    filter_upwards [hopen.mem_nhds hτ] with z hz using paper2_xi1_latticeTheta hz
  rw [dbar_congr_of_eventuallyEq hev]
  exact paper2_dbar_xi1_two_I_ne_zero

/-- The `ξ₁` expression is not the zero function.  This follows from the
nonzero `∂̄(ξ₁·)` witness at `2i`, rather than from numerical sampling. -/
theorem paper2_xi1_latticeTheta_ne_zero : xi1 paper2LatticeTheta ≠ 0 := by
  intro hzero
  have h := paper2_dbar_xi1_latticeTheta_two_I_ne_zero
  rw [hzero] at h
  simp [dbar, wirtingerBarCLM_apply] at h

/-- The `∂̄` expression is not the zero function. -/
theorem paper2_dbar_latticeTheta_ne_zero :
    (fun τ => dbar paper2LatticeTheta τ) ≠ 0 := by
  intro hzero
  apply paper2_xi1_latticeTheta_ne_zero
  funext τ
  rw [xi1, congrFun hzero τ]
  simp

/-! ### `⟨T⟩`-quasiperiodicity for the completed object -/

theorem paper2LatticeSgnTerm_add_one (p : ℤ × ℤ) (τ : ℂ) :
    paper2LatticeSgnTerm p (τ + 1)
      = Complex.exp (Real.pi * Complex.I / 5) * paper2LatticeSgnTerm p τ := by
  rw [paper2LatticeSgnTerm, paper2LatticeSgnTerm, paper2LatticeNome_add_one]
  ring

theorem paper2LatticeTheta_tsum_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    (∑' p : ℤ × ℤ, (paper2LatticeC2Term p (τ + 1) - paper2LatticeC1Term p (τ + 1)
        + paper2LatticeSgnTerm p (τ + 1)))
      = Complex.exp (Real.pi * Complex.I / 5) *
          ∑' p : ℤ × ℤ, (paper2LatticeC2Term p τ - paper2LatticeC1Term p τ
            + paper2LatticeSgnTerm p τ) := by
  rw [← (summable_paper2LatticeThetaTerm hτ).tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [paper2LatticeC2Term_add_one, paper2LatticeC1Term_add_one, paper2LatticeSgnTerm_add_one]
  ring

theorem paper2LatticeTheta_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta (τ + 1)
      = Complex.exp (Real.pi * Complex.I / 5) * paper2LatticeTheta τ := by
  rw [paper2LatticeTheta, paper2LatticeTheta, paper2LatticeTheta_tsum_add_one hτ]
  ring

theorem paper2LatticeTheta_add_nat {τ : ℂ} (hτ : 0 < τ.im) (m : ℕ) :
    paper2LatticeTheta (τ + m)
      = Complex.exp ((m : ℂ) * (Real.pi * Complex.I / 5)) * paper2LatticeTheta τ := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hk : (0 : ℝ) < (τ + (k : ℂ)).im := by simpa using hτ
      have hstep : τ + ((k + 1 : ℕ) : ℂ) = (τ + (k : ℂ)) + 1 := by push_cast; ring
      rw [hstep, paper2LatticeTheta_add_one hk, ih, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem paper2LatticeTheta_add_ten {τ : ℂ} (hτ : 0 < τ.im) :
    paper2LatticeTheta (τ + 10) = paper2LatticeTheta τ := by
  have h := paper2LatticeTheta_add_nat hτ 10
  norm_num at h
  rw [h, show (10 : ℂ) * ((Real.pi : ℂ) * Complex.I / 5) = 2 * (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_two_pi_mul_I, one_mul]

end

end Ch10
end QseriesFormalization
