import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Real.Sign

/-!
# Paper 2: Zwegers' error kernel

This file begins the analytic half of Paper 2 with the normalized real error
kernel used in Zwegers' indefinite theta completion.  The definition is made
from Mathlib's interval integral, so its derivative follows from the
fundamental theorem of calculus and its boundary values follow from the
Gaussian integral.  No modular-transformation statement is used here.
-/

namespace QseriesFormalization
namespace Ch10

open Filter MeasureTheory Set
open scoped Interval

noncomputable section

/-! ## Definition and local differential properties -/

/-- The Gaussian integrand in Zwegers' normalization.  The factor `Real.pi`
is chosen so that its integral over the real line is exactly one. -/
def zwegersGaussian (u : ℝ) : ℝ := Real.exp (-Real.pi * u ^ 2)

/-- Zwegers' error kernel
`E(z) = 2 ∫_0^z exp(-πu²) du`.  This normalization has limits `±1` at the two
ends of the real line. -/
def zwegersErrorKernel (z : ℝ) : ℝ :=
  2 * ∫ u : ℝ in (0 : ℝ)..z, zwegersGaussian u

/-- The normalized Gaussian integrand is continuous on the real line. -/
theorem continuous_zwegersGaussian : Continuous zwegersGaussian := by
  unfold zwegersGaussian
  fun_prop

@[simp] theorem zwegersErrorKernel_zero : zwegersErrorKernel 0 = 0 := by
  simp [zwegersErrorKernel]

/-- The fundamental derivative identity `E'(z)=2 exp(-πz²)`. -/
theorem hasDerivAt_zwegersErrorKernel (z : ℝ) :
    HasDerivAt zwegersErrorKernel (2 * zwegersGaussian z) z := by
  simpa [zwegersErrorKernel] using
    (continuous_zwegersGaussian.integral_hasStrictDerivAt 0 z).hasDerivAt.const_mul 2

theorem deriv_zwegersErrorKernel (z : ℝ) :
    deriv zwegersErrorKernel z = 2 * zwegersGaussian z :=
  (hasDerivAt_zwegersErrorKernel z).deriv

/-- The Gaussian is even, hence the oriented integral defining `E` is odd. -/
theorem zwegersErrorKernel_neg (z : ℝ) :
    zwegersErrorKernel (-z) = -zwegersErrorKernel z := by
  have hmirror :
      (∫ u : ℝ in -z..0, zwegersGaussian u) =
        ∫ u : ℝ in 0..z, zwegersGaussian u := by
    calc
      (∫ u : ℝ in -z..0, zwegersGaussian u) =
          ∫ u : ℝ in 0..z, zwegersGaussian (-u) := by
            simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
              (f := zwegersGaussian) (a := 0) (b := z)).symm
      _ = ∫ u : ℝ in 0..z, zwegersGaussian u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        simp [zwegersGaussian]
  unfold zwegersErrorKernel
  rw [intervalIntegral.integral_symm, hmirror]
  ring

/-! ## Gaussian mass and boundary values -/

/-- The positive half-line has Gaussian mass `1/2` in the chosen
normalization. -/
theorem integral_Ioi_zwegersGaussian :
    ∫ u : ℝ in Ioi 0, zwegersGaussian u = 1 / 2 := by
  unfold zwegersGaussian
  rw [integral_gaussian_Ioi]
  rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one]

/-- By evenness, the negative half-line has the same Gaussian mass. -/
theorem integral_Iic_zwegersGaussian :
    ∫ u : ℝ in Iic 0, zwegersGaussian u = 1 / 2 := by
  have hneg := integral_comp_neg_Ioi (0 : ℝ) zwegersGaussian
  have heven : (fun u : ℝ => zwegersGaussian (-u)) = zwegersGaussian := by
    funext u
    simp [zwegersGaussian]
  rw [heven, neg_zero, integral_Ioi_zwegersGaussian] at hneg
  exact hneg.symm

/-- The error kernel tends to `1` at the positive end. -/
theorem tendsto_zwegersErrorKernel_atTop :
    Tendsto zwegersErrorKernel atTop (nhds 1) := by
  have hlim := intervalIntegral_tendsto_integral_Ioi 0
    ((integrable_exp_neg_mul_sq Real.pi_pos).integrableOn)
    tendsto_id
  have hscaled : Tendsto
      (fun z : ℝ => 2 * ∫ u : ℝ in 0..z,
        Real.exp (-Real.pi * u ^ 2)) atTop
      (nhds (2 * ∫ u : ℝ in Ioi 0, Real.exp (-Real.pi * u ^ 2))) :=
    tendsto_const_nhds.mul hlim
  have hmass : (∫ u : ℝ in Ioi 0, Real.exp (-Real.pi * u ^ 2)) = 1 / 2 := by
    simpa only [zwegersGaussian] using integral_Ioi_zwegersGaussian
  rw [hmass] at hscaled
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at hscaled
  change Tendsto
    (fun z : ℝ => 2 * ∫ u : ℝ in 0..z, zwegersGaussian u)
    atTop (nhds 1)
  simpa only [zwegersGaussian, neg_mul] using hscaled

/-- The error kernel tends to `-1` at the negative end. -/
theorem tendsto_zwegersErrorKernel_atBot :
    Tendsto zwegersErrorKernel atBot (nhds (-1)) := by
  have hlim := intervalIntegral_tendsto_integral_Iic 0
    ((integrable_exp_neg_mul_sq Real.pi_pos).integrableOn)
    tendsto_id
  have hscaled : Tendsto
      (fun z : ℝ => (-2) * ∫ u : ℝ in z..0,
        Real.exp (-Real.pi * u ^ 2)) atBot
      (nhds ((-2) * ∫ u : ℝ in Iic 0, Real.exp (-Real.pi * u ^ 2))) :=
    tendsto_const_nhds.mul hlim
  have hmass : (∫ u : ℝ in Iic 0, Real.exp (-Real.pi * u ^ 2)) = 1 / 2 := by
    simpa only [zwegersGaussian] using integral_Iic_zwegersGaussian
  rw [hmass] at hscaled
  rw [show (-2 : ℝ) * (1 / 2) = -1 by norm_num] at hscaled
  have hfun : zwegersErrorKernel =
      fun z : ℝ => (-2) * ∫ u : ℝ in z..0, zwegersGaussian u := by
    funext z
    unfold zwegersErrorKernel
    rw [intervalIntegral.integral_symm]
    ring
  rw [hfun]
  simpa only [zwegersGaussian, neg_mul] using hscaled

/-! ## The scaled boundary kernel appearing in Paper 2 -/

/-- The surviving `c₂` correction evaluates the error kernel at
`-n sqrt(Y/10)`, where `Y` is the imaginary part of `τ`. -/
def paper2BoundaryError (n : ℝ) (Y : ℝ) : ℝ :=
  zwegersErrorKernel (-n * Real.sqrt (Y / 10))

/-- Chain-rule form of the boundary derivative before denominator
normalization.  This is the stable interface for later complex differentiation. -/
theorem hasDerivAt_paper2BoundaryError_raw (n Y : ℝ) (hY : 0 < Y) :
    HasDerivAt (paper2BoundaryError n)
      ((2 * zwegersGaussian (-n * Real.sqrt (Y / 10))) *
        ((-n) * ((1 / 10) / (2 * Real.sqrt (Y / 10))))) Y := by
  have hdiv : HasDerivAt (fun t : ℝ => t / 10) (1 / 10) Y := by
    simpa using (hasDerivAt_id Y).div_const (10 : ℝ)
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (t / 10))
      ((1 / 10) / (2 * Real.sqrt (Y / 10))) Y :=
    hdiv.sqrt (by positivity)
  have hinner : HasDerivAt (fun t : ℝ => -n * Real.sqrt (t / 10))
      ((-n) * ((1 / 10) / (2 * Real.sqrt (Y / 10)))) Y :=
    hsqrt.const_mul (-n)
  change HasDerivAt
    (fun t : ℝ => zwegersErrorKernel (-n * Real.sqrt (t / 10)))
    ((2 * zwegersGaussian (-n * Real.sqrt (Y / 10))) *
      ((-n) * ((1 / 10) / (2 * Real.sqrt (Y / 10))))) Y
  have houter : HasDerivAt zwegersErrorKernel
      (2 * zwegersGaussian (-n * Real.sqrt (Y / 10)))
      (-n * Real.sqrt (Y / 10)) :=
    hasDerivAt_zwegersErrorKernel (-n * Real.sqrt (Y / 10))
  have hcomp : HasDerivAt
      (zwegersErrorKernel ∘ fun t : ℝ => -n * Real.sqrt (t / 10))
      ((2 * zwegersGaussian (-n * Real.sqrt (Y / 10))) *
        ((-n) * ((1 / 10) / (2 * Real.sqrt (Y / 10))))) Y :=
    houter.comp Y hinner
  simpa only [Function.comp_apply] using hcomp

/-- Paper-normalized real derivative of the surviving boundary kernel:
`d/dY E(-n sqrt(Y/10)) = -n / sqrt(10Y) * exp(-πn²Y/10)`. -/
theorem hasDerivAt_paper2BoundaryError (n Y : ℝ) (hY : 0 < Y) :
    HasDerivAt (paper2BoundaryError n)
      ((-n / Real.sqrt (10 * Y)) * Real.exp (-Real.pi * n ^ 2 * Y / 10)) Y := by
  have hraw := hasDerivAt_paper2BoundaryError_raw n Y hY
  convert hraw using 1
  have hsmall : 0 ≤ Y / 10 := by positivity
  have hlarge : 0 ≤ 10 * Y := by positivity
  have hsSmall : (Real.sqrt (Y / 10)) ^ 2 = Y / 10 := Real.sq_sqrt hsmall
  have hsLarge : (Real.sqrt (10 * Y)) ^ 2 = 10 * Y := Real.sq_sqrt hlarge
  have hsqrt : Real.sqrt (10 * Y) = 10 * Real.sqrt (Y / 10) := by
    have hnonnegSmall : 0 ≤ Real.sqrt (Y / 10) := Real.sqrt_nonneg _
    have hnonnegLarge : 0 ≤ Real.sqrt (10 * Y) := Real.sqrt_nonneg _
    nlinarith
  have harg : (-n * Real.sqrt (Y / 10)) ^ 2 = n ^ 2 * Y / 10 := by
    rw [mul_pow, neg_sq, hsSmall]
    ring
  have hsSmallPos : 0 < Real.sqrt (Y / 10) := Real.sqrt_pos.2 (by positivity)
  rw [zwegersGaussian, harg, hsqrt]
  field_simp [hsSmallPos.ne']

/-! ## Gaussian tail identity and the Mills-type bound

The boundary limits proved above are upgraded here to a quantitative
statement.  The tail identity `1-E(z)=2∫_{u>z}e^{-πu²}du` follows from
splitting the Gaussian mass of `Ioi 0` at `z`, and the Mills-type bound
follows from the classical comparison `e^{-πu²} ≤ (u/z)e^{-πu²}`, valid for
`u>z>0`, whose primitive `-(2π)⁻¹e^{-πu²}` is elementary. -/

/-- The normalized Gaussian is integrable on the real line. -/
theorem integrable_zwegersGaussian : Integrable zwegersGaussian :=
  integrable_exp_neg_mul_sq Real.pi_pos

/-- The normalized Gaussian is strictly positive. -/
theorem zwegersGaussian_pos (u : ℝ) : 0 < zwegersGaussian u :=
  Real.exp_pos _

/-- The normalized Gaussian decays to zero at `+∞`. -/
theorem tendsto_zwegersGaussian_atTop :
    Tendsto zwegersGaussian atTop (nhds 0) := by
  show Tendsto (fun u : ℝ => Real.exp (-Real.pi * u ^ 2)) atTop (nhds 0)
  have hpos : Tendsto (fun t : ℝ => Real.pi * t ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop Real.pi_pos (tendsto_pow_atTop (n := 2) (by norm_num))
  have harg : Tendsto (fun t : ℝ => -Real.pi * t ^ 2) atTop atBot := by
    simpa only [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp hpos
  simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp harg

/-- The Gaussian mass of the half-line `Ioi z`, expressed through the oriented
integral defining `E`.  This single splitting computation is what makes both
the tail identity and the Mills bound available. -/
theorem integral_Ioi_zwegersGaussian_eq (z : ℝ) :
    (∫ u : ℝ in Ioi z, zwegersGaussian u)
      = 1 / 2 - ∫ u : ℝ in (0 : ℝ)..z, zwegersGaussian u := by
  have hdisj : ∀ a b : ℝ, Disjoint (Ioc a b) (Ioi b) := by
    intro a b
    exact Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx')
  rcases le_total (0 : ℝ) z with hz | hz
  · have hsplit :
        (∫ u : ℝ in Ioc (0 : ℝ) z, zwegersGaussian u) +
            (∫ u : ℝ in Ioi z, zwegersGaussian u)
          = ∫ u : ℝ in Ioi (0 : ℝ), zwegersGaussian u := by
      rw [← setIntegral_union (hdisj 0 z) measurableSet_Ioi
        integrable_zwegersGaussian.integrableOn
        integrable_zwegersGaussian.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hz]
    rw [integral_Ioi_zwegersGaussian] at hsplit
    rw [intervalIntegral.integral_of_le hz]
    linarith
  · have hsplit :
        (∫ u : ℝ in Ioc z (0 : ℝ), zwegersGaussian u) +
            (∫ u : ℝ in Ioi (0 : ℝ), zwegersGaussian u)
          = ∫ u : ℝ in Ioi z, zwegersGaussian u := by
      rw [← setIntegral_union (hdisj z 0) measurableSet_Ioi
        integrable_zwegersGaussian.integrableOn
        integrable_zwegersGaussian.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hz]
    rw [integral_Ioi_zwegersGaussian] at hsplit
    have hsym : (∫ u : ℝ in (0 : ℝ)..z, zwegersGaussian u)
        = -∫ u : ℝ in Ioc z (0 : ℝ), zwegersGaussian u := by
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hz]
    rw [hsym]
    linarith

/-- Exact Gaussian tail identity in the paper's normalization:
`1 - E(z) = 2∫_{u>z}e^{-πu²}du`, valid for every real `z`. -/
theorem one_sub_zwegersErrorKernel (z : ℝ) :
    1 - zwegersErrorKernel z = 2 * ∫ u : ℝ in Ioi z, zwegersGaussian u := by
  rw [integral_Ioi_zwegersGaussian_eq]
  simp only [zwegersErrorKernel]
  ring

/-- The tail `1-E(z)` is nonnegative, i.e. `E(z) ≤ 1`. -/
theorem zwegersErrorKernel_le_one (z : ℝ) : zwegersErrorKernel z ≤ 1 := by
  have hnn : 0 ≤ ∫ u : ℝ in Ioi z, zwegersGaussian u :=
    setIntegral_nonneg measurableSet_Ioi fun u _ => (zwegersGaussian_pos u).le
  have h := one_sub_zwegersErrorKernel z
  linarith

/-- The mirrored tail `E(z)+1` is nonnegative, i.e. `-1 ≤ E(z)`; this is the
oddness reflection of `zwegersErrorKernel_le_one`. -/
theorem neg_one_le_zwegersErrorKernel (z : ℝ) : -1 ≤ zwegersErrorKernel z := by
  have h := zwegersErrorKernel_le_one (-z)
  rw [zwegersErrorKernel_neg] at h
  linarith

/-- The first Gaussian moment on a half-line:
`∫_{u>z} u e^{-πu²}du = e^{-πz²}/(2π)`. -/
theorem integral_Ioi_mul_zwegersGaussian (z : ℝ) :
    (∫ u : ℝ in Ioi z, u * zwegersGaussian u)
      = Real.exp (-Real.pi * z ^ 2) / (2 * Real.pi) := by
  have hint : IntegrableOn (fun u : ℝ => u * zwegersGaussian u) (Ioi z) :=
    (integrable_mul_exp_neg_mul_sq Real.pi_pos).integrableOn
  have hscaled :
      IntegrableOn (fun u : ℝ => 2 * Real.pi * (u * zwegersGaussian u)) (Ioi z) :=
    hint.const_mul _
  have hderiv : ∀ x ∈ Ici z,
      HasDerivAt (fun t : ℝ => -Real.exp (-Real.pi * t ^ 2))
        (2 * Real.pi * (x * zwegersGaussian x)) x := by
    intro x _
    have hx : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h1 : HasDerivAt (fun t : ℝ => -Real.pi * t ^ 2) (-Real.pi * (2 * x)) x :=
      hx.const_mul (-Real.pi)
    have h2 : HasDerivAt (fun t : ℝ => -Real.exp (-Real.pi * t ^ 2))
        (-(Real.exp (-Real.pi * x ^ 2) * (-Real.pi * (2 * x)))) x := h1.exp.neg
    have hval : -(Real.exp (-Real.pi * x ^ 2) * (-Real.pi * (2 * x)))
        = 2 * Real.pi * (x * zwegersGaussian x) := by
      simp only [zwegersGaussian]
      ring
    rw [← hval]
    exact h2
  have hlim :
      Tendsto (fun t : ℝ => -Real.exp (-Real.pi * t ^ 2)) atTop (nhds 0) := by
    have hg : Tendsto (fun t : ℝ => Real.exp (-Real.pi * t ^ 2)) atTop (nhds 0) :=
      tendsto_zwegersGaussian_atTop
    simpa using hg.neg
  have hmain : (∫ u : ℝ in Ioi z, 2 * Real.pi * (u * zwegersGaussian u))
      = 0 - -Real.exp (-Real.pi * z ^ 2) :=
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hscaled hlim
  rw [integral_const_mul] at hmain
  have hmain' : 2 * Real.pi * (∫ u : ℝ in Ioi z, u * zwegersGaussian u)
      = Real.exp (-Real.pi * z ^ 2) := by
    rw [hmain]; ring
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity)
  rw [eq_div_iff hpi]
  linear_combination hmain'

/-- Mills-type Gaussian tail bound: for `z>0`,
`1 - E(z) ≤ e^{-πz²}/(πz)`. -/
theorem one_sub_zwegersErrorKernel_le {z : ℝ} (hz : 0 < z) :
    1 - zwegersErrorKernel z ≤ Real.exp (-Real.pi * z ^ 2) / (Real.pi * z) := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hg : IntegrableOn zwegersGaussian (Ioi z) :=
    integrable_zwegersGaussian.integrableOn
  have hmom : IntegrableOn (fun u : ℝ => z⁻¹ * (u * zwegersGaussian u)) (Ioi z) :=
    ((integrable_mul_exp_neg_mul_sq Real.pi_pos).const_mul z⁻¹).integrableOn
  have hinv : z⁻¹ * z = 1 := inv_mul_cancel₀ hzne
  have hcomp : (∫ u : ℝ in Ioi z, zwegersGaussian u)
      ≤ ∫ u : ℝ in Ioi z, z⁻¹ * (u * zwegersGaussian u) := by
    refine setIntegral_mono_on hg hmom measurableSet_Ioi ?_
    intro u hu
    have hu' : z < u := hu
    have hzu : 1 ≤ z⁻¹ * u := by
      nlinarith [mul_pos (inv_pos.2 hz) (sub_pos.2 hu'), hinv]
    calc zwegersGaussian u = 1 * zwegersGaussian u := (one_mul _).symm
      _ ≤ z⁻¹ * u * zwegersGaussian u :=
          mul_le_mul_of_nonneg_right hzu (zwegersGaussian_pos u).le
      _ = z⁻¹ * (u * zwegersGaussian u) := by ring
  have hval : (∫ u : ℝ in Ioi z, z⁻¹ * (u * zwegersGaussian u))
      = z⁻¹ * (Real.exp (-Real.pi * z ^ 2) / (2 * Real.pi)) := by
    rw [integral_const_mul, integral_Ioi_mul_zwegersGaussian]
  rw [hval] at hcomp
  have hfinal : 2 * (z⁻¹ * (Real.exp (-Real.pi * z ^ 2) / (2 * Real.pi)))
      = Real.exp (-Real.pi * z ^ 2) / (Real.pi * z) := by
    field_simp
  rw [one_sub_zwegersErrorKernel, ← hfinal]
  linarith

/-- The negative half of the Mills bound, obtained from oddness: for `z<0`,
`E(z) + 1 ≤ e^{-πz²}/(π(-z))`. -/
theorem zwegersErrorKernel_add_one_le {z : ℝ} (hz : z < 0) :
    zwegersErrorKernel z + 1 ≤ Real.exp (-Real.pi * z ^ 2) / (Real.pi * -z) := by
  have hb := one_sub_zwegersErrorKernel_le (z := -z) (by linarith)
  rw [zwegersErrorKernel_neg] at hb
  have hsq : (-z) ^ 2 = z ^ 2 := by ring
  rw [hsq] at hb
  linarith

/-- Uniform Zwegers correction bound: for `z≠0`,
`|E(z) - sgn(z)| ≤ e^{-πz²}/(π|z|)`.  This is the exact Gaussian decay used
for the completed `c₂` longitudinal series. -/
theorem abs_zwegersErrorKernel_sub_sign_le {z : ℝ} (hz : z ≠ 0) :
    |zwegersErrorKernel z - Real.sign z|
      ≤ Real.exp (-Real.pi * z ^ 2) / (Real.pi * |z|) := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hlow : -1 ≤ zwegersErrorKernel z := neg_one_le_zwegersErrorKernel z
    have hb := zwegersErrorKernel_add_one_le hneg
    rw [Real.sign_of_neg hneg, abs_of_neg hneg,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ zwegersErrorKernel z - -1)]
    linarith
  · have hhigh : zwegersErrorKernel z ≤ 1 := zwegersErrorKernel_le_one z
    have hb := one_sub_zwegersErrorKernel_le hpos
    rw [Real.sign_of_pos hpos, abs_of_pos hpos,
      abs_of_nonpos (by linarith : zwegersErrorKernel z - 1 ≤ 0)]
    linarith

/-! ## The surviving `c₂` boundary correction -/

/-- Paper 2's surviving `c₂` boundary correction `E(-n√(Y/10)) - sgn(-n)`,
in the `(n,T)` coordinates of the manuscript's Section 6.  The subtracted sign
is the holomorphic sign part of Zwegers' completion, so this is exactly the
nonholomorphic remainder attached to the boundary vector `c₂`. -/
def paper2BoundaryCorrection (n Y : ℝ) : ℝ :=
  paper2BoundaryError n Y - Real.sign (-n)

@[simp] theorem paper2BoundaryCorrection_zero (Y : ℝ) :
    paper2BoundaryCorrection 0 Y = 0 := by
  simp [paper2BoundaryCorrection, paper2BoundaryError]

/-- For `Y>0` the paper's `sgn(-n)` is Zwegers' sign of the full kernel
argument `-n√(Y/10)`: the positive scale `√(Y/10)` does not move the sign. -/
theorem sign_neg_mul_sqrt (n : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Real.sign (-n * Real.sqrt (Y / 10)) = Real.sign (-n) := by
  have hs : 0 < Real.sqrt (Y / 10) := Real.sqrt_pos.2 (by positivity)
  rcases lt_trichotomy (-n) 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_neg_of_pos h hs)]
  · rw [h, zero_mul]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos h hs)]

/-- The paper's correction is Zwegers' `E(z)-sgn(z)` evaluated at
`z = -n√(Y/10)`. -/
theorem paper2BoundaryCorrection_eq_sub_sign (n : ℝ) {Y : ℝ} (hY : 0 < Y) :
    paper2BoundaryCorrection n Y
      = zwegersErrorKernel (-n * Real.sqrt (Y / 10))
          - Real.sign (-n * Real.sqrt (Y / 10)) := by
  rw [paper2BoundaryCorrection, paper2BoundaryError, sign_neg_mul_sqrt n hY]

/-- Quantitative Gaussian decay of the surviving `c₂` correction: for `n≠0`
and `Y>0`,
`|E(-n√(Y/10)) - sgn(-n)| ≤ e^{-πn²Y/10}/(π|n|√(Y/10))`. -/
theorem abs_paper2BoundaryCorrection_le {n Y : ℝ} (hn : n ≠ 0) (hY : 0 < Y) :
    |paper2BoundaryCorrection n Y|
      ≤ Real.exp (-Real.pi * n ^ 2 * Y / 10) /
          (Real.pi * (|n| * Real.sqrt (Y / 10))) := by
  have hs : 0 < Real.sqrt (Y / 10) := Real.sqrt_pos.2 (by positivity)
  have hz : -n * Real.sqrt (Y / 10) ≠ 0 := by
    intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact hn (by linarith)
    · exact (ne_of_gt hs) h'
  have hbound := abs_zwegersErrorKernel_sub_sign_le hz
  have hsq : (-n * Real.sqrt (Y / 10)) ^ 2 = n ^ 2 * Y / 10 := by
    rw [mul_pow, neg_sq, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Y / 10)]
    ring
  have habs : |(-n * Real.sqrt (Y / 10))| = |n| * Real.sqrt (Y / 10) := by
    rw [abs_mul, abs_neg, abs_of_pos hs]
  rw [hsq, habs,
    show -Real.pi * (n ^ 2 * Y / 10) = -Real.pi * n ^ 2 * Y / 10 by ring] at hbound
  rw [paper2BoundaryCorrection_eq_sub_sign n hY]
  exact hbound

end

end Ch10
end QseriesFormalization
