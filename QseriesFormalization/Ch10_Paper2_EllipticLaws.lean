import QseriesFormalization.Ch10_Paper2_ZwegersFourier

/-!
# Paper 2: the elliptic transformation laws of the completed indefinite theta

Zwegers' Corollary 2.9 parts (1), (2) and (3) — the *elliptic* transformation
properties of the completed indefinite theta `θ^{c₁,c₂}_{a,b}`, specialized to
this paper's data `A = diag(1,-5)`, `c₁ = (0,1)`, `c₂ = (-5,3)`.

These are the properties that describe how `θ` responds to moving the two
characteristics `a` and `b`, with `τ` held fixed.  They are elementary — no
Fourier analysis, no Poisson summation — but they are what collapses the
manuscript's five-term `S`-law to two displayed functions, so they are worth
having on their own.

The three laws are, writing `ν` for a point of the shifted lattice `a + ℤ²`:

* **(1)** `θ_{a+λ,b} = θ_{a,b}` for `λ ∈ ℤ²`, because `λ` merely reindexes the
  lattice;
* **(2)** `θ_{a,b+μ} = e^{2πiB(a,μ)}θ_{a,b}` for `μ` in the dual lattice
  `A⁻¹ℤ² = ℤ × (1/5)ℤ`, because `B(ν,μ)` then differs from `B(a,μ)` by an
  integer;
* **(3)** `θ_{-a,-b} = -θ_{a,b}`, because the kernel `ρ` is odd while `Q` is
  even and `B(-ν,-b) = B(ν,b)`.

The payoff is `paper2ThetaAB_eq_zero`: a *sufficient* criterion for `θ` to
vanish identically, obtained by composing the three laws rather than by a
direct pairing argument.  If `2a` is integral then (1) turns `-a` back into
`a`; if `2b` is dual-integral and `2B(a,b)` is an integer then (2) turns `-b`
back into `b` at no phase cost; and (3) then says the result is its own
negative.  This is the indefinite analogue of the classical odd-characteristic
vanishing `θ_{1/2,1/2} = 0`.

**Only the sufficient direction is claimed.**  The converse would have to rule
out cancellation between *distinct* orbits of `ν ↦ -ν`, and since `ρ` is itself
a difference `ρ^{c₁} - ρ^{c₂}` there is no general reason such accidental
cancellation cannot occur.  Sufficiency is all the manuscript's vanishing coset
term needs.

Nothing in this file formalizes Zwegers' completion theorem or his modular
`S`-transformation; those are Corollary 2.9(4),(5) and are not proved here.
-/

namespace QseriesFormalization
namespace Ch10

open scoped Real

noncomputable section

/-! ## The general-characteristic completed theta -/

/-- The lattice point `a + n` of the shifted lattice `a + ℤ²`.

Zwegers' Definition 2.1 sums over `a + ℤ²` rather than over `ℤ²`, so every
statement about moving the first characteristic is really a statement about
reindexing this map. -/
def paper2Shift (a : ℝ × ℝ) (n : ℤ × ℤ) : ℝ × ℝ := (a.1 + (n.1 : ℝ), a.2 + (n.2 : ℝ))

@[simp] theorem paper2Shift_fst (a : ℝ × ℝ) (n : ℤ × ℤ) :
    (paper2Shift a n).1 = a.1 + (n.1 : ℝ) := rfl

@[simp] theorem paper2Shift_snd (a : ℝ × ℝ) (n : ℤ × ℤ) :
    (paper2Shift a n).2 = a.2 + (n.2 : ℝ) := rfl

/-- The summand of Zwegers' completed indefinite theta at general
characteristics: `ρ(ν;τ)·e^{2πiQ(ν)τ + 2πiB(ν,b)}` with `ν = a + n`.

The kernel `paper2Rho` is the difference `ρ^{c₁} - ρ^{c₂}` of the two error
functions; it is what makes the sum converge even though `Q` is indefinite and
`|e^{2πiQ(ν)τ}| = e^{-2πyQ(ν)}` grows along the light cone. -/
def paper2ThetaABTerm (a b : ℝ × ℝ) (τ : ℂ) (n : ℤ × ℤ) : ℂ :=
  ((paper2Rho (paper2Shift a n) τ : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * τ *
        ((paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2 : ℝ) : ℂ) +
      2 * Real.pi * Complex.I *
        ((paper2B0 (paper2Shift a n).1 (paper2Shift a n).2 b.1 b.2 : ℝ) : ℂ))

/-- **Zwegers' completed indefinite theta at general characteristics**,
`θ^{c₁,c₂}_{a,b}(τ) = Σ_{ν ∈ a+ℤ²} ρ(ν;τ) e^{2πiQ(ν)τ + 2πiB(ν,b)}`,
specialized to `A = diag(1,-5)`, `c₁ = (0,1)`, `c₂ = (-5,3)`.

This is a definition of the convergent lattice sum.  It does not assert that
the sum is modular, nor that it completes any particular holomorphic object. -/
def paper2ThetaAB (a b : ℝ × ℝ) (τ : ℂ) : ℂ := ∑' n : ℤ × ℤ, paper2ThetaABTerm a b τ n

/-! ## Convergence

The modulus of a summand is `|ρ(ν)|·e^{-2πyQ(ν)}`, because the second
characteristic enters only through a character of modulus one.  That is exactly
the quantity bounded by the Gaussian majorant of the Fourier development, so
convergence is inherited rather than re-proved. -/

/-- The modulus of a summand: the second characteristic contributes a unit
character and drops out entirely. -/
theorem norm_paper2ThetaABTerm (a b : ℝ × ℝ) (τ : ℂ) (n : ℤ × ℤ) :
    ‖paper2ThetaABTerm a b τ n‖
      = |paper2Rho (paper2Shift a n) τ| *
          Real.exp (-(2 * Real.pi * τ.im *
            paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2)) := by
  rw [paper2ThetaABTerm, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring_nf

/-- The summand is dominated by an isotropic Gaussian on the shifted lattice.
This is the majorant proved for the Fourier development, transported to a
lattice point. -/
theorem norm_paper2ThetaABTerm_le (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) (n : ℤ × ℤ) :
    ‖paper2ThetaABTerm a b τ n‖
      ≤ 10 * Real.exp (-(2 * Real.pi * τ.im *
          (((a.1 + (n.1 : ℝ)) ^ 2 + (a.2 + (n.2 : ℝ)) ^ 2) / 100))) := by
  rw [norm_paper2ThetaABTerm]
  exact paper2_abs_rho_mul_exp_le hτ (paper2Shift a n)

/-- A one-dimensional shifted Gaussian over `ℤ` is summable, in the exact
exponent normalization the majorant produces. -/
theorem summable_paper2GaussianShift (s : ℝ) {y : ℝ} (hy : 0 < y) :
    Summable (fun m : ℤ => Real.exp (-(2 * Real.pi * y * ((s + (m : ℝ)) ^ 2 / 100)))) := by
  have hc : (0 : ℝ) < 2 * y / 100 := by positivity
  refine (summable_exp_neg_pi_mul_shift_sq s hc).congr fun m => ?_
  congr 1
  ring

/-- The general-characteristic theta series converges absolutely on the upper
half plane. -/
theorem summable_paper2ThetaABTerm (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ × ℤ => paper2ThetaABTerm a b τ n) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_paper2ThetaABTerm_le a b hτ n) ?_
  have hprod : Summable (fun n : ℤ × ℤ =>
      Real.exp (-(2 * Real.pi * τ.im * ((a.1 + (n.1 : ℝ)) ^ 2 / 100))) *
      Real.exp (-(2 * Real.pi * τ.im * ((a.2 + (n.2 : ℝ)) ^ 2 / 100)))) :=
    Summable.mul_of_nonneg (summable_paper2GaussianShift a.1 hτ)
      (summable_paper2GaussianShift a.2 hτ)
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine (hprod.mul_left 10).congr fun n => ?_
  rw [← Real.exp_add]
  congr 2
  ring

/-! ## Corollary 2.9(1): translating the first characteristic by the lattice -/

/-- **Zwegers Corollary 2.9(1).**  Moving the first characteristic by a lattice
vector does not change the theta function, because it only reindexes the sum
over `a + ℤ²`. -/
theorem paper2ThetaAB_add_int (a b : ℝ × ℝ) (l : ℤ × ℤ) (τ : ℂ) :
    paper2ThetaAB (a.1 + (l.1 : ℝ), a.2 + (l.2 : ℝ)) b τ = paper2ThetaAB a b τ := by
  rw [paper2ThetaAB, paper2ThetaAB, ← Equiv.tsum_eq (Equiv.addRight l)
    (fun n : ℤ × ℤ => paper2ThetaABTerm a b τ n)]
  refine tsum_congr fun n => ?_
  have h1 : paper2Shift (a.1 + (l.1 : ℝ), a.2 + (l.2 : ℝ)) n
      = paper2Shift a ((Equiv.addRight l) n) := by
    simp only [paper2Shift, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add, Int.cast_add,
      Prod.mk.injEq]
    constructor <;> ring
  rw [paper2ThetaABTerm, paper2ThetaABTerm, h1]

/-! ## Corollary 2.9(3): simultaneous negation of both characteristics -/

/-- **Zwegers Corollary 2.9(3).**  Negating both characteristics negates the
theta function.

The mechanism is that the kernel is odd while the exponent is even: `ρ(-ν) =
-ρ(ν)` because the error function is odd and `B(c,-ν) = -B(c,ν)`, whereas
`Q(-ν) = Q(ν)` and `B(-ν,-b) = B(ν,b)`.  So the summand at `-n` is the negative
of the summand at `n`, and `n ↦ -n` is a bijection of the index set. -/
theorem paper2ThetaAB_neg (a b : ℝ × ℝ) (τ : ℂ) :
    paper2ThetaAB (-a.1, -a.2) (-b.1, -b.2) τ = -paper2ThetaAB a b τ := by
  rw [paper2ThetaAB, paper2ThetaAB, ← Equiv.tsum_eq (Equiv.neg (ℤ × ℤ))
    (fun n : ℤ × ℤ => paper2ThetaABTerm a b τ n), ← tsum_neg]
  refine tsum_congr fun n => ?_
  have hshift : paper2Shift (-a.1, -a.2) n = -paper2Shift a ((Equiv.neg (ℤ × ℤ)) n) := by
    simp only [paper2Shift, Equiv.neg_apply, Prod.fst_neg, Prod.snd_neg, Int.cast_neg,
      Prod.neg_mk, Prod.mk.injEq]
    constructor <;> ring
  rw [paper2ThetaABTerm, paper2ThetaABTerm, hshift, paper2Rho_neg]
  have hQ : paper2Q0 (-paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).1
        (-paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).2
      = paper2Q0 (paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).1
        (paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).2 := by
    simp only [paper2Q0, Prod.fst_neg, Prod.snd_neg]
    ring
  have hB : paper2B0 (-paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).1
        (-paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).2 (-b.1) (-b.2)
      = paper2B0 (paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).1
        (paper2Shift a ((Equiv.neg (ℤ × ℤ)) n)).2 b.1 b.2 := by
    simp only [paper2B0, Prod.fst_neg, Prod.snd_neg]
    ring
  rw [hQ, hB]
  push_cast
  ring

/-! ## Corollary 2.9(2): translating the second characteristic by the dual lattice

The dual lattice of `ℤ²` for the pairing `B` is `A⁻¹ℤ² = ℤ × (1/5)ℤ`, since
`B((X,Y),(X',Y')) = XX' - 5YY'` and so `B(n, (m₁, m₂/5)) = n₁m₁ - n₂m₂ ∈ ℤ`. -/

/-- **Zwegers Corollary 2.9(2).**  Moving the second characteristic by a dual
lattice vector `μ = (m₁, m₂/5)` multiplies the theta function by the constant
`e^{2πiB(a,μ)}`.

The point is that `B(ν,μ) - B(a,μ) = n₁m₁ - n₂m₂` is an *integer* for every
lattice index `n`, so the extra character is the same on every summand and
factors out of the sum. -/
theorem paper2ThetaAB_add_dual (a b : ℝ × ℝ) (m : ℤ × ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    paper2ThetaAB a (b.1 + (m.1 : ℝ), b.2 + (m.2 : ℝ) / 5) τ
      = Complex.exp (2 * Real.pi * Complex.I *
          ((a.1 * (m.1 : ℝ) - a.2 * (m.2 : ℝ) : ℝ) : ℂ)) * paper2ThetaAB a b τ := by
  rw [paper2ThetaAB, paper2ThetaAB, ← (summable_paper2ThetaABTerm a b hτ).tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [paper2ThetaABTerm, paper2ThetaABTerm]
  have hB : paper2B0 (paper2Shift a n).1 (paper2Shift a n).2
        (b.1 + (m.1 : ℝ)) (b.2 + (m.2 : ℝ) / 5)
      = paper2B0 (paper2Shift a n).1 (paper2Shift a n).2 b.1 b.2
        + (a.1 * (m.1 : ℝ) - a.2 * (m.2 : ℝ))
        + ((n.1 * m.1 - n.2 * m.2 : ℤ) : ℝ) := by
    simp only [paper2B0, paper2Shift]
    push_cast
    ring
  rw [hB]
  push_cast
  rw [show (2 : ℂ) * Real.pi * Complex.I * τ *
        ((paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2 : ℝ) : ℂ) +
      2 * Real.pi * Complex.I *
        (((paper2B0 (paper2Shift a n).1 (paper2Shift a n).2 b.1 b.2 : ℝ) : ℂ)
          + ((a.1 : ℂ) * (m.1 : ℂ) - (a.2 : ℂ) * (m.2 : ℂ))
          + ((n.1 : ℂ) * (m.1 : ℂ) - (n.2 : ℂ) * (m.2 : ℂ)))
      = (2 * Real.pi * Complex.I *
          ((a.1 : ℂ) * (m.1 : ℂ) - (a.2 : ℂ) * (m.2 : ℂ)))
        + ((n.1 * m.1 - n.2 * m.2 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
        + (2 * Real.pi * Complex.I * τ *
            ((paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2 : ℝ) : ℂ) +
          2 * Real.pi * Complex.I *
            ((paper2B0 (paper2Shift a n).1 (paper2Shift a n).2 b.1 b.2 : ℝ) : ℂ)) by
    push_cast; ring]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring

/-! ## A sufficient vanishing criterion -/

/-- **A sufficient criterion for identical vanishing.**

If `2a` is an integer vector, `2b` lies in the dual lattice, and `2B(a,b)` is an
integer, then `θ^{c₁,c₂}_{a,b}` vanishes identically.

The proof composes the three elliptic laws rather than pairing terms directly.
Law (1) with `λ = -2a` moves `a` to `-a`; law (2) with `μ = -2b` moves `b` to
`-b`, and the phase it produces is `e^{2πi·2B(a,b)} = 1` precisely because
`2B(a,b)` is an integer; law (3) then identifies the result with `-θ_{a,b}`.
Hence `θ = -θ`.

Only this direction is claimed.  See the module docstring for why the converse
is not asserted. -/
theorem paper2ThetaAB_eq_zero (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im)
    (k : ℤ × ℤ) (hk1 : 2 * a.1 = (k.1 : ℝ)) (hk2 : 2 * a.2 = (k.2 : ℝ))
    (m : ℤ × ℤ) (hm1 : 2 * b.1 = (m.1 : ℝ)) (hm2 : 2 * b.2 = (m.2 : ℝ) / 5)
    (j : ℤ) (hj : 2 * paper2B0 a.1 a.2 b.1 b.2 = (j : ℝ)) :
    paper2ThetaAB a b τ = 0 := by
  -- Law (1) with `λ = -k` turns `a` into `-a`.
  have step1 : paper2ThetaAB (-a.1, -a.2) b τ = paper2ThetaAB a b τ := by
    have h := paper2ThetaAB_add_int a b (-k.1, -k.2) τ
    rw [show (a.1 + ((-k.1 : ℤ) : ℝ), a.2 + ((-k.2 : ℤ) : ℝ)) = (-a.1, -a.2) by
      push_cast
      simp only [Prod.mk.injEq]
      constructor <;> linarith] at h
    exact h
  -- Law (2) with `μ = -2b` turns `b` into `-b`, at a phase that is trivial
  -- because `2B(a,b)` is an integer.
  have step2 : paper2ThetaAB (-a.1, -a.2) (-b.1, -b.2) τ
      = paper2ThetaAB (-a.1, -a.2) b τ := by
    have h := paper2ThetaAB_add_dual (-a.1, -a.2) b (-m.1, -m.2) hτ
    rw [show (b.1 + ((-m.1 : ℤ) : ℝ), b.2 + ((-m.2 : ℤ) : ℝ) / 5) = (-b.1, -b.2) by
      push_cast
      simp only [Prod.mk.injEq]
      constructor <;> linarith] at h
    rw [h]
    have hphase : ((-a.1) * ((-m.1 : ℤ) : ℝ) - (-a.2) * ((-m.2 : ℤ) : ℝ) : ℝ) = (j : ℝ) := by
      push_cast
      rw [← hj, paper2B0]
      linear_combination (-a.1) * hm1 + (5 * a.2) * hm2
    rw [hphase]
    rw [show (2 : ℂ) * Real.pi * Complex.I * ((j : ℝ) : ℂ)
        = (j : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I, one_mul]
  -- Law (3) identifies the doubly negated theta with the negative of the original.
  have step3 := paper2ThetaAB_neg a b τ
  have hself : paper2ThetaAB a b τ = -paper2ThetaAB a b τ := by
    rw [← step3, step2, step1]
  have htwo : (2 : ℂ) * paper2ThetaAB a b τ = 0 := by linear_combination hself
  simpa using htwo

/-! ## The dual-lattice cosets

Corollary 2.9(5) sums over `A⁻¹ℤ² / ℤ²`.  For `A = diag(1,-5)` the dual lattice
is `A⁻¹ℤ² = ℤ × (1/5)ℤ`, so the quotient has order five with representatives
`(0, m/5)` for `m = 0,…,4`.  The reduction below is what makes "sum over the
quotient" a well-defined five-term sum: it is law (1) applied to the integral
part of the dual vector. -/

/-- Reducing a dual-lattice vector modulo `ℤ²` does not change the theta.

For `μ = (m₁, m₂/5)`, the difference `μ − (0, (m₂ mod 5)/5) = (m₁, m₂ / 5)` is an
integer vector, so law (1) applies.  This is what lets the sum over
`A⁻¹ℤ²/ℤ²` be written as the five-term sum over `m = 0,…,4`. -/
theorem paper2ThetaAB_dual_coset_reduce (b : ℝ × ℝ) (m : ℤ × ℤ) (τ : ℂ) :
    paper2ThetaAB (b.1 + (m.1 : ℝ), b.2 + (m.2 : ℝ) / 5) b τ
      = paper2ThetaAB (b.1, b.2 + ((m.2 % 5 : ℤ) : ℝ) / 5) b τ := by
  have hdiv : (m.2 : ℝ) / 5 = ((m.2 % 5 : ℤ) : ℝ) / 5 + ((m.2 / 5 : ℤ) : ℝ) := by
    have h := Int.emod_add_mul_ediv m.2 5
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    linarith
  have hshift := paper2ThetaAB_add_int (b.1, b.2 + ((m.2 % 5 : ℤ) : ℝ) / 5) b (m.1, m.2 / 5) τ
  rw [show ((b.1, b.2 + ((m.2 % 5 : ℤ) : ℝ) / 5).1 + ((m.1 : ℤ) : ℝ),
        (b.1, b.2 + ((m.2 % 5 : ℤ) : ℝ) / 5).2 + (((m.2 / 5 : ℤ)) : ℝ))
      = (b.1 + (m.1 : ℝ), b.2 + (m.2 : ℝ) / 5) by
    simp only [Prod.mk.injEq]
    refine ⟨by norm_num, ?_⟩
    rw [hdiv]; ring] at hshift
  exact hshift


/-! ## Bridge to the manuscript's object

`paper2LatticeTheta` is the Definition 2.1 object at the manuscript's specific
characteristics, assembled in this repository out of three separately-managed
pieces: the two error-kernel corrections and the sign half.  The general
`paper2ThetaAB` above is the same object with the characteristics left free.
Identifying them is what will carry any general-characteristic transformation law
back to the manuscript's `F̂`.

The computation is a cancellation among the three pieces.  With `Eⱼ` the two
error kernels and `sgnⱼ` the corresponding signs,

    (E₂ − sgn₂) − (E₁ − sgn₁) + (sgn₂ − sgn₁) = E₂ − E₁ = −ρ,

so the assembled summand is `−ρ(ν)` times the common phase and weight.  The
minus sign is real and is why the bridge below carries one: this repository's
`paper2Rho` is `ρ^{c₁} − ρ^{c₂}`, while the assembled lattice object is built
with the opposite cone order. -/

/-- **The manuscript's completed theta is the general-characteristic theta.**

`paper2LatticeTheta τ = −½e^{−3πi/5}·θ_{a,b}(τ)` at `a = (1/2,1/10)`,
`b = (1/2,−1/10)`.

The sign records the cone order: `paper2Rho = ρ^{c₁} − ρ^{c₂}`, whereas the
assembled object uses `ρ^{c₂} − ρ^{c₁}`. -/
theorem paper2LatticeTheta_eq_thetaAB (τ : ℂ) :
    paper2LatticeTheta τ
      = -((1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5)) *
          paper2ThetaAB (1 / 2, 1 / 10) (1 / 2, -(1 / 10)) τ := by
  have hterm : ∀ p : ℤ × ℤ,
      paper2LatticeC2Term p τ - paper2LatticeC1Term p τ + paper2LatticeSgnTerm p τ
        = -paper2ThetaABTerm (1 / 2, 1 / 10) (1 / 2, -(1 / 10)) τ p := by
    intro p
    have hQ : paper2Q0 ((1 : ℝ) / 2 + (p.1 : ℝ)) ((1 : ℝ) / 10 + (p.2 : ℝ))
        = paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) := by
      simp only [paper2Q0]; ring
    have hB : paper2B0 ((1 : ℝ) / 2 + (p.1 : ℝ)) ((1 : ℝ) / 10 + (p.2 : ℝ))
          (1 / 2) (-(1 / 10))
        = paper2B0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) (1 / 2) (-(1 / 10)) := by
      simp only [paper2B0]; ring
    have hB1 : paper2B0 0 1 ((1 : ℝ) / 2 + (p.1 : ℝ)) ((1 : ℝ) / 10 + (p.2 : ℝ))
        = paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) := by
      simp only [paper2B0]; ring
    have hB2 : paper2B0 (-5) 3 ((1 : ℝ) / 2 + (p.1 : ℝ)) ((1 : ℝ) / 10 + (p.2 : ℝ))
        = paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) := by
      simp only [paper2B0]; ring
    have hphase : paper2CharPhase p * paper2LatticeNome p τ
        = Complex.exp (2 * Real.pi * Complex.I * τ *
              ((paper2Q0 ((1 : ℝ) / 2 + (p.1 : ℝ)) ((1 : ℝ) / 10 + (p.2 : ℝ)) : ℝ) : ℂ) +
            2 * Real.pi * Complex.I *
              ((paper2B0 ((1 : ℝ) / 2 + (p.1 : ℝ)) ((1 : ℝ) / 10 + (p.2 : ℝ))
                (1 / 2) (-(1 / 10)) : ℝ) : ℂ)) := by
      rw [paper2CharPhase, paper2LatticeNome, ← Complex.exp_add, hQ, hB]
      ring_nf
    rw [paper2ThetaABTerm, paper2Shift, paper2Rho, paper2LatticeC2Term,
      paper2LatticeC1Term, paper2LatticeSgnTerm, paper2SignDiff,
      paper2C2KernelArg, paper2C1KernelArg]
    simp only [hphase, hB1, hB2, paper2Q0]
    push_cast
    ring
  rw [paper2LatticeTheta, paper2ThetaAB, tsum_congr hterm, tsum_neg]
  ring

/-! ## Corollary 2.9(4): the translation `τ ↦ τ + 1`

Unlike the `S`-law this one is elementary, because `ρ` depends on `τ` only
through `Im τ`, which translation does not move.  Everything therefore reduces
to a single arithmetic fact about the lattice: `Q(n) − B(n,ρ_A) ∈ ℤ` for every
integer vector `n`, where `ρ_A = (1/2, 1/10)` is the characteristic vector of
`A = diag(1,-5)`.  That is the indefinite analogue of "`Q` is an integral form
modulo its diagonal", and it is what lets `e^{2πiQ(n)}` be absorbed into the
second characteristic. -/

/-- The characteristic vector of `A = diag(1,-5)`: the unique class mod `ℤ²` with
`B(n,ρ_A) ≡ Q(n) (mod 1)` for every integer vector `n`.

Concretely `B(n,ρ_A) = (n₁ − n₂)/2`, and `Q(n) − (n₁ − n₂)/2` is an integer
because `n₁² − n₁` and `5n₂² − n₂` are both even. -/
def paper2CharVec : ℝ × ℝ := (1 / 2, 1 / 10)

/-- `Q(n) − B(n,ρ_A)` is an integer on the lattice.  The witness is
`(n₁² − n₁)/2 − (5n₂² − n₂)/2`, and both halves are integers by parity. -/
theorem paper2_Q0_sub_B0_charVec_int (n : ℤ × ℤ) :
    ∃ k : ℤ, paper2Q0 (n.1 : ℝ) (n.2 : ℝ)
      - paper2B0 (n.1 : ℝ) (n.2 : ℝ) paper2CharVec.1 paper2CharVec.2 = (k : ℝ) := by
  obtain ⟨p, hp⟩ : ∃ p : ℤ, n.1 ^ 2 - n.1 = 2 * p := by
    rcases Int.even_or_odd n.1 with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨2 * m ^ 2 - m, by rw [hm]; ring⟩
    · exact ⟨2 * m ^ 2 + m, by rw [hm]; ring⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, 5 * n.2 ^ 2 - n.2 = 2 * q := by
    rcases Int.even_or_odd n.2 with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨10 * m ^ 2 - m, by rw [hm]; ring⟩
    · exact ⟨10 * m ^ 2 + 9 * m + 2, by rw [hm]; ring⟩
  refine ⟨p - q, ?_⟩
  have hp' := congrArg (fun z : ℤ => (z : ℝ)) hp
  have hq' := congrArg (fun z : ℤ => (z : ℝ)) hq
  simp only [paper2Q0, paper2B0, paper2CharVec]
  push_cast at hp' hq' ⊢
  linarith

/-- **Zwegers Corollary 2.9(4).**  Translating `τ` by one multiplies the theta by
an explicit constant and shifts the second characteristic by `a + ρ_A`.

`ρ` is unchanged because it sees only `Im τ`.  The extra factor `e^{2πiQ(ν)}`
coming from `Q(ν)(τ+1)` is absorbed into the second characteristic using the
integrality of `Q(n) − B(n,ρ_A)`; the constant collects the terms that do not
depend on the summation index. -/
theorem paper2ThetaAB_add_one (a b : ℝ × ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    paper2ThetaAB a b (τ + 1)
      = Complex.exp (-2 * Real.pi * Complex.I *
            ((paper2Q0 a.1 a.2 + paper2B0 a.1 a.2 paper2CharVec.1 paper2CharVec.2 : ℝ) : ℂ)) *
          paper2ThetaAB a (b.1 + a.1 + paper2CharVec.1, b.2 + a.2 + paper2CharVec.2) τ := by
  have him : (τ + 1).im = τ.im := by simp
  rw [paper2ThetaAB, paper2ThetaAB,
    ← (summable_paper2ThetaABTerm a
        (b.1 + a.1 + paper2CharVec.1, b.2 + a.2 + paper2CharVec.2) hτ).tsum_mul_left]
  refine tsum_congr fun n => ?_
  obtain ⟨k, hk⟩ := paper2_Q0_sub_B0_charVec_int n
  rw [paper2ThetaABTerm, paper2ThetaABTerm]
  have hrho : paper2Rho (paper2Shift a n) (τ + 1) = paper2Rho (paper2Shift a n) τ := by
    simp only [paper2Rho, him]
  have hQ : paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2
      = paper2Q0 a.1 a.2 + paper2B0 a.1 a.2 (n.1 : ℝ) (n.2 : ℝ)
        + paper2Q0 (n.1 : ℝ) (n.2 : ℝ) := by
    simp only [paper2Q0, paper2B0, paper2Shift]
    ring
  have hB : paper2B0 (paper2Shift a n).1 (paper2Shift a n).2
        (b.1 + a.1 + paper2CharVec.1) (b.2 + a.2 + paper2CharVec.2)
      = paper2B0 (paper2Shift a n).1 (paper2Shift a n).2 b.1 b.2
        + paper2Q0 a.1 a.2 + paper2B0 a.1 a.2 (n.1 : ℝ) (n.2 : ℝ)
        + paper2Q0 (n.1 : ℝ) (n.2 : ℝ)
        + (paper2Q0 a.1 a.2 + paper2B0 a.1 a.2 paper2CharVec.1 paper2CharVec.2)
        - (k : ℝ) := by
    simp only [paper2Q0, paper2B0, paper2Shift, paper2CharVec] at hk ⊢
    linarith [hk]
  rw [hrho]
  have hQc := congrArg (fun r : ℝ => (r : ℂ)) hQ
  have hBc := congrArg (fun r : ℝ => (r : ℂ)) hB
  simp only at hQc hBc
  have hE : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ + 1) *
        ((paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2 : ℝ) : ℂ) +
      2 * (Real.pi : ℂ) * Complex.I *
        ((paper2B0 (paper2Shift a n).1 (paper2Shift a n).2 b.1 b.2 : ℝ) : ℂ))
      = Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          ((paper2Q0 a.1 a.2 + paper2B0 a.1 a.2 paper2CharVec.1 paper2CharVec.2 : ℝ) : ℂ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ *
            ((paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2 : ℝ) : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I *
            ((paper2B0 (paper2Shift a n).1 (paper2Shift a n).2
              (b.1 + a.1 + paper2CharVec.1) (b.2 + a.2 + paper2CharVec.2) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨k, ?_⟩
    push_cast at hQc hBc ⊢
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hQc
      - (2 * (Real.pi : ℂ) * Complex.I) * hBc
  rw [hE]
  ring


/-! ## Reflecting the first characteristic, and the collapse of the printed `S`-law

Combining (2) and (3) gives a reflection law for the *first* characteristic
alone, at the cost of an explicit character.  Together with (1) this is what
makes the manuscript's five printed theta functions reduce to two displayed
ones — a reduction needing no Fourier analysis whatsoever, only the elliptic
laws above.

The lemmas here are stated in components rather than pairs, because the
manuscript's characteristics are explicit rationals and component form keeps the
`norm_num` arithmetic free of projection noise. -/

/-- **Reflection of the first characteristic.**  When `2d` lies in the dual
lattice, `θ_{-c,-d} = -e^{2πiB(c,2d)}θ_{c,-d}`.

Law (2) moves the second characteristic from `-d` to `d` at the character
`e^{-2πiB(c,2d)}`, and law (3) identifies `θ_{-c,d}` with `-θ_{c,-d}`; the two
combine after cancelling the character against its inverse. -/
theorem paper2ThetaAB_neg_fst (c1 c2 d1 d2 : ℝ) (m : ℤ × ℤ)
    (hm1 : 2 * d1 = (m.1 : ℝ)) (hm2 : 2 * d2 = (m.2 : ℝ) / 5) {τ : ℂ} (hτ : 0 < τ.im) :
    paper2ThetaAB (-c1, -c2) (-d1, -d2) τ
      = -(Complex.exp (2 * Real.pi * Complex.I *
            ((paper2B0 c1 c2 (2 * d1) (2 * d2) : ℝ) : ℂ))) *
          paper2ThetaAB (c1, c2) (-d1, -d2) τ := by
  have h2 := paper2ThetaAB_add_dual (-c1, -c2) (-d1, -d2) m hτ
  rw [show ((-d1) + (m.1 : ℝ), (-d2) + (m.2 : ℝ) / 5) = (d1, d2) by
    simp only [Prod.mk.injEq]
    constructor <;> linarith] at h2
  have h3 := paper2ThetaAB_neg (c1, c2) (-d1, -d2) τ
  simp only [neg_neg] at h3
  rw [h3] at h2
  have hphase : (((-c1, -c2).1 * (m.1 : ℝ) - (-c1, -c2).2 * (m.2 : ℝ) : ℝ))
      = -(paper2B0 c1 c2 (2 * d1) (2 * d2)) := by
    simp only [paper2B0]
    linear_combination c1 * hm1 + (-5 * c2) * hm2
  rw [hphase] at h2
  have hcancel : Complex.exp (2 * Real.pi * Complex.I *
        ((paper2B0 c1 c2 (2 * d1) (2 * d2) : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I *
        ((-(paper2B0 c1 c2 (2 * d1) (2 * d2)) : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add, show (2 * Real.pi * Complex.I *
        ((paper2B0 c1 c2 (2 * d1) (2 * d2) : ℝ) : ℂ) +
        2 * Real.pi * Complex.I *
        ((-(paper2B0 c1 c2 (2 * d1) (2 * d2)) : ℝ) : ℂ)) = 0 by push_cast; ring,
      Complex.exp_zero]
  calc paper2ThetaAB (-c1, -c2) (-d1, -d2) τ
      = 1 * paper2ThetaAB (-c1, -c2) (-d1, -d2) τ := (one_mul _).symm
    _ = (Complex.exp (2 * Real.pi * Complex.I *
            ((paper2B0 c1 c2 (2 * d1) (2 * d2) : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((-(paper2B0 c1 c2 (2 * d1) (2 * d2)) : ℝ) : ℂ))) *
          paper2ThetaAB (-c1, -c2) (-d1, -d2) τ := by rw [hcancel]
    _ = Complex.exp (2 * Real.pi * Complex.I *
            ((paper2B0 c1 c2 (2 * d1) (2 * d2) : ℝ) : ℂ)) *
          (Complex.exp (2 * Real.pi * Complex.I *
            ((-(paper2B0 c1 c2 (2 * d1) (2 * d2)) : ℝ) : ℂ)) *
            paper2ThetaAB (-c1, -c2) (-d1, -d2) τ) := by ring
    _ = Complex.exp (2 * Real.pi * Complex.I *
            ((paper2B0 c1 c2 (2 * d1) (2 * d2) : ℝ) : ℂ)) *
          (-paper2ThetaAB (c1, c2) (-d1, -d2) τ) := by rw [← h2]
    _ = -(Complex.exp (2 * Real.pi * Complex.I *
            ((paper2B0 c1 c2 (2 * d1) (2 * d2) : ℝ) : ℂ))) *
          paper2ThetaAB (c1, c2) (-d1, -d2) τ := by ring

/-- `-e^{w} = e^{πi + w}`, the form in which the reflection character's minus
sign is absorbed into an exponential. -/
theorem paper2_neg_exp_eq (w : ℂ) :
    -(Complex.exp w) = Complex.exp ((Real.pi : ℂ) * Complex.I + w) := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- **The `m = 0` term of the printed `S`-law is `e^{-πi/5}` times the `m = 1`
term.**

`-(1/2,1/10) + (1,0) = (1/2,-1/10)` identifies the first characteristics up to
the lattice, and the reflection character is `e^{2πi·(2/5)}`, so the constant is
`-e^{4πi/5} = e^{-πi/5}`. -/
theorem paper2ThetaAB_coset_zero {τ : ℂ} (hτ : 0 < τ.im) :
    paper2ThetaAB (1 / 2, -(1 / 10)) (-(1 / 2), -(1 / 10)) τ
      = Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5) *
          paper2ThetaAB (1 / 2, 1 / 10) (-(1 / 2), -(1 / 10)) τ := by
  have hrefl := paper2ThetaAB_neg_fst (1 / 2) (1 / 10) (1 / 2) (1 / 10) (1, 1)
    (by norm_num) (by norm_num) hτ
  have hshift := paper2ThetaAB_add_int ((-(1 / 2) : ℝ), (-(1 / 10) : ℝ))
    ((-(1 / 2) : ℝ), (-(1 / 10) : ℝ)) (1, 0) τ
  norm_num at hrefl hshift
  rw [hshift, hrefl, paper2B0]
  norm_num
  have hc : -(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (2 / 5)))
      = Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5) := by
    rw [paper2_neg_exp_eq, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨1, by push_cast; ring⟩
  rw [← hc]
  ring

/-- **The `m = 2` term of the printed `S`-law is `e^{3πi/5}` times the `m = 4`
term.**

`-(1/2,7/10) + (1,1) = (1/2,3/10)`, the reflection character is
`e^{2πi·(-1/5)}`, and `-e^{-2πi/5} = e^{3πi/5}`. -/
theorem paper2ThetaAB_coset_two {τ : ℂ} (hτ : 0 < τ.im) :
    paper2ThetaAB (1 / 2, 3 / 10) (-(1 / 2), -(1 / 10)) τ
      = Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5) *
          paper2ThetaAB (1 / 2, 7 / 10) (-(1 / 2), -(1 / 10)) τ := by
  have hrefl := paper2ThetaAB_neg_fst (1 / 2) (7 / 10) (1 / 2) (1 / 10) (1, 1)
    (by norm_num) (by norm_num) hτ
  have hshift := paper2ThetaAB_add_int ((-(1 / 2) : ℝ), (-(7 / 10) : ℝ))
    ((-(1 / 2) : ℝ), (-(1 / 10) : ℝ)) (1, 1) τ
  norm_num at hrefl hshift
  rw [hshift, hrefl, paper2B0]
  norm_num
  have hc : -(Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (1 / 5))))
      = Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 5) := by
    rw [paper2_neg_exp_eq, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨0, by push_cast; ring⟩
  rw [← hc]
  ring


/-! ## The manuscript's identically-zero coset term

Paper 2's `S`-transformation is printed as a sum of five theta functions
`θ^{c₂,c₁}_{b+(0,m/5),-a}` for `m = 0,…,4`, with `a = (1/2,1/10)` and
`b = (1/2,-1/10)`.  At `m = 3` the first characteristic is
`b + (0,3/5) = (1/2,1/2)`, which is half-integral, and the second is
`-a = (-1/2,-1/10)`, whose double `(-1,-1/5)` lies in the dual lattice; the
pairing `2B((1/2,1/2),(-1/2,-1/10)) = 2(-1/4 + 1/4) = 0` is an integer.  All
three hypotheses of the criterion hold, so that term is identically zero and
the printed five-term sum really has four terms.

The manuscript does not remark on this. -/

/-- The `m = 3` term of the manuscript's printed five-term `S`-law vanishes
identically: its characteristics satisfy the odd-characteristic criterion. -/
theorem paper2ThetaAB_half_half_eq_zero {τ : ℂ} (hτ : 0 < τ.im) :
    paper2ThetaAB (1 / 2, 1 / 2) (-(1 / 2), -(1 / 10)) τ = 0 := by
  refine paper2ThetaAB_eq_zero _ _ hτ (1, 1) (by norm_num) (by norm_num)
    (-1, -1) (by norm_num) (by norm_num) 0 ?_
  rw [paper2B0]
  norm_num


end

end Ch10
end QseriesFormalization
