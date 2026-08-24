import Mathlib

/-!
# A complete shifted indefinite-theta completion over Q(sqrt(5))

This Mathlib-only Challenge states the coefficientwise row factorization and
the analytic headline results of Paper 2.  The definitions are duplicated in
the Solution-side public module and checked byte-for-byte for drift.
-/

namespace PalomarQseriesRowFactorization

noncomputable section

/-! ## BEGIN PUBLIC STATEMENT DEFINITIONS -/

/-! ### The coefficientwise row model -/

def Q (k r : Int) : Int :=
  4 * k ^ 2 + 2 * k + r ^ 2 + (6 * k + 1) * r

def triZ (r : Int) : Int := r * (r + 1) / 2

def E (k r : Int) : Int :=
  2 * k ^ 2 + k + 3 * k * r + triZ r

def negOnePowInt (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

def ACoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N)).sum
    (fun p => -negOnePowInt (↑p.2))

def DCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N)).sum
    (fun p => negOnePowInt (-(↑p.2 + 1)))

def BCoeff (N : Nat) : Int := DCoeff N + ACoeff N

abbrev Hq (k r : Int) : Int := Q k r

def mkSign (n : Int) : Int := (Int.negOnePow n : Int)

def thetaUBound (a : Int) : Int := |a| + 3

def thetaVBound (a : Int) : Int := |a| + 4

def thetaUCoeff (a : Int) : Int :=
  ∑ u ∈ Finset.Icc (-thetaUBound a) (thetaUBound a),
    if 5 * u ^ 2 - 3 * u = a then mkSign u else 0

def thetaVCoeff (a : Int) : Int :=
  ∑ v ∈ Finset.Icc (-thetaVBound a) (thetaVBound a),
    if 5 * v ^ 2 - 7 * v = a then mkSign v else 0

def QoutCoeff (a : Int) : Int :=
  ∑ i ∈ Finset.Icc 0 (a + 2), thetaUCoeff i * thetaVCoeff (a - i)

def rowDisc (k m : Int) : Int :=
  4 * m - (16 * k ^ 2 + 8 * k) + (6 * k + 1) ^ 2

def rowRBound (k m : Int) : Int :=
  |rowDisc k m| + |6 * k + 1| + 2

def rowFiber (k m : Int) : Finset Int :=
  (Finset.Icc (-rowRBound k m) (rowRBound k m)).filter
    (fun r => Hq k r = m)

def mixedSide (k r : Int) : Prop :=
  (0 ≤ k ∧ r ≤ -1) ∨ (k ≤ -1 ∧ 0 ≤ r)

def coneSide (k r : Int) : Prop :=
  (0 ≤ k ∧ 0 ≤ r) ∨ (k ≤ -1 ∧ r ≤ -1)

instance (k r : Int) : Decidable (mixedSide k r) := by
  unfold mixedSide
  infer_instance

instance (k r : Int) : Decidable (coneSide k r) := by
  unfold coneSide
  infer_instance

def rowMixedCoeff (k m : Int) : Int :=
  ((rowFiber k m).filter (mixedSide k)).sum mkSign

def rowConeCoeff (k m : Int) : Int :=
  ((rowFiber k m).filter (coneSide k)).sum mkSign

def rowMin (k : Int) : Int :=
  if 0 ≤ k then 4 * k ^ 2 + 2 * k else 4 * k ^ 2 - 4 * k

def rowEpsilon (k : Int) : Int := if 0 ≤ k then 1 else -1

def coneSignedCoeff (k m : Int) : Int :=
  -rowEpsilon k * rowConeCoeff k m

def mkKBound (T : Int) : Int := |T| + 3

def mkRowCoeff (k T : Int) : Int :=
  ∑ a ∈ Finset.Icc (-2) (T - rowMin k),
    QoutCoeff a * rowMixedCoeff k (T - a)

def MKcoeff (T : Int) : Int :=
  ∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
    rowEpsilon k * mkRowCoeff k T

def coneKBound (m : Int) : Int := |m| + 1

def coneDiffH (m : Int) : Int :=
  ∑ k ∈ Finset.Icc (-coneKBound m) (coneKBound m),
    coneSignedCoeff k m

/-! ### The completed indefinite theta -/

def paper2Q0 (X Y : ℝ) : ℝ := (X ^ 2 - 5 * Y ^ 2) / 2

def paper2B0 (X Y X' Y' : ℝ) : ℝ := X * X' - 5 * (Y * Y')

def zwegersGaussian (u : ℝ) : ℝ := Real.exp (-Real.pi * u ^ 2)

def zwegersErrorKernel (z : ℝ) : ℝ :=
  2 * ∫ u : ℝ in (0 : ℝ)..z, zwegersGaussian u

def paper2Rho (a : ℝ × ℝ) (τ : ℂ) : ℝ :=
  zwegersErrorKernel
      (paper2B0 0 1 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 0 1)) -
    zwegersErrorKernel
      (paper2B0 (-5) 3 a.1 a.2 * Real.sqrt τ.im / Real.sqrt (-paper2Q0 (-5) 3))

def paper2FourierIntegrand (τ : ℂ) (α a : ℝ × ℝ) : ℂ :=
  ((paper2Rho a τ : ℝ) : ℂ) *
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((paper2Q0 a.1 a.2 : ℝ) : ℂ) * τ +
       2 * (Real.pi : ℂ) * Complex.I *
         ((paper2B0 a.1 a.2 α.1 α.2 : ℝ) : ℂ))

def paper2H (τ : ℂ) (α : ℝ × ℝ) : ℂ :=
  ∫ a : ℝ × ℝ, paper2FourierIntegrand τ α a

def paper2Shift (a : ℝ × ℝ) (n : ℤ × ℤ) : ℝ × ℝ :=
  (a.1 + (n.1 : ℝ), a.2 + (n.2 : ℝ))

def paper2ThetaABTerm (a b : ℝ × ℝ) (τ : ℂ) (n : ℤ × ℤ) : ℂ :=
  ((paper2Rho (paper2Shift a n) τ : ℝ) : ℂ) *
    Complex.exp
      (2 * Real.pi * Complex.I * τ *
          ((paper2Q0 (paper2Shift a n).1 (paper2Shift a n).2 : ℝ) : ℂ) +
       2 * Real.pi * Complex.I *
          ((paper2B0 (paper2Shift a n).1 (paper2Shift a n).2 b.1 b.2 : ℝ) : ℂ))

def paper2ThetaAB (a b : ℝ × ℝ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ × ℤ, paper2ThetaABTerm a b τ n

/-- The manuscript's cone order `(c₂,c₁)`. -/
def paper2ThetaAB_c2c1 (a b : ℝ × ℝ) (τ : ℂ) : ℂ :=
  -paper2ThetaAB a b τ

/-- The normalized completed theta called `F-hat` in the paper. -/
def paper2CompletedTheta (τ : ℂ) : ℂ :=
  -((1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5)) *
    paper2ThetaAB (1 / 2, 1 / 10) (1 / 2, -(1 / 10)) τ

/-! ### Holomorphic sign part and boundary correction -/

def paper2BSeries (q : ℂ) : ℂ :=
  ∑' N : ℕ, (BCoeff N : ℂ) * q ^ N

def paper2Nome (τ : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ)

def paper2NomeTenth (τ : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ / 10)

def paper2C2KernelArg (p : ℤ × ℤ) (Y : ℝ) : ℝ :=
  paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * Real.sqrt Y /
    Real.sqrt (-paper2Q0 (-5) 3)

def paper2C1KernelArg (p : ℤ × ℤ) (Y : ℝ) : ℝ :=
  paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) * Real.sqrt Y /
    Real.sqrt (-paper2Q0 0 1)

def paper2CharPhase (p : ℤ × ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    (paper2B0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)
      (1 / 2) (-(1 / 10)) : ℝ))

def paper2LatticeNome (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * τ *
    (paper2Q0 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10) : ℝ))

def paper2LatticeC2Term (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  ((zwegersErrorKernel (paper2C2KernelArg p τ.im) -
      Real.sign (paper2B0 (-5) 3 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) : ℝ) : ℂ) *
    (paper2CharPhase p * paper2LatticeNome p τ)

def paper2LatticeC1Term (p : ℤ × ℤ) (τ : ℂ) : ℂ :=
  ((zwegersErrorKernel (paper2C1KernelArg p τ.im) -
      Real.sign (paper2B0 0 1 ((p.1 : ℝ) + 1 / 2) ((p.2 : ℝ) + 1 / 10)) : ℝ) : ℂ) *
    (paper2CharPhase p * paper2LatticeNome p τ)

def paper2LatticeCorrection (τ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.exp (-3 * Real.pi * Complex.I / 5) *
    ∑' p : ℤ × ℤ, (paper2LatticeC2Term p τ - paper2LatticeC1Term p τ)

/-! ### Differential components -/

def paper2ThetaResidue (j T : ℤ) : Prop :=
  T % 4 = (3 * j + 2) % 4

def paper2GResidue (j n : ℤ) : Prop :=
  n % 20 = (5 * j + 4) % 20

instance (j T : ℤ) : Decidable (paper2ThetaResidue j T) := by
  unfold paper2ThetaResidue
  infer_instance

instance (j n : ℤ) : Decidable (paper2GResidue j n) := by
  unfold paper2GResidue
  infer_instance

def paper2ThetaTerm (j T : ℤ) (τ : ℂ) : ℂ :=
  if paper2ThetaResidue j T then jacobiTheta₂_term T 0 (τ / 4) else 0

def paper2GTerm (j n : ℤ) (τ : ℂ) : ℂ :=
  if paper2GResidue j n then (n : ℂ) * jacobiTheta₂_term n 0 (τ / 20) else 0

def paper2ThetaComponent (j : ℤ) (τ : ℂ) : ℂ :=
  ∑' T : ℤ, paper2ThetaTerm j T τ

def paper2GComponent (j : ℤ) (τ : ℂ) : ℂ :=
  ∑' n : ℤ, paper2GTerm j n τ

/-- The Wirtinger derivative with respect to the conjugate variable. -/
def dbar (F : ℂ → ℂ) (τ : ℂ) : ℂ :=
  (fderiv ℝ F τ 1 + Complex.I * fderiv ℝ F τ Complex.I) / 2

def xi1 (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  2 * Complex.I * (τ.im : ℂ) * (starRingEnd ℂ) (dbar f τ)

def Delta1 (f : ℂ → ℂ) (τ : ℂ) : ℂ :=
  -xi1 (xi1 f) τ

/-! ## END PUBLIC STATEMENT DEFINITIONS -/

/-! ## Registered theorems -/

/-- Finite coefficientwise separation of the shifted row model. -/
theorem mk_factorization (T : Int) :
    MKcoeff T =
      ∑ a ∈ Finset.Icc (-2) T,
        QoutCoeff a * coneDiffH (T - a) := by
  sorry

/-- Even row levels recover the norm-theta coefficient. -/
theorem coneDiffH_two_mul (N : Nat) :
    coneDiffH (2 * (N : Int)) = BCoeff N := by
  sorry

/-- Odd row levels vanish. -/
theorem coneDiffH_odd {m : Int} (hm : ¬ 2 ∣ m) :
    coneDiffH m = 0 := by
  sorry

/-- The completed theta has holomorphic sign part
`q^(1/10) B(q)` and the explicit two-boundary correction. -/
theorem exact_completion_bridge {τ : ℂ} (hτ : 0 < τ.im) :
    paper2CompletedTheta τ =
      paper2NomeTenth τ * paper2BSeries (paper2Nome τ) +
        paper2LatticeCorrection τ := by
  sorry

/-- The defining lattice series of the normalized completed theta converges
absolutely throughout the upper half-plane. -/
theorem completedTheta_summable {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n : ℤ × ℤ =>
      paper2ThetaABTerm (1 / 2, 1 / 10) (1 / 2, -(1 / 10)) τ n) := by
  sorry

/-- Zwegers' Lemma 2.8, specialized to the quadratic form and cone vectors of
Paper 2, including the exact square-root branch and exponential sign. -/
theorem zwegers_lemma28 {τ : ℂ} (hτ : 0 < τ.im) (α : ℝ × ℝ) :
    paper2H τ α =
      (((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * (Complex.I / (-Complex.I * τ))) *
        (paper2Rho α (-1 / τ) : ℂ) *
          Complex.exp
            (-(2 * (Real.pi : ℂ) * Complex.I *
              ((paper2Q0 α.1 α.2 : ℝ) : ℂ) / τ)) := by
  sorry

/-- The weight-one translation law of the normalized completed theta. -/
theorem completedTheta_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    paper2CompletedTheta (τ + 1) =
      Complex.exp (Real.pi * Complex.I / 5) * paper2CompletedTheta τ := by
  sorry

/-- The manuscript's five-term S-law and its algebraic reduction to the two
displayed characteristic components. -/
theorem completedTheta_S {τ : ℂ} (hτ : 0 < τ.im) :
    paper2CompletedTheta (-1 / τ) =
        ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
          ∑ r : Fin 5, paper2ThetaAB_c2c1
            (1 / 2, -(1 / 10) + (r : ℝ) / 5)
            (-(1 / 2), -(1 / 10)) τ ∧
    paper2CompletedTheta (-1 / τ) =
        ((((Real.sqrt 5 : ℝ) : ℂ)⁻¹ * τ) / 2) *
          ((1 + Complex.exp (-((Real.pi : ℂ) * Complex.I) / 5)) *
              paper2ThetaAB_c2c1
                (1 / 2, 1 / 10) (-(1 / 2), -(1 / 10)) τ +
            (1 + Complex.exp (3 * Real.pi * Complex.I / 5)) *
              paper2ThetaAB_c2c1
                (1 / 2, 7 / 10) (-(1 / 2), -(1 / 10)) τ) := by
  sorry

/-- The exact mixed boundary derivative and Bruinier--Funke image. -/
theorem exact_differential_image {τ : ℂ} (hτ : 0 < τ.im) :
    dbar paper2CompletedTheta τ =
        -(Complex.I / (4 * ((Real.sqrt (10 * τ.im) : ℝ) : ℂ))) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            paper2ThetaComponent (j : ℤ) τ *
              (starRingEnd ℂ) (paper2GComponent (j : ℤ) τ) ∧
    xi1 paper2CompletedTheta τ =
        -(((Real.sqrt τ.im / (2 * Real.sqrt 10) : ℝ)) : ℂ) *
          ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ j *
            (starRingEnd ℂ) (paper2ThetaComponent (j : ℤ) τ) *
              paper2GComponent (j : ℤ) τ := by
  sorry

/-- The displayed differential images are nonzero and the completed theta is
not weight-one harmonic; the explicit witness point is `2i`. -/
theorem completedTheta_not_harmonic :
    Delta1 paper2CompletedTheta (2 * Complex.I) ≠ 0 ∧
    dbar (xi1 paper2CompletedTheta) (2 * Complex.I) ≠ 0 ∧
    (fun τ => dbar paper2CompletedTheta τ) ≠ 0 ∧
    xi1 paper2CompletedTheta ≠ 0 := by
  sorry

end

end PalomarQseriesRowFactorization
