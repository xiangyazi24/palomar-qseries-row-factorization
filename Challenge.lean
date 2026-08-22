import Mathlib

/-!
# Finite row factorization for a shifted indefinite theta kernel

This file gives the Mathlib-only statement surface. All coefficient functions
are explicit finite sums over integer or natural-number boxes.
-/

namespace PalomarQseriesRowFactorization

noncomputable section

/-! ## Norm-theta coefficients -/

/-- The quadratic exponent before division by two. -/
def Q (k r : Int) : Int :=
  4 * k ^ 2 + 2 * k + r ^ 2 + (6 * k + 1) * r

/-- The triangular number `r(r+1)/2`. -/
def triZ (r : Int) : Int := r * (r + 1) / 2

/-- The norm-theta exponent. -/
def E (k r : Int) : Int :=
  2 * k ^ 2 + k + 3 * k * r + triZ r

/-- The integral parity sign. -/
def negOnePowInt (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

/-- Positive-cone coefficient. -/
def ACoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N)).sum
    (fun p => -negOnePowInt (↑p.2))

/-- Negative-cone coefficient in translated natural coordinates. -/
def DCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N)).sum
    (fun p => negOnePowInt (-(↑p.2 + 1)))

/-- Difference of the two norm-theta cones. -/
def BCoeff (N : Nat) : Int := DCoeff N + ACoeff N

/-! ## Shifted-kernel coefficient model -/

/-- The paper's row quadratic form. -/
abbrev Hq (k r : Int) : Int := Q k r

/-- The integer value of `(-1)^n`. -/
def mkSign (n : Int) : Int := (Int.negOnePow n : Int)

def thetaUBound (a : Int) : Int := |a| + 3

def thetaVBound (a : Int) : Int := |a| + 4

def thetaUCoeff (a : Int) : Int :=
  ∑ u ∈ Finset.Icc (-thetaUBound a) (thetaUBound a),
    if 5 * u ^ 2 - 3 * u = a then mkSign u else 0

def thetaVCoeff (a : Int) : Int :=
  ∑ v ∈ Finset.Icc (-thetaVBound a) (thetaVBound a),
    if 5 * v ^ 2 - 7 * v = a then mkSign v else 0

/-- Coefficient of the product of the two positive-definite theta legs. -/
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

/-- The transported row, with the outer `D-A` sign included. -/
def coneSignedCoeff (k m : Int) : Int :=
  -rowEpsilon k * rowConeCoeff k m

def mkKBound (T : Int) : Int := |T| + 3

def mkRowCoeff (k T : Int) : Int :=
  ∑ a ∈ Finset.Icc (-2) (T - rowMin k),
    QoutCoeff a * rowMixedCoeff k (T - a)

/-- Coefficient of the shifted row-model kernel. -/
def MKcoeff (T : Int) : Int :=
  ∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
    rowEpsilon k * mkRowCoeff k T

def coneKBound (m : Int) : Int := |m| + 1

/-- Coefficient of the same-sign cone difference at a fixed row level. -/
def coneDiffH (m : Int) : Int :=
  ∑ k ∈ Finset.Icc (-coneKBound m) (coneKBound m),
    coneSignedCoeff k m

/-! ## Registered theorems -/

/-- Finite separation of the shifted kernel into a convolution. -/
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

end
end PalomarQseriesRowFactorization
