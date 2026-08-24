import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Ch10: Norm-Supported Indefinite Theta Series over Q(√5)

Definitions for the independently specified Q(√5) norm theta series B(X)
studied in Paper 3.  No source-faithful identification with Chan's missing
kernel is assumed here.

## Main definitions

* `PhiInt` — elements a + bφ of ℤ[φ], φ = (1+√5)/2
* `Q`, `E` — exponent functions from (k,r) atom coordinates
* `beta` — bijection Z² → affine coset L
* `InL` — membership predicate for L = {a+bφ : b-3a ≡ 1 mod 10}
* `epsMul`, `eps6Mul` — multiplication by ε = φ² and ε⁶
* `negOnePowInt` — parity sign function avoiding (-1)^r for negative r
-/

namespace QseriesFormalization
namespace Ch10

@[ext]
structure PhiInt where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace PhiInt

instance : Zero PhiInt := ⟨⟨0, 0⟩⟩
instance : One PhiInt := ⟨⟨1, 0⟩⟩
instance : Add PhiInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg PhiInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub PhiInt := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩

-- φ² = φ+1, so (a₁+b₁φ)(a₂+b₂φ) = (a₁a₂+b₁b₂) + (a₁b₂+a₂b₁+b₁b₂)φ
instance : Mul PhiInt :=
  ⟨fun x y =>
    ⟨x.a * y.a + x.b * y.b,
     x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[simp] theorem zero_a : (0 : PhiInt).a = 0 := rfl
@[simp] theorem zero_b : (0 : PhiInt).b = 0 := rfl
@[simp] theorem one_a : (1 : PhiInt).a = 1 := rfl
@[simp] theorem one_b : (1 : PhiInt).b = 0 := rfl
@[simp] theorem add_a (x y : PhiInt) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : PhiInt) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : PhiInt) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : PhiInt) : (-x).b = -x.b := rfl
@[simp] theorem sub_a (x y : PhiInt) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : PhiInt) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : PhiInt) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : PhiInt) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl
@[simp] theorem mk_a (a b : Int) : (PhiInt.mk a b).a = a := rfl
@[simp] theorem mk_b (a b : Int) : (PhiInt.mk a b).b = b := rfl

def norm (x : PhiInt) : Int := x.a ^ 2 + x.a * x.b - x.b ^ 2

def star (x : PhiInt) : PhiInt := ⟨x.a + x.b, -x.b⟩

def phi : PhiInt := ⟨0, 1⟩
def sqrt5 : PhiInt := ⟨-1, 2⟩
def eps : PhiInt := ⟨1, 1⟩

end PhiInt

-- Exponent function Q(k,r) = 4k²+2k+r²+(6k+1)r — always even
def Q (k r : Int) : Int :=
  4 * k ^ 2 + 2 * k + r ^ 2 + (6 * k + 1) * r

-- Triangular number (integer division; use via spec lemma two_mul_triZ)
def triZ (r : Int) : Int := r * (r + 1) / 2

-- E(k,r) = Q(k,r)/2 — the actual series exponent
def E (k r : Int) : Int :=
  2 * k ^ 2 + k + 3 * k * r + triZ r

-- The atom-to-golden-integer bijection
def beta (k r : Int) : PhiInt :=
  ⟨r - 2 * k, 4 * k + 3 * r + 1⟩

-- Affine coset L = {a+bφ : b-3a ≡ 1 mod 10}
def InL (x : PhiInt) : Prop :=
  10 ∣ x.b - 3 * x.a - 1

-- Underlying sublattice L₀ = {a+bφ : b-3a ≡ 0 mod 10}
def InL0 (x : PhiInt) : Prop :=
  10 ∣ x.b - 3 * x.a

-- Positive same-sign cone A: k ≥ 0, r ≥ 0
def InACone (k r : Int) : Prop := 0 ≤ k ∧ 0 ≤ r

instance (k r : Int) : Decidable (InACone k r) :=
  show Decidable (0 ≤ k ∧ 0 ≤ r) from inferInstance

-- Negative same-sign cone D: k < 0, r < 0
def InDCone (k r : Int) : Prop := k < 0 ∧ r < 0

instance (k r : Int) : Decidable (InDCone k r) :=
  show Decidable (k < 0 ∧ r < 0) from inferInstance

-- Parity sign (-1)^n without negative integer exponent issues
def negOnePowInt (n : Int) : Int :=
  if n % 2 = 0 then 1 else -1

@[simp] theorem negOnePowInt_even {n : Int} (h : n % 2 = 0) :
    negOnePowInt n = 1 := by simp [negOnePowInt, h]

@[simp] theorem negOnePowInt_odd {n : Int} (h : n % 2 ≠ 0) :
    negOnePowInt n = -1 := by simp [negOnePowInt, h]

-- Multiplication by ε = φ² (matrix [[1,1],[1,2]])
def epsMul (x : PhiInt) : PhiInt :=
  ⟨x.a + x.b, x.a + 2 * x.b⟩

-- Multiplication by ε⁶ (matrix [[89,144],[144,233]])
def eps6Mul (x : PhiInt) : PhiInt :=
  ⟨89 * x.a + 144 * x.b, 144 * x.a + 233 * x.b⟩

-- 2√5 as element of ℤ[φ]: -2+4φ
def c_2sqrt5 : PhiInt := ⟨-2, 4⟩

-- Cone weight for B = D - A
def BWeight (k r : Int) : Int :=
  if InACone k r then -negOnePowInt r
  else if InDCone k r then negOnePowInt r
  else 0

-- HM exponent after substitution x=X, y=-X³, q=X
def HMExp (k r : Int) : Int :=
  triZ r + 3 * r * k + 2 * k ^ 2 + k

-- A-cone contribution: sum over (k,r) ∈ [0,N] × [0,2N+1] with E(k,r) = N
def ACoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (↑p.1) (↑p.2) = ↑N)).sum
    (fun p => -negOnePowInt (↑p.2))

-- D-cone contribution via (m,s) ↦ (-(m+1), -(s+1)), m,s ∈ [0,N] × [0,2N+1]
def DCoeff (N : Nat) : Int :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun p => E (-(↑p.1 + 1)) (-(↑p.2 + 1)) = ↑N)).sum
    (fun p => negOnePowInt (-(↑p.2 + 1)))

-- B_N = D - A (cone difference)
def BCoeff (N : Nat) : Int := DCoeff N + ACoeff N

end Ch10
end QseriesFormalization
