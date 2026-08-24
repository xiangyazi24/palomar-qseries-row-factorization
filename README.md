# A shifted indefinite theta completion over Q(sqrt(5))

This repository prepares a complete Paper 2 entry for the
[Palomar Registry](https://palomar-registry.org/).  It accompanies Xiang
Huang's paper

> *A shifted indefinite theta completion over Q(sqrt(5)): an asymmetric
> boundary derivative and a row-model factorization*.

The repository is self-contained apart from its pinned Mathlib dependency. It
contains the exact 39-file transitive source closure extracted from the
canonical internal development at commit
`93ade4af0234cdd007215842f8b4fbbbb9535985`, together with the signed 15-page
paper in `paper/`. The internal Q-series repository is provenance, not a build
dependency.

## Registered statement surface

The Mathlib-only `Challenge.lean` defines the coefficient model and the
analytic completed theta explicitly. Comparator checks ten declarations:

1. `mk_factorization`: coefficientwise separation of the shifted row model;
2. `coneDiffH_two_mul`: identification of every even cone level with the
   manuscript coefficient;
3. `coneDiffH_odd`: vanishing of every odd cone level;
4. `exact_completion_bridge`: the completed theta is the holomorphic sign
   part `q^(1/10) B(q)` plus the explicit two-boundary correction;
5. `completedTheta_summable`: absolute convergence of the defining completed-
   theta lattice series throughout the upper half-plane;
6. `zwegers_lemma28`: the specialized Fourier-transform identity, including
   its exact square-root constant and exponential sign;
7. `completedTheta_add_one`: the weight-one translation law;
8. `completedTheta_S`: both the five-characteristic inversion law and its
   algebraic reduction to the two displayed components;
9. `exact_differential_image`: the exact Wirtinger derivative and
   Bruinier--Funke image as mixed unary-theta sums;
10. `completedTheta_not_harmonic`: explicit nonvanishing at `2i`, hence failure
   of the weight-one harmonicity equation.

The selected Solution declarations use only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. They use no custom certificate, compiler-
trust axiom, or `sorry`.

## Claim boundary

The formalization proves the explicit convergent completed theta, its
holomorphic sign part, the specialized Lemma 2.8, its transformation laws, the
mixed differential image, and nonharmonicity. It does not assert that this is
the unique or canonical completion of the holomorphic series, does not produce
a closed vector-valued representation, and does not identify the paper's row
model with an older Chan-project source object. These are also non-claims of
the paper.

## Repository map

- `Challenge.lean`: Mathlib-only statement surface.
- `PalomarQseriesRowFactorization/Public.lean`: byte-identical public
  definition block used on the Solution side.
- `Solution.lean`: transports all ten statements to the extracted proof
  closure.
- `QseriesFormalization/`: exact 39-file substantive source closure.
- `AxiomAudit.lean`: permanent `#print axioms` checks for the ten declarations.
- `paper/`: signed TeX source, bibliography, and compiled PDF.
- `comparator.json`: selected declarations and permitted axioms.
- `formalization.yaml`: scope, provenance, automation, fidelity, and review
  metadata.

## Verification

Run the complete checks on Linux:

```text
lake exe cache get
lake build
lake env lean AxiomAudit.lean
ruby scripts/validate-formalization.rb
./test/landrun_wrapper_test.sh
./test/validate_formalization_test.rb
./scripts/verify-comparator.sh
```

After Xiang approves the paper and this repository is publicly frozen, its
exact commit can be sent through
[Palomar's submission form](https://submit.palomar-registry.org/).
