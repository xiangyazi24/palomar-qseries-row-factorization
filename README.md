# Q-series finite row factorization

> **Local blocked wrapper.** Xiang submits a paper-associated Palomar entry
> only after the paper's complete headline theorem chain is formalized.  This
> package currently proves only the finite row-model layer; the analytic
> completion, transformations, derivative, and nonharmonicity theorem are not
> yet in Lean.  Keep this repository local: do not create its public GitHub
> repository or begin Palomar intake until the full-paper gate is closed.

This repository prepares a
[Palomar](https://palomar-registry.org/) entry associated with
*A shifted indefinite theta completion over Q(sqrt(5)): an asymmetric
boundary derivative and a row-model factorization* by Xiang Huang.

The repository is self-contained apart from its pinned Mathlib dependency. It
contains the exact nine-file transitive source closure extracted from the
canonical internal development at commit
`4c926778c1b8701e3b4d85ec44c33766da9f724b`, together with the signed paper
snapshot in `paper/`.

## Registered statement surface

`Challenge.lean` states three finite coefficient identities:

- `mk_factorization` separates the shifted row-model kernel coefficient into a
  convolution of two explicit positive-definite theta legs with a same-sign
  cone difference;
- `coneDiffH_two_mul` identifies every even cone level with the independently
  defined norm-theta coefficient `BCoeff`;
- `coneDiffH_odd` proves that every odd cone level vanishes.

All sums in the Challenge have explicit finite bounds. The registered Lean
surface does not include the manuscript's Jacobi-triple-product evaluation,
the halved-variable Laurent-series restatement, the analytic Zwegers
completion, modular transformations, differential image, or a provenance
theorem identifying the row model with an older Chan-project source object.

## Repository map

- `Challenge.lean`: Mathlib-only statement surface.
- `Solution.lean`: matching declarations proved from the extracted closure.
- `QseriesFormalization/`: the exact nine-file substantive proof closure.
- `paper/`: signed TeX source, bibliography, and compiled PDF.
- `comparator.json`: declarations, definitions, and permitted axioms checked
  by Comparator.
- `formalization.yaml`: scope, provenance, automation, fidelity, and review.

This standalone repository and its fixed commit will be the authoritative
public source for the Palomar entry; the internal development is not a build
dependency.

## Verification

Run the full checks on Linux:

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./test/landrun_wrapper_test.sh
./test/validate_formalization_test.rb
./scripts/verify-comparator.sh
```

After the repository is publicly frozen, its exact commit can be sent through
[Palomar's submission form](https://submit.palomar-registry.org/).
