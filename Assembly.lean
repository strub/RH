import RH.Solution
import Main

/-!
# The Riemann Hypothesis of `RH/Statement.lean`

This file proves `RH.riemann_hypothesis`, the last theorem of `RH/Challenge.lean`. It
combines two things:

* `RH.riemann_hypothesis_of_mathlib`, from this project: the statement of
  `RH/Statement.lean` follows from Mathlib's `RiemannHypothesis`;
* `riemannHypothesis`, from the module `Main` of
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis):
  a proof of Mathlib's `RiemannHypothesis`.

It is kept out of the default build target: importing `Main` loads about 150,000 compiled
modules, which needs the prebuilt cache of that repository and, on macOS, a raised
`kern.maxvnodes`.
-/

/-- The Riemann Hypothesis. -/
theorem RH.riemann_hypothesis : RH.RiemannHypothesis :=
  RH.riemann_hypothesis_of_mathlib riemannHypothesis
