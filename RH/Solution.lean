import RH.Bridge.Main

/-!
# The theorems of `RH/Challenge.lean`, with their proofs

This file states the first three theorems of `RH/Challenge.lean` again, under the same
names, and proves them from Mathlib alone. It must not be imported together with
`RH/Challenge.lean`.

The fourth, `RH.riemann_hypothesis`, is in `Assembly.lean` at the root of the project,
because it imports the whole Lean proof of the Riemann Hypothesis.
-/

/-- A complete ordered field exists. -/
theorem RH.reals_exist : Nonempty RH.Reals :=
  RHBridge.reals_exist

/-- Over every complete ordered field, a zeta function exists. -/
theorem RH.zeta_exists (R : RH.Reals) :
    ∃ zeta : RH.Complex R → RH.Complex R, RH.IsZeta R zeta :=
  RHBridge.zeta_exists R

/-- Two zeta functions over the same field agree everywhere but at `1`. -/
theorem RH.zeta_unique (R : RH.Reals) (zeta zeta' : RH.Complex R → RH.Complex R) :
    RH.IsZeta R zeta → RH.IsZeta R zeta' →
    ∀ s : RH.Complex R, ¬ s = RH.Complex.ofReal R R.one → zeta s = zeta' s :=
  RHBridge.zeta_unique R zeta zeta'

/-- The Riemann Hypothesis of `RH/Statement.lean` follows from Mathlib's. -/
theorem RH.riemann_hypothesis_of_mathlib (h : _root_.RiemannHypothesis) :
    RH.RiemannHypothesis :=
  RHBridge.riemannHypothesis_iff.2 h
