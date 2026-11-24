import RH.Bridge.Categorical
import RH.Bridge.Model

/-!
# What `RH/Statement.lean` says, in terms of Mathlib

This file collects the conclusions of the bridge, for every complete ordered field of the
statement:

* `reals_exist`, `zeta_exists`: the statement is not vacuous;
* `zeta_unique`: the zeta function of the statement is a single function;
* `riemannHypothesis_iff`: the statement is equivalent to Mathlib's `RiemannHypothesis`.

None of this uses a proof of the Riemann Hypothesis.
-/

namespace RHBridge

/-- Over every complete ordered field, a zeta function exists. -/
theorem zeta_exists (R : RH.Reals) :
    ∃ zeta : RH.Complex R → RH.Complex R, RH.IsZeta R zeta :=
  ⟨_, (iso R).isZeta_riemannZeta⟩

/-- Two zeta functions over the same field agree everywhere but at `1`. -/
theorem zeta_unique (R : RH.Reals) (zeta zeta' : RH.Complex R → RH.Complex R) :
    RH.IsZeta R zeta → RH.IsZeta R zeta' →
    ∀ s : RH.Complex R, ¬ s = RH.Complex.ofReal R R.one → zeta s = zeta' s := by
  intro h h' s hs
  have hs' : (iso R).cx s ≠ 1 := by
    rw [← (iso R).cx_one]
    exact (iso R).cx.injective.ne hs
  apply (iso R).cx.injective
  rw [(iso R).cx_zeta zeta h s hs', (iso R).cx_zeta zeta' h' s hs']

/-- The statement of `RH/Statement.lean` is equivalent to Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesis_iff : RH.RiemannHypothesis ↔ _root_.RiemannHypothesis :=
  ⟨fun h => realIso.riemannHypothesisOver_iff.1 (h realModel),
    fun h R => (iso R).riemannHypothesisOver_iff.2 h⟩

end RHBridge
