import RH.Statement

/-!
# What has to be proved

The theorems that go with `RH/Statement.lean`, without their proofs. The first two say
that `RH.RiemannHypothesis` is not vacuous. The third is not needed for that; it says
that the zeta function of the statement is a single function.
-/

/-- A complete ordered field exists. -/
theorem RH.reals_exist : Nonempty RH.Reals := sorry

/-- Over every complete ordered field, a zeta function exists. -/
theorem RH.zeta_exists (R : RH.Reals) :
    ∃ zeta : RH.Complex R → RH.Complex R, RH.IsZeta R zeta := sorry

/-- Two zeta functions over the same field agree everywhere but at `1`. -/
theorem RH.zeta_unique (R : RH.Reals) (zeta zeta' : RH.Complex R → RH.Complex R) :
    RH.IsZeta R zeta → RH.IsZeta R zeta' →
    ∀ s : RH.Complex R, ¬ s = RH.Complex.ofReal R R.one → zeta s = zeta' s := sorry

/-- The Riemann Hypothesis. -/
theorem RH.riemann_hypothesis : RH.RiemannHypothesis := sorry
