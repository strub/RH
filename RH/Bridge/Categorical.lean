import RH.Bridge.Transport

/-!
# Every complete ordered field is isomorphic to Mathlib's real numbers

For every complete ordered field `R` in the sense of `RH/Statement.lean`, this file builds
an isomorphism `iso R : RealIso R` onto Mathlib's real numbers.

The field `R` is first given the structures Mathlib expects (a field, a linear order, an
ordered ring), and shown to be archimedean. Mathlib then provides an order-preserving
ring homomorphism from `R` to the real numbers, and completeness of `R` makes it onto.
-/

namespace RHBridge

namespace Categorical

open Classical

variable (R : RH.Reals)

/-! ## `R` as a linear ordered field of Mathlib -/

noncomputable local instance : Zero R.carrier := ⟨R.zero⟩
noncomputable local instance : One R.carrier := ⟨R.one⟩
noncomputable local instance : Add R.carrier := ⟨R.add⟩
noncomputable local instance : Neg R.carrier := ⟨R.neg⟩
noncomputable local instance : Mul R.carrier := ⟨R.mul⟩

/-- Mathlib wants `0⁻¹ = 0`, which the statement does not ask of `R.inv`. -/
noncomputable local instance : Inv R.carrier :=
  ⟨fun x => if x = R.zero then R.zero else R.inv x⟩

theorem inv_eq (x : R.carrier) (hx : x ≠ R.zero) : x⁻¹ = R.inv x := by
  change (if x = R.zero then R.zero else R.inv x) = R.inv x
  simp only [hx, ↓reduceIte]

noncomputable local instance : Field R.carrier :=
  Field.ofMinimalAxioms R.carrier
    (fun a b c => (R.add_assoc a b c).symm)
    (fun a => (R.add_comm _ _).trans (R.add_zero a))
    (fun a => (R.add_comm _ _).trans (R.add_neg a))
    (fun a b c => (R.mul_assoc a b c).symm)
    R.mul_comm
    (fun a => (R.mul_comm _ _).trans (R.mul_one a))
    (fun a ha => by
      have ha' : ¬ a = R.zero := ha
      change R.mul a (if a = R.zero then R.zero else R.inv a) = R.one
      simp only [ha', ↓reduceIte]
      exact R.mul_inv a ha')
    (by
      change (if R.zero = R.zero then R.zero else R.inv R.zero) = R.zero
      simp only [↓reduceIte])
    R.mul_add
    ⟨R.zero, R.one, R.zero_ne_one⟩

noncomputable local instance : LinearOrder R.carrier where
  le := R.le
  le_refl := R.le_refl
  le_trans := R.le_trans
  le_antisymm := R.le_antisymm
  le_total := R.le_total
  toDecidableLE := Classical.decRel _

local instance : IsOrderedAddMonoid R.carrier where
  add_le_add_left a b h c := R.add_le_add a b c h

theorem zero_le_one' : (0 : R.carrier) ≤ 1 := by
  rcases le_total (0 : R.carrier) 1 with h | h
  · exact h
  · have h' : (0 : R.carrier) ≤ -1 := neg_nonneg.2 h
    have := R.mul_nonneg (-1) (-1) h' h'
    change (0 : R.carrier) ≤ -1 * -1 at this
    simpa using this

local instance : ZeroLEOneClass R.carrier := ⟨zero_le_one' R⟩

local instance : IsStrictOrderedRing R.carrier :=
  IsStrictOrderedRing.of_mul_pos fun a b ha hb =>
    lt_of_le_of_ne (R.mul_nonneg a b ha.le hb.le) (mul_ne_zero ha.ne' hb.ne').symm

/-- `R` is archimedean: otherwise the natural numbers would have a supremum `s`, and
`s - 1` would be a smaller upper bound. -/
theorem archimedean : Archimedean R.carrier := by
  rw [archimedean_iff_nat_le]
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := h
  let E : R.carrier → Prop := fun a => ∃ n : ℕ, a = (n : R.carrier)
  have hne : ∃ a, E a := ⟨0, 0, by simp⟩
  have hbd : ∃ b, ∀ a, E a → R.le a b := ⟨x, by rintro a ⟨n, rfl⟩; exact (hx n).le⟩
  have hup := R.sup_upper E hne hbd
  have hleast := R.sup_least E hne hbd
  have hle : R.sup E ≤ R.sup E - 1 := hleast _ (by
    rintro a ⟨n, rfl⟩
    have h1 : ((n + 1 : ℕ) : R.carrier) ≤ R.sup E := hup _ ⟨n + 1, rfl⟩
    change (n : R.carrier) ≤ R.sup E - 1
    push_cast at h1
    linarith)
  linarith

local instance : Archimedean R.carrier := archimedean R

/-! ## The isomorphism -/

/-- The order-preserving ring homomorphism from `R` to Mathlib's real numbers. -/
noncomputable def hom : R.carrier →+*o ℝ :=
  ConditionallyCompleteLinearOrderedField.inducedOrderRingHom R.carrier ℝ

theorem hom_strictMono : StrictMono (hom R) :=
  (hom R).monotone'.strictMono_of_injective (hom R).toRingHom.injective

theorem hom_ratCast (q : ℚ) : hom R (q : R.carrier) = q :=
  map_ratCast (hom R) q

/-- Completeness of `R` makes the homomorphism onto: a real number `y` is the image of the
supremum of the elements of `R` sent below `y`. -/
theorem hom_surjective : Function.Surjective (hom R) := by
  intro y
  have hmono := hom_strictMono R
  let E : R.carrier → Prop := fun x => hom R x < y
  have hne : ∃ x, E x := by
    obtain ⟨q, hq⟩ := exists_rat_lt y
    exact ⟨(q : R.carrier), by change hom R q < y; rw [hom_ratCast]; exact hq⟩
  have hbelow : ∀ q : ℚ, y < q → ∀ x, E x → R.le x (q : R.carrier) := fun q hq x hx => by
    have : hom R x < hom R (q : R.carrier) := by rw [hom_ratCast]; exact lt_trans hx hq
    exact (hmono.lt_iff_lt.1 this).le
  have hbd : ∃ b, ∀ x, E x → R.le x b := by
    obtain ⟨q, hq⟩ := exists_rat_gt y
    exact ⟨(q : R.carrier), hbelow q hq⟩
  refine ⟨R.sup E, le_antisymm ?_ ?_⟩
  · by_contra h
    push Not at h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    have hub : R.sup E ≤ (q : R.carrier) := R.sup_least E hne hbd _ (hbelow q hq1)
    have := hmono.monotone hub
    rw [hom_ratCast] at this
    linarith
  · by_contra h
    push Not at h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    have hq : E (q : R.carrier) := by change hom R q < y; rw [hom_ratCast]; exact hq2
    have hle : (q : R.carrier) ≤ R.sup E := R.sup_upper E hne hbd _ hq
    have := hmono.monotone hle
    rw [hom_ratCast] at this
    linarith

/-- The homomorphism, as a bijection. -/
noncomputable def equiv : R.carrier ≃ ℝ :=
  Equiv.ofBijective (hom R) ⟨(hom_strictMono R).injective, hom_surjective R⟩

theorem equiv_apply (x : R.carrier) : equiv R x = hom R x := rfl

theorem equiv_le (x y : R.carrier) : R.le x y ↔ equiv R x ≤ equiv R y :=
  (hom_strictMono R).le_iff_le.symm

/-- The isomorphism between `R` and Mathlib's real numbers. -/
noncomputable def iso : RealIso R where
  φ := equiv R
  map_zero := map_zero (hom R)
  map_one := map_one (hom R)
  map_add := map_add (hom R)
  map_neg := map_neg (hom R)
  map_mul := map_mul (hom R)
  map_inv x hx := by
    rw [← inv_eq R x hx]
    exact map_inv₀ (hom R) x
  map_le := equiv_le R
  map_sup E hne hbd := by
    refine (IsLUB.csSup_eq ⟨fun y hy => ?_, fun b hb => ?_⟩ ?_).symm
    · have := (equiv_le R _ _).1 (R.sup_upper E hne hbd _ hy)
      simpa using this
    · have hle : R.le (R.sup E) ((equiv R).symm b) := R.sup_least E hne hbd _ (fun x hx => by
        rw [equiv_le]
        simpa using hb (show equiv R x ∈ {y | E ((equiv R).symm y)} by simpa using hx))
      simpa using (equiv_le R _ _).1 hle
    · obtain ⟨x, hx⟩ := hne
      exact ⟨equiv R x, by simpa using hx⟩

end Categorical

/-- Every complete ordered field in the sense of `RH/Statement.lean` is isomorphic to
Mathlib's real numbers. -/
noncomputable def iso (R : RH.Reals) : RealIso R :=
  Categorical.iso R

end RHBridge
