import RH.Bridge.Transport

/-!
# Mathlib's real numbers are a model of `RH/Statement.lean`

This file tests the definitions of the statement on Mathlib's real numbers:

* they form a complete ordered field in the sense of the statement, so one exists;
* over them, Mathlib's `riemannZeta` is a zeta function in the sense of the statement,
  and it is the only one away from `1`;
* over them, the statement is equivalent to Mathlib's `RiemannHypothesis`.
-/

namespace RHBridge

/-- Mathlib's real numbers, as a complete ordered field in the sense of the statement. -/
noncomputable def realModel : RH.Reals where
  carrier := ℝ
  zero := 0
  one := 1
  add x y := x + y
  neg x := -x
  mul x y := x * y
  inv x := x⁻¹
  le x y := x ≤ y
  sup E := sSup {x | E x}
  add_assoc x y z := (add_assoc x y z).symm
  add_comm := add_comm
  add_zero := add_zero
  add_neg := add_neg_cancel
  mul_assoc x y z := (mul_assoc x y z).symm
  mul_comm := mul_comm
  mul_one := mul_one
  mul_inv _ hx := mul_inv_cancel₀ hx
  mul_add := mul_add
  zero_ne_one := zero_ne_one
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total := le_total
  add_le_add _ _ z h := add_le_add_left h z
  mul_nonneg _ _ := mul_nonneg
  sup_upper _ _ hb _ hx := le_csSup hb hx
  sup_least _ hne _ _ hb := csSup_le hne hb

/-- A complete ordered field exists. -/
theorem reals_exist : Nonempty RH.Reals :=
  ⟨realModel⟩

/-- The identity, as an isomorphism between `realModel` and Mathlib's real numbers. -/
noncomputable def realIso : RealIso realModel where
  φ := Equiv.refl ℝ
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_mul _ _ := rfl
  map_inv _ _ := rfl
  map_le _ _ := Iff.rfl
  map_sup _ _ _ := rfl

/-- Over Mathlib's real numbers, a zeta function in the sense of the statement exists. -/
theorem zeta_exists_real :
    ∃ zeta : RH.Complex realModel → RH.Complex realModel, RH.IsZeta realModel zeta :=
  ⟨_, realIso.isZeta_riemannZeta⟩

/-- Over Mathlib's real numbers, two zeta functions in the sense of the statement agree
everywhere but at `1`. -/
theorem zeta_unique_real (zeta zeta' : RH.Complex realModel → RH.Complex realModel)
    (h : RH.IsZeta realModel zeta) (h' : RH.IsZeta realModel zeta') (s : RH.Complex realModel)
    (hs : ¬ s = RH.Complex.ofReal realModel realModel.one) : zeta s = zeta' s := by
  have hs' : realIso.cx s ≠ 1 := by
    rw [← realIso.cx_one]
    exact realIso.cx.injective.ne hs
  apply realIso.cx.injective
  rw [realIso.cx_zeta zeta h s hs', realIso.cx_zeta zeta' h' s hs']

/-- Over Mathlib's real numbers, the statement of `RH/Statement.lean` is equivalent to
Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesisOver_real_iff :
    RiemannHypothesisOver realModel ↔ _root_.RiemannHypothesis :=
  realIso.riemannHypothesisOver_iff

end RHBridge
