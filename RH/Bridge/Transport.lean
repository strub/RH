import Mathlib
import RH.Statement

/-!
# The definitions of `RH/Statement.lean` are the ones of Mathlib

Let `R` be a complete ordered field in the sense of `RH/Statement.lean`, together with an
isomorphism `I : RealIso R` onto Mathlib's real numbers. This file shows that every
definition of the statement, carried along `I`, is the corresponding notion of Mathlib:
limits, the complex numbers, complex differentiability, the exponential, the logarithm,
and finally the zeta function and the Riemann Hypothesis.

Nothing here is part of the statement; this file is only evidence that the statement
says what it should.
-/

open Filter Topology

namespace RHBridge

/-- An isomorphism between a complete ordered field `R` of `RH/Statement.lean` and
Mathlib's real numbers. `R.inv` is only constrained away from zero, and `R.sup` only on
non-empty sets that are bounded above. -/
structure RealIso (R : RH.Reals) where
  φ : R.carrier ≃ ℝ
  map_zero : φ R.zero = 0
  map_one : φ R.one = 1
  map_add : ∀ x y, φ (R.add x y) = φ x + φ y
  map_neg : ∀ x, φ (R.neg x) = -φ x
  map_mul : ∀ x y, φ (R.mul x y) = φ x * φ y
  map_inv : ∀ x, x ≠ R.zero → φ (R.inv x) = (φ x)⁻¹
  map_le : ∀ x y, R.le x y ↔ φ x ≤ φ y
  map_sup : ∀ E : R.carrier → Prop,
    (∃ x, E x) → (∃ b, ∀ x, E x → R.le x b) → φ (R.sup E) = sSup {y | E (φ.symm y)}

namespace RealIso

variable {R : RH.Reals} (I : RealIso R)

/-! ## Real numbers -/

theorem map_lt (x y : R.carrier) : R.lt x y ↔ I.φ x < I.φ y := by
  unfold RH.Reals.lt
  rw [I.map_le, not_le]

theorem map_sub (x y : R.carrier) : I.φ (R.sub x y) = I.φ x - I.φ y := by
  unfold RH.Reals.sub
  rw [I.map_add, I.map_neg, sub_eq_add_neg]

theorem map_two : I.φ R.two = 2 := by
  unfold RH.Reals.two
  rw [I.map_add, I.map_one]
  norm_num

theorem map_ofNat (n : ℕ) : I.φ (R.ofNat n) = n := by
  induction n with
  | zero =>
    change I.φ R.zero = _
    simp [I.map_zero]
  | succ n ih =>
    change I.φ (R.add (R.ofNat n) R.one) = _
    rw [I.map_add, I.map_one, ih]
    push_cast
    rfl

theorem ne_zero_iff (x : R.carrier) : x ≠ R.zero ↔ I.φ x ≠ 0 := by
  rw [← I.map_zero]
  exact I.φ.injective.ne_iff.symm

/-- The supremum of a set with a single element is that element. -/
theorem map_sup_singleton (E : R.carrier → Prop) (a : ℝ) (h : ∀ x, E x ↔ I.φ x = a) :
    I.φ (R.sup E) = a := by
  have hset : {y | E (I.φ.symm y)} = {a} := by
    ext y
    simp [h]
  have ha : E (I.φ.symm a) := (h _).2 (by simp)
  rw [I.map_sup E ⟨_, ha⟩ ⟨I.φ.symm a, fun x hx => by rw [I.map_le]; simp [(h x).1 hx]⟩, hset,
    csSup_singleton]

theorem map_sqrt (a : R.carrier) (ha : 0 ≤ I.φ a) : I.φ (R.sqrt a) = Real.sqrt (I.φ a) := by
  unfold RH.Reals.sqrt
  have hset : {y | R.le (R.mul (I.φ.symm y) (I.φ.symm y)) a} = {y | y * y ≤ I.φ a} := by
    ext y
    simp [I.map_le, I.map_mul]
  have hub : ∀ y : ℝ, y * y ≤ I.φ a → y ≤ Real.sqrt (I.φ a) := fun y hy =>
    le_trans (le_abs_self y) (Real.abs_le_sqrt (by rw [sq]; exact hy))
  rw [I.map_sup, hset]
  · exact IsGreatest.csSup_eq ⟨by simp [Real.mul_self_sqrt ha], fun y hy => hub y hy⟩
  · exact ⟨R.zero, by rw [I.map_le, I.map_mul, I.map_zero]; simpa using ha⟩
  · refine ⟨I.φ.symm (Real.sqrt (I.φ a)), fun x hx => ?_⟩
    rw [I.map_le, I.map_mul] at hx
    rw [I.map_le]
    simpa using hub _ hx

/-! ## Limits -/

theorem map_tendsto (u : ℕ → R.carrier) (l : R.carrier) :
    R.Tendsto u l ↔ Tendsto (fun n => I.φ (u n)) atTop (𝓝 (I.φ l)) := by
  rw [Metric.tendsto_atTop]
  unfold RH.Reals.Tendsto
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (I.φ.symm ε) (by rw [I.map_lt, I.map_zero]; simpa using hε)
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [I.map_lt, I.map_lt, I.map_sub, I.map_add] at this
    simp only [Equiv.apply_symm_apply] at this
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [this.1, this.2]
  · intro h ε hε
    rw [I.map_lt, I.map_zero] at hε
    obtain ⟨N, hN⟩ := h (I.φ ε) hε
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq, abs_lt] at this
    rw [I.map_lt, I.map_lt, I.map_sub, I.map_add]
    constructor <;> linarith [this.1, this.2]

theorem map_lim (u : ℕ → R.carrier) (L : ℝ)
    (h : Tendsto (fun n => I.φ (u n)) atTop (𝓝 L)) : I.φ (R.lim u) = L := by
  unfold RH.Reals.lim
  apply I.map_sup_singleton
  intro x
  rw [I.map_tendsto]
  exact ⟨fun hx => tendsto_nhds_unique hx h, fun hx => hx ▸ h⟩

/-! ## Complex numbers -/

/-- The isomorphism between the complex numbers over `R` and Mathlib's. -/
def cx : RH.Complex R ≃ ℂ where
  toFun z := ⟨I.φ z.re, I.φ z.im⟩
  invFun w := ⟨I.φ.symm w.re, I.φ.symm w.im⟩
  left_inv z := by cases z; simp
  right_inv w := by apply Complex.ext <;> simp

@[simp] theorem cx_re (z : RH.Complex R) : (I.cx z).re = I.φ z.re := rfl

@[simp] theorem cx_im (z : RH.Complex R) : (I.cx z).im = I.φ z.im := rfl

@[simp] theorem cx_symm_re (w : ℂ) : (I.cx.symm w).re = I.φ.symm w.re := rfl

@[simp] theorem cx_symm_im (w : ℂ) : (I.cx.symm w).im = I.φ.symm w.im := rfl

theorem cx_ofReal (x : R.carrier) : I.cx (RH.Complex.ofReal R x) = (I.φ x : ℂ) := by
  apply Complex.ext <;> simp [RH.Complex.ofReal, I.map_zero]

theorem cx_zero : I.cx (RH.Complex.ofReal R R.zero) = 0 := by
  rw [I.cx_ofReal, I.map_zero, Complex.ofReal_zero]

theorem cx_one : I.cx (RH.Complex.ofReal R R.one) = 1 := by
  rw [I.cx_ofReal, I.map_one, Complex.ofReal_one]

theorem cx_add (z w : RH.Complex R) : I.cx (RH.Complex.add R z w) = I.cx z + I.cx w := by
  apply Complex.ext <;> simp [RH.Complex.add, I.map_add]

theorem cx_sub (z w : RH.Complex R) : I.cx (RH.Complex.sub R z w) = I.cx z - I.cx w := by
  apply Complex.ext <;> simp [RH.Complex.sub, I.map_sub]

theorem cx_mul (z w : RH.Complex R) : I.cx (RH.Complex.mul R z w) = I.cx z * I.cx w := by
  apply Complex.ext <;> simp [RH.Complex.mul, I.map_sub, I.map_add, I.map_mul]

theorem cx_scale (x : R.carrier) (z : RH.Complex R) :
    I.cx (RH.Complex.scale R x z) = (I.φ x : ℂ) * I.cx z := by
  apply Complex.ext <;> simp [RH.Complex.scale, I.map_mul]

theorem map_abs (z : RH.Complex R) : I.φ (RH.Complex.abs R z) = ‖I.cx z‖ := by
  unfold RH.Complex.abs
  rw [I.map_sqrt, I.map_add, I.map_mul, I.map_mul, Complex.norm_def, Complex.normSq_apply]
  · rfl
  · rw [I.map_add, I.map_mul, I.map_mul]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem cx_pow (z : RH.Complex R) (k : ℕ) : I.cx (RH.Complex.pow R z k) = I.cx z ^ k := by
  induction k with
  | zero =>
    change I.cx (RH.Complex.ofReal R R.one) = _
    simp [I.cx_one]
  | succ k ih =>
    change I.cx (RH.Complex.mul R (RH.Complex.pow R z k) z) = _
    rw [I.cx_mul, ih, pow_succ]

theorem cx_sum (a : ℕ → RH.Complex R) (N : ℕ) :
    I.cx (RH.Complex.sum R a N) = ∑ n ∈ Finset.range N, I.cx (a n) := by
  induction N with
  | zero =>
    change I.cx (RH.Complex.ofReal R R.zero) = _
    simp [I.cx_zero]
  | succ N ih =>
    change I.cx (RH.Complex.add R (RH.Complex.sum R a N) (a N)) = _
    rw [I.cx_add, ih, Finset.sum_range_succ]

/-- A sequence of complex numbers converges if and only if its real and imaginary parts
do. -/
theorem _root_.RHBridge.tendsto_iff_re_im (f : ℕ → ℂ) (w : ℂ) :
    Tendsto f atTop (𝓝 w) ↔
      Tendsto (fun n => (f n).re) atTop (𝓝 w.re) ∧ Tendsto (fun n => (f n).im) atTop (𝓝 w.im) := by
  constructor
  · intro h
    exact ⟨(Complex.continuous_re.tendsto w).comp h, (Complex.continuous_im.tendsto w).comp h⟩
  · rintro ⟨hre, him⟩
    have h1 := (Complex.continuous_ofReal.tendsto w.re).comp hre
    have h2 := ((Complex.continuous_ofReal.tendsto w.im).comp him).mul_const Complex.I
    have := h1.add h2
    simpa [Function.comp_def, Complex.re_add_im] using this

theorem cx_tendsto (z : ℕ → RH.Complex R) (l : RH.Complex R) :
    RH.Complex.Tendsto R z l ↔ Tendsto (fun n => I.cx (z n)) atTop (𝓝 (I.cx l)) := by
  unfold RH.Complex.Tendsto
  rw [tendsto_iff_re_im, I.map_tendsto, I.map_tendsto]
  rfl

theorem cx_lim (z : ℕ → RH.Complex R) (L : ℂ)
    (h : Tendsto (fun n => I.cx (z n)) atTop (𝓝 L)) : I.cx (RH.Complex.lim R z) = L := by
  rw [tendsto_iff_re_im] at h
  apply Complex.ext
  · exact I.map_lim _ _ h.1
  · exact I.map_lim _ _ h.2

/-! ## Complex differentiability -/

/-- Complex differentiability in Mathlib, in the `ε`-`δ` form used by the statement. -/
theorem _root_.RHBridge.differentiableAt_iff (F : ℂ → ℂ) (s : ℂ) :
    DifferentiableAt ℂ F s ↔
      ∃ d : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℂ, ‖h‖ < δ → ‖F (s + h) - F s - d * h‖ ≤ ε * ‖h‖ := by
  constructor
  · intro hF
    refine ⟨deriv F s, fun ε hε => ?_⟩
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 hF.hasDerivAt
    rw [Asymptotics.isLittleO_iff] at this
    obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff.1 (this hε)
    refine ⟨δ, hδ, fun h hh => ?_⟩
    have := H (y := h) (by simpa using hh)
    simpa [smul_eq_mul, mul_comm] using this
  · rintro ⟨d, hd⟩
    refine HasDerivAt.differentiableAt (f' := d) ?_
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := hd ε hε
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun h hh => ?_⟩
    have := H h (by simpa using hh)
    simpa [smul_eq_mul, mul_comm] using this

/-- A function on the complex numbers over `R`, as a function on Mathlib's. -/
def conj (f : RH.Complex R → RH.Complex R) : ℂ → ℂ :=
  fun w => I.cx (f (I.cx.symm w))

theorem conj_cx (f : RH.Complex R → RH.Complex R) (s : RH.Complex R) :
    I.conj f (I.cx s) = I.cx (f s) := by
  simp [conj]

theorem cx_differentiable (f : RH.Complex R → RH.Complex R) (s : RH.Complex R) :
    RH.Complex.Differentiable R f s ↔ DifferentiableAt ℂ (I.conj f) (I.cx s) := by
  rw [differentiableAt_iff]
  unfold RH.Complex.Differentiable
  have key : ∀ (d h : RH.Complex R) (ε : R.carrier),
      R.le
          (RH.Complex.abs R (RH.Complex.sub R
            (RH.Complex.sub R (f (RH.Complex.add R s h)) (f s)) (RH.Complex.mul R d h)))
          (R.mul ε (RH.Complex.abs R h)) ↔
        ‖I.conj f (I.cx s + I.cx h) - I.conj f (I.cx s) - I.cx d * I.cx h‖ ≤
          I.φ ε * ‖I.cx h‖ := by
    intro d h ε
    rw [I.map_le, I.map_abs, I.map_mul, I.map_abs, I.cx_sub, I.cx_sub, I.cx_mul, ← I.cx_add,
      I.conj_cx, I.conj_cx]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨I.cx d, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, H⟩ := hd (I.φ.symm ε) (by rw [I.map_lt, I.map_zero]; simpa using hε)
    rw [I.map_lt, I.map_zero] at hδ
    refine ⟨I.φ δ, hδ, fun h hh => ?_⟩
    have := (key d (I.cx.symm h) (I.φ.symm ε)).1
      (H (I.cx.symm h) (by rw [I.map_lt, I.map_abs]; simpa using hh))
    simpa using this
  · rintro ⟨d, hd⟩
    refine ⟨I.cx.symm d, fun ε hε => ?_⟩
    rw [I.map_lt, I.map_zero] at hε
    obtain ⟨δ, hδ, H⟩ := hd (I.φ ε) hε
    refine ⟨I.φ.symm δ, by rw [I.map_lt, I.map_zero]; simpa using hδ, fun h hh => ?_⟩
    rw [I.map_lt, I.map_abs] at hh
    rw [key]
    simpa using H (I.cx h) (by simpa using hh)

/-! ## Exponential and logarithm -/

theorem map_factorial (k : ℕ) : I.φ (R.factorial k) = (k.factorial : ℝ) := by
  induction k with
  | zero =>
    change I.φ R.one = _
    simp [I.map_one]
  | succ k ih =>
    change I.φ (R.mul (R.ofNat (k + 1)) (R.factorial k)) = _
    rw [I.map_mul, I.map_ofNat, ih, Nat.factorial_succ]
    push_cast
    rfl

theorem cx_expTerm (z : RH.Complex R) (k : ℕ) :
    I.cx (RH.Complex.expTerm R z k) = I.cx z ^ k / (k.factorial : ℂ) := by
  unfold RH.Complex.expTerm
  have hk : R.factorial k ≠ R.zero := by
    rw [I.ne_zero_iff, I.map_factorial]
    exact_mod_cast k.factorial_ne_zero
  rw [I.cx_scale, I.map_inv _ hk, I.map_factorial, I.cx_pow]
  push_cast
  rw [div_eq_inv_mul]

theorem cx_exp (z : RH.Complex R) : I.cx (RH.Complex.exp R z) = Complex.exp (I.cx z) := by
  unfold RH.Complex.exp
  apply I.cx_lim
  have := (NormedSpace.expSeries_div_hasSum_exp (I.cx z)).tendsto_sum_nat
  rw [← Complex.exp_eq_exp_ℂ] at this
  simpa [I.cx_sum, I.cx_expTerm] using this

theorem map_exp (x : R.carrier) : I.φ (R.exp x) = Real.exp (I.φ x) := by
  unfold RH.Reals.exp
  rw [← I.cx_re, I.cx_exp, I.cx_ofReal, Complex.exp_ofReal_re]

theorem map_log (y : R.carrier) (hy : 0 < I.φ y) : I.φ (R.log y) = Real.log (I.φ y) := by
  unfold RH.Reals.log
  apply I.map_sup_singleton
  intro x
  rw [← I.φ.injective.eq_iff, I.map_exp]
  exact ⟨fun h => by rw [← h, Real.log_exp], fun h => by rw [h, Real.exp_log hy]⟩

theorem cx_natPowNeg (n : ℕ) (hn : 0 < n) (s : RH.Complex R) :
    I.cx (RH.Complex.natPowNeg R n s) = (n : ℂ) ^ (-I.cx s) := by
  unfold RH.Complex.natPowNeg
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [I.cx_exp, I.cx_scale, I.map_neg, I.map_log _ (by rw [I.map_ofNat]; exact hn'), I.map_ofNat,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hn'.le]
  congr 1
  push_cast
  ring

/-! ## The zeta function -/

/-- The partial sums of `1 + 1/2^s + 1/3^s + ...` tend to `riemannZeta s` when `Re s > 1`. -/
theorem _root_.RHBridge.tendsto_zeta_sum (w : ℂ) (hw : 1 < w.re) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) ^ (-w)) atTop
      (𝓝 (riemannZeta w)) := by
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ w) := by
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hw)
    simpa using this
  have := hsum.hasSum.tendsto_sum_nat
  rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hw] at this
  simpa [Complex.cpow_neg] using this

theorem tendsto_zetaTerm (s : RH.Complex R) (hs : 1 < (I.cx s).re) :
    Tendsto (fun N => I.cx (RH.Complex.sum R (RH.zetaTerm R s) N)) atTop
      (𝓝 (riemannZeta (I.cx s))) := by
  have := tendsto_zeta_sum (I.cx s) hs
  refine this.congr fun N => ?_
  rw [I.cx_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold RH.zetaTerm
  rw [I.cx_natPowNeg _ (Nat.succ_pos n)]

/-- `zeta` is a zeta function in the sense of the statement if and only if, carried to
Mathlib's complex numbers, it is differentiable away from `1` and equal to Mathlib's
`riemannZeta` on the half-plane `Re s > 1`. -/
theorem isZeta_iff (zeta : RH.Complex R → RH.Complex R) :
    RH.IsZeta R zeta ↔
      (∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ (I.conj zeta) w) ∧
      (∀ w : ℂ, 1 < w.re → I.conj zeta w = riemannZeta w) := by
  unfold RH.IsZeta
  have hone : ∀ s : RH.Complex R, s = RH.Complex.ofReal R R.one ↔ I.cx s = 1 := fun s => by
    rw [← I.cx_one]
    exact I.cx.injective.eq_iff.symm
  constructor
  · rintro ⟨hd, hs⟩
    constructor
    · intro w hw
      have := (I.cx_differentiable zeta (I.cx.symm w)).1
        (hd _ (by rw [hone]; simpa using hw))
      simpa using this
    · intro w hw
      have h1 := (I.cx_tendsto _ _).1
        (hs (I.cx.symm w) (by rw [I.map_lt, I.map_one]; simpa using hw))
      have h2 := I.tendsto_zetaTerm (I.cx.symm w) (by simpa using hw)
      have := tendsto_nhds_unique h1 h2
      simpa [conj] using this
  · rintro ⟨hd, hs⟩
    constructor
    · intro s hs1
      rw [I.cx_differentiable]
      exact hd _ (by rwa [hone] at hs1)
    · intro s hs1
      rw [I.map_lt, I.map_one] at hs1
      rw [I.cx_tendsto, ← I.conj_cx, hs _ (by simpa using hs1)]
      exact I.tendsto_zetaTerm s (by simpa using hs1)

/-- Mathlib's `riemannZeta`, carried to the complex numbers over `R`, is a zeta function in
the sense of the statement. -/
theorem isZeta_riemannZeta : RH.IsZeta R (fun s => I.cx.symm (riemannZeta (I.cx s))) := by
  rw [I.isZeta_iff]
  have : I.conj (fun s => I.cx.symm (riemannZeta (I.cx s))) = riemannZeta := by
    funext w
    simp [conj]
  rw [this]
  exact ⟨fun w hw => differentiableAt_riemannZeta hw, fun _ _ => rfl⟩

/-- A function on Mathlib's complex numbers that is differentiable away from `1` and equal
to `riemannZeta` on the half-plane `Re s > 1` is equal to `riemannZeta` away from `1`. -/
theorem _root_.RHBridge.eq_riemannZeta (F : ℂ → ℂ) (hd : ∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ F w)
    (hs : ∀ w : ℂ, 1 < w.re → F w = riemannZeta w) (w : ℂ) (hw : w ≠ 1) :
    F w = riemannZeta w := by
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hF : AnalyticOnNhd ℂ F {1}ᶜ :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hd z hz).differentiableWithinAt) hopen
  have hZ : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt) hopen
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hev : F =ᶠ[𝓝 (2 : ℂ)] riemannZeta := by
    have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact Filter.eventuallyEq_of_mem this hs
  exact hF.eqOn_of_preconnected_of_eventuallyEq hZ hconn h2 hev hw

/-- A zeta function in the sense of the statement is Mathlib's `riemannZeta` away from `1`. -/
theorem cx_zeta (zeta : RH.Complex R → RH.Complex R) (h : RH.IsZeta R zeta) (s : RH.Complex R)
    (hs : I.cx s ≠ 1) : I.cx (zeta s) = riemannZeta (I.cx s) := by
  rw [I.isZeta_iff] at h
  rw [← I.conj_cx]
  exact eq_riemannZeta _ h.1 h.2 _ hs

/-! ## The Riemann Hypothesis -/

theorem isTrivialZero_iff (s : RH.Complex R) :
    RH.IsTrivialZero R s ↔ ∃ n : ℕ, I.cx s = -2 * ((n : ℂ) + 1) := by
  unfold RH.IsTrivialZero
  refine exists_congr fun n => ?_
  rw [← I.cx.injective.eq_iff, I.cx_ofReal, I.map_neg, I.map_mul, I.map_two, I.map_ofNat]
  push_cast
  constructor <;> intro h <;> rw [h] <;> ring

/-- The statement of `RH/Statement.lean`, for the field `R` alone. -/
def _root_.RHBridge.RiemannHypothesisOver (R : RH.Reals) : Prop :=
  ∀ zeta : RH.Complex R → RH.Complex R, RH.IsZeta R zeta →
    ∀ s : RH.Complex R,
      zeta s = RH.Complex.ofReal R R.zero →
      ¬ s = RH.Complex.ofReal R R.one →
      ¬ RH.IsTrivialZero R s →
      s.re = R.inv R.two

include I in
/-- Over a field `R` isomorphic to Mathlib's real numbers, the statement of
`RH/Statement.lean` is equivalent to Mathlib's `RiemannHypothesis`. -/
theorem riemannHypothesisOver_iff : RiemannHypothesisOver R ↔ _root_.RiemannHypothesis := by
  have hhalf : ∀ x : R.carrier, x = R.inv R.two ↔ I.φ x = 1 / 2 := fun x => by
    rw [← I.φ.injective.eq_iff, I.map_inv _ (by rw [I.ne_zero_iff, I.map_two]; norm_num),
      I.map_two, one_div]
  have hone : ∀ s : RH.Complex R, s = RH.Complex.ofReal R R.one ↔ I.cx s = 1 := fun s => by
    rw [← I.cx_one]
    exact I.cx.injective.eq_iff.symm
  have hzero : ∀ z : RH.Complex R, z = RH.Complex.ofReal R R.zero ↔ I.cx z = 0 := fun z => by
    rw [← I.cx_zero]
    exact I.cx.injective.eq_iff.symm
  constructor
  · intro h w hw htriv hw1
    have := h _ I.isZeta_riemannZeta (I.cx.symm w) (by rw [hzero]; simpa using hw)
      (by rw [hone]; simpa using hw1) (by rw [I.isTrivialZero_iff]; simpa using htriv)
    rw [hhalf] at this
    simpa using this
  · intro h zeta hzeta s hs hs1 htriv
    rw [hone] at hs1
    rw [hzero, I.cx_zeta zeta hzeta s hs1] at hs
    rw [I.isTrivialZero_iff] at htriv
    rw [hhalf]
    exact h (I.cx s) hs htriv hs1

end RealIso

end RHBridge
