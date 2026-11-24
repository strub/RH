/-
# The Riemann Hypothesis, stated without any dependency

This file states the Riemann Hypothesis. It imports nothing: everything the statement
depends on is defined below, on top of the natural numbers and the logical connectives
that every Lean file starts with. Its purpose is to be read, from top to bottom, by
someone who wants to be sure of what has been proved.

The statement is the usual one: every zero of the Riemann zeta function, other than the
negative even integers `-2, -4, -6, ...`, has real part `1/2`.

Neither the real numbers nor the zeta function are constructed. Both are described by
the properties that characterise them, and the statement is made for everything that
has these properties:

* the real numbers are any complete ordered field, as in Gonthier's statement of the
  Four Colour Theorem; any two complete ordered fields are isomorphic;
* the zeta function is any function that is holomorphic on the complex plane without
  the point `1` and equal to `1 + 1/2^s + 1/3^s + ...` when `Re s > 1`; there is only
  one such function, because the plane without a point is connected.

The statement would hold vacuously if no complete ordered field existed, or no such
function. That they exist has to be proved alongside the statement, and is not proved
in this file.

To keep the meaning of the text as plain as possible, the file uses no notation of its
own, no type class and no coercion: every operation is written as a function applied to
its arguments, and names the field `R` it belongs to. The only arguments left implicit
are those of `Complex.mk`, `re` and `im`, where Lean infers `R`. From Lean the file
uses only `Nat` (with `Nat.zero`, `Nat.succ`, `Nat.le` and definitions by recursion),
equality, and the connectives `∀`, `∃`, `→`, `∧`, `∨`, `¬`.
-/

set_option autoImplicit false

namespace RH

/-! ## The real numbers -/

/-- A complete ordered field: a set `carrier` with two constants, four operations, an
order and a supremum operation, satisfying the axioms listed after them.

`inv zero` is not specified. `sup E` is specified only when `E` is non-empty and bounded
above; the statement below never depends on its value for other sets. -/
structure Reals where
  carrier : Type
  zero : carrier
  one : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  le : carrier → carrier → Prop
  sup : (carrier → Prop) → carrier
  -- It is a field.
  add_assoc : ∀ x y z : carrier, add x (add y z) = add (add x y) z
  add_comm : ∀ x y : carrier, add x y = add y x
  add_zero : ∀ x : carrier, add x zero = x
  add_neg : ∀ x : carrier, add x (neg x) = zero
  mul_assoc : ∀ x y z : carrier, mul x (mul y z) = mul (mul x y) z
  mul_comm : ∀ x y : carrier, mul x y = mul y x
  mul_one : ∀ x : carrier, mul x one = x
  mul_inv : ∀ x : carrier, ¬ x = zero → mul x (inv x) = one
  mul_add : ∀ x y z : carrier, mul x (add y z) = add (mul x y) (mul x z)
  zero_ne_one : ¬ zero = one
  -- The order is total.
  le_refl : ∀ x : carrier, le x x
  le_trans : ∀ x y z : carrier, le x y → le y z → le x z
  le_antisymm : ∀ x y : carrier, le x y → le y x → x = y
  le_total : ∀ x y : carrier, le x y ∨ le y x
  -- The order is compatible with the operations.
  add_le_add : ∀ x y z : carrier, le x y → le (add x z) (add y z)
  mul_nonneg : ∀ x y : carrier, le zero x → le zero y → le zero (mul x y)
  -- Completeness: if `E` is non-empty and bounded above, `sup E` is its least upper bound.
  sup_upper : ∀ E : carrier → Prop,
    (∃ x : carrier, E x) → (∃ b : carrier, ∀ x : carrier, E x → le x b) →
    ∀ x : carrier, E x → le x (sup E)
  sup_least : ∀ E : carrier → Prop,
    (∃ x : carrier, E x) → (∃ b : carrier, ∀ x : carrier, E x → le x b) →
    ∀ b : carrier, (∀ x : carrier, E x → le x b) → le (sup E) b

/-- `x < y`. -/
def Reals.lt (R : Reals) (x y : R.carrier) : Prop :=
  ¬ R.le y x

/-- `x - y`. -/
def Reals.sub (R : Reals) (x y : R.carrier) : R.carrier :=
  R.add x (R.neg y)

/-- `2`. -/
def Reals.two (R : Reals) : R.carrier :=
  R.add R.one R.one

/-- The natural number `n`, as a real number: `1 + ... + 1`, with `n` ones. -/
def Reals.ofNat (R : Reals) : Nat → R.carrier
  | Nat.zero => R.zero
  | Nat.succ n => R.add (Reals.ofNat R n) R.one

/-- The square root of a real number `a ≥ 0`: the largest `x` such that `x * x ≤ a`. -/
def Reals.sqrt (R : Reals) (a : R.carrier) : R.carrier :=
  R.sup (fun x : R.carrier => R.le (R.mul x x) a)

/-! ## Limits -/

/-- The sequence `u 0, u 1, u 2, ...` tends to `l`: for every `ε > 0` there is a rank `N`
from which `l - ε < u n < l + ε`. -/
def Reals.Tendsto (R : Reals) (u : Nat → R.carrier) (l : R.carrier) : Prop :=
  ∀ ε : R.carrier, R.lt R.zero ε →
    ∃ N : Nat, ∀ n : Nat, Nat.le N n →
      R.lt (R.sub l ε) (u n) ∧ R.lt (u n) (R.add l ε)

/-- The limit of the sequence `u`, when it has one. A sequence has at most one limit, so
the set of its limits then has a single element, and that element is its supremum. -/
def Reals.lim (R : Reals) (u : Nat → R.carrier) : R.carrier :=
  R.sup (fun l : R.carrier => R.Tendsto u l)

/-! ## The complex numbers -/

/-- A complex number `re + i * im`. -/
structure Complex (R : Reals) where
  re : R.carrier
  im : R.carrier

/-- The real number `x`, as a complex number. -/
def Complex.ofReal (R : Reals) (x : R.carrier) : Complex R :=
  Complex.mk x R.zero

/-- `z + w`. -/
def Complex.add (R : Reals) (z w : Complex R) : Complex R :=
  Complex.mk (R.add z.re w.re) (R.add z.im w.im)

/-- `z - w`. -/
def Complex.sub (R : Reals) (z w : Complex R) : Complex R :=
  Complex.mk (R.sub z.re w.re) (R.sub z.im w.im)

/-- `z * w`. -/
def Complex.mul (R : Reals) (z w : Complex R) : Complex R :=
  Complex.mk
    (R.sub (R.mul z.re w.re) (R.mul z.im w.im))
    (R.add (R.mul z.re w.im) (R.mul z.im w.re))

/-- `x * z`, for a real number `x`. -/
def Complex.scale (R : Reals) (x : R.carrier) (z : Complex R) : Complex R :=
  Complex.mk (R.mul x z.re) (R.mul x z.im)

/-- The modulus `|z|`. -/
def Complex.abs (R : Reals) (z : Complex R) : R.carrier :=
  R.sqrt (R.add (R.mul z.re z.re) (R.mul z.im z.im))

/-- `z^k`. -/
def Complex.pow (R : Reals) (z : Complex R) : Nat → Complex R
  | Nat.zero => Complex.ofReal R R.one
  | Nat.succ k => Complex.mul R (Complex.pow R z k) z

/-- `a 0 + a 1 + ... + a (N - 1)`. -/
def Complex.sum (R : Reals) (a : Nat → Complex R) : Nat → Complex R
  | Nat.zero => Complex.ofReal R R.zero
  | Nat.succ N => Complex.add R (Complex.sum R a N) (a N)

/-- The sequence `z 0, z 1, z 2, ...` of complex numbers tends to `l`. -/
def Complex.Tendsto (R : Reals) (z : Nat → Complex R) (l : Complex R) : Prop :=
  R.Tendsto (fun n : Nat => (z n).re) l.re ∧ R.Tendsto (fun n : Nat => (z n).im) l.im

/-- The limit of the sequence `z` of complex numbers, when it has one. -/
def Complex.lim (R : Reals) (z : Nat → Complex R) : Complex R :=
  Complex.mk (R.lim (fun n : Nat => (z n).re)) (R.lim (fun n : Nat => (z n).im))

/-- The function `f` has a derivative at `s`, in the complex sense: there is a complex
number `d` such that, for every `ε > 0`, there is a `δ > 0` for which
`|f (s + h) - f s - d * h| ≤ ε * |h|` whenever `|h| < δ`. -/
def Complex.Differentiable (R : Reals) (f : Complex R → Complex R) (s : Complex R) : Prop :=
  ∃ d : Complex R,
    ∀ ε : R.carrier, R.lt R.zero ε →
      ∃ δ : R.carrier, R.lt R.zero δ ∧
        ∀ h : Complex R, R.lt (Complex.abs R h) δ →
          R.le
            (Complex.abs R
              (Complex.sub R (Complex.sub R (f (Complex.add R s h)) (f s)) (Complex.mul R d h)))
            (R.mul ε (Complex.abs R h))

/-! ## Exponential and logarithm -/

/-- `k!`, as a real number. -/
def Reals.factorial (R : Reals) : Nat → R.carrier
  | Nat.zero => R.one
  | Nat.succ k => R.mul (R.ofNat (Nat.succ k)) (Reals.factorial R k)

/-- `z^k / k!`. -/
def Complex.expTerm (R : Reals) (z : Complex R) (k : Nat) : Complex R :=
  Complex.scale R (R.inv (R.factorial k)) (Complex.pow R z k)

/-- `exp z`, the sum of the series `1 + z + z^2/2! + z^3/3! + ...`, which converges for
every `z`. -/
def Complex.exp (R : Reals) (z : Complex R) : Complex R :=
  Complex.lim R (Complex.sum R (Complex.expTerm R z))

/-- `exp x`, for a real number `x`. -/
def Reals.exp (R : Reals) (x : R.carrier) : R.carrier :=
  (Complex.exp R (Complex.ofReal R x)).re

/-- `log y`, for a real number `y > 0`: the real number `x` such that `exp x = y`. There
is exactly one, so the set of these `x` has a single element, and that element is its
supremum. -/
def Reals.log (R : Reals) (y : R.carrier) : R.carrier :=
  R.sup (fun x : R.carrier => R.exp x = y)

/-- `1 / n^s`, for a natural number `n ≥ 1`: by definition `exp (-(log n) * s)`. -/
def Complex.natPowNeg (R : Reals) (n : Nat) (s : Complex R) : Complex R :=
  Complex.exp R (Complex.scale R (R.neg (R.log (R.ofNat n))) s)

/-! ## The zeta function -/

/-- The term of rank `n` of the series `1 + 1/2^s + 1/3^s + ...`, the ranks starting
at `0`: `1 / (n + 1)^s`. -/
def zetaTerm (R : Reals) (s : Complex R) (n : Nat) : Complex R :=
  Complex.natPowNeg R (Nat.succ n) s

/-- The function `zeta` is the Riemann zeta function: it has a complex derivative at
every point other than `1`, and `zeta s = 1 + 1/2^s + 1/3^s + ...` when `Re s > 1`.

The value of `zeta` at `1` is not specified. -/
def IsZeta (R : Reals) (zeta : Complex R → Complex R) : Prop :=
  (∀ s : Complex R, ¬ s = Complex.ofReal R R.one → Complex.Differentiable R zeta s) ∧
  (∀ s : Complex R, R.lt R.one s.re →
    Complex.Tendsto R (Complex.sum R (zetaTerm R s)) (zeta s))

/-- `s` is one of the negative even integers `-2, -4, -6, ...`, which are zeros of the
zeta function: `s = -(2 * (n + 1))` for some natural number `n`. -/
def IsTrivialZero (R : Reals) (s : Complex R) : Prop :=
  ∃ n : Nat, s = Complex.ofReal R (R.neg (R.mul R.two (R.ofNat (Nat.succ n))))

/-! ## The Riemann Hypothesis -/

/-- **The Riemann Hypothesis.** Every zero `s` of the zeta function, other than the
negative even integers, has `Re s = 1/2`.

The point `1` is set aside because `IsZeta` does not say what `zeta` is there. -/
def RiemannHypothesis : Prop :=
  ∀ (R : Reals) (zeta : Complex R → Complex R), IsZeta R zeta →
    ∀ s : Complex R,
      zeta s = Complex.ofReal R R.zero →
      ¬ s = Complex.ofReal R R.one →
      ¬ IsTrivialZero R s →
      s.re = R.inv R.two

end RH
