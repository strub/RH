# The Riemann Hypothesis, stated without any dependency

A Lean proof of the Riemann Hypothesis was released by Levent Alpöge on 20 November 2026.
It proves `RiemannHypothesis`, a statement of Mathlib. To know what that statement says,
you have to trust Mathlib's definition of the zeta function, which rests on a large part
of the library.

This project states the Riemann Hypothesis again in a single Lean file that imports
nothing, and proves that statement from the one of Mathlib. It follows what Georges
Gonthier did for the Four Colour Theorem and for the Odd Order Theorem: a statement short
and plain enough to be read by someone who trusts neither the proof nor the library.

## What you have to read

Two files, 270 lines together. Nothing else in this repository has to be read or trusted.

1. [`RH/Statement.lean`](RH/Statement.lean) (246 lines) defines everything and ends with
   the statement, `RH.RiemannHypothesis`.
2. [`RH/Challenge.lean`](RH/Challenge.lean) (24 lines) lists the four theorems that are
   claimed about it, without their proofs.

## What you have to understand

### The statement

`RH.RiemannHypothesis` says: every zero of the Riemann zeta function, other than the
negative even integers `-2, -4, -6, ...`, has real part `1/2`.

Neither the real numbers nor the zeta function are constructed. Each is described by the
properties that characterise it, and the statement is made for everything that has these
properties.

- **The real numbers** are any complete ordered field: the structure `RH.Reals` has a
  carrier, two constants, four operations, an order, a supremum, and 18 axioms. Any two
  complete ordered fields are isomorphic.
- **The zeta function** is any function `zeta` such that `RH.IsZeta R zeta` holds: it has
  a complex derivative at every point other than `1`, and it equals
  `1 + 1/2^s + 1/3^s + ...` when `Re s > 1`. There is only one such function away from
  `1`, because the plane without a point is connected. This is the textbook definition of
  zeta; no analytic continuation is constructed in the file.

Everything in between is elementary: limits of sequences in `ε`-`N` form, complex numbers
as pairs, the complex derivative in `ε`-`δ` form, the exponential as the sum of its
series, the logarithm as its inverse, and `1/n^s` as `exp (-(log n) * s)`.

### The four theorems

A statement of the form "for every `R` and every `zeta` with these properties" would be
true for a bad reason if no such `R` or no such `zeta` existed. The first two theorems of
`RH/Challenge.lean` rule this out, and the third says that `zeta` is a single function.

| Theorem                 | Says                                                          |
|-------------------------|---------------------------------------------------------------|
| `RH.reals_exist`        | a complete ordered field exists                               |
| `RH.zeta_exists`        | over every complete ordered field, a zeta function exists     |
| `RH.zeta_unique`        | two zeta functions over one field agree everywhere but at `1` |
| `RH.riemann_hypothesis` | the Riemann Hypothesis, `RH.RiemannHypothesis`                |

All four are stated with the definitions of `RH/Statement.lean` only.

### The conventions of the file

Four choices are worth knowing before you read it.

- **Values left unspecified.** `R.inv R.zero` is not constrained. `R.sup E` is constrained
  only when `E` is non-empty and bounded above. `zeta` is not constrained at `1`, which is
  why the statement sets `s = 1` aside. The statement never depends on these values.
- **Functions defined through `sup`.** The limit of a sequence is defined as the supremum
  of the set of its limits, and `log y` as the supremum of the set of `x` with
  `exp x = y`. Each of these sets has a single element in every case the statement uses
  (a convergent series, a positive `y`), and the supremum of a one-element set is that
  element. The square root is the supremum of the `x` with `x * x ≤ a`. This is how the
  file defines functions without the axiom of choice.
- **No notation.** The file uses no notation of its own, no type class and no coercion.
  Every operation is a function applied to its arguments and names the field `R` it
  belongs to: `R.add x y`, `RH.Complex.mul R z w`. The only arguments left implicit are
  those of `Complex.mk`, `re` and `im`, where Lean infers `R`.
- **What it takes from Lean.** Only `Nat` (with `Nat.zero`, `Nat.succ`, `Nat.le` and
  definitions by recursion), equality, and the connectives `∀`, `∃`, `→`, `∧`, `∨`, `¬`.

`RH.RiemannHypothesis` depends on no axiom. Besides the definitions of the file, it
depends on 28 constants of Lean: the connectives and equality, `Nat` with its
constructors and `Nat.le`, and the auxiliary constants Lean generates for definitions by
recursion. [`scripts/Audit.lean`](scripts/Audit.lean) prints this list:

```bash
lake build RH.Statement && lake env lean scripts/Audit.lean
```

## What you do not have to read

The rest of the repository is proofs. Lean's kernel checks them, so their content does not
affect what the four theorems mean.

| File                         | Content                                                    |
|------------------------------|------------------------------------------------------------|
| `RH/Bridge/Transport.lean`   | each definition is the corresponding notion of Mathlib     |
| `RH/Bridge/Categorical.lean` | every complete ordered field is isomorphic to Mathlib's    |
| `RH/Bridge/Model.lean`       | Mathlib's real numbers are a complete ordered field        |
| `RH/Bridge/Main.lean`        | zeta exists and is unique; equivalence with Mathlib        |
| `RH/Solution.lean`           | the first three theorems of the challenge, from Mathlib    |
| `Assembly.lean`              | the fourth, from the bridge and the proof of Alpöge        |

`Transport.lean` works with a field `R` given together with an isomorphism onto Mathlib's
real numbers; `Categorical.lean` provides that isomorphism for every `R`. The equivalence
proved in `Main.lean` is `RH.RiemannHypothesis ↔ RiemannHypothesis`.

The proof of Alpöge is the package `tree` of [`lakefile.toml`](lakefile.toml): the
repository [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
at the revision pinned there. Mathlib is pinned at the revision that repository uses.

If you want evidence that the definitions say what they should, without reading proofs,
the statements of `RH/Bridge/Transport.lean` are the place to look: one lemma for each
definition (`map_sqrt`, `map_tendsto`, `cx_differentiable`, `cx_exp`, `map_log`,
`cx_natPowNeg`, `isZeta_iff`, ...), and `cx_zeta`, which says that a zeta function in the
sense of the statement is Mathlib's `riemannZeta` away from `1`.

## What has been checked, and what has not

- The whole project compiles with Lean 4.37.0-rc1, and the four theorems depend on no
  axiom other than `propext`, `Classical.choice` and `Quot.sound`.
- The first three theorems, and the equivalence with Mathlib's statement, use Mathlib
  only. They were compiled from source.
- `RH.riemann_hypothesis` was compiled against the prebuilt cache of the proof of Alpöge.
  That cache was not rebuilt, and its 149,216 modules were not checked again.
- [Comparator](https://github.com/leanprover/comparator) has not been run on this project
  yet. It is the tool that establishes, with a replay in Lean's kernel, that the theorems
  proved are exactly those of `RH/Challenge.lean`. [`comparator.json`](comparator.json)
  and [`scripts/comparator.sh`](scripts/comparator.sh) are ready for it.

## Building

The statement, the bridge and the first three theorems need Mathlib's cache and take a
few minutes:

```bash
lake exe mathlib/cache get
lake build
```

The last theorem needs the proof of Alpöge. `Assembly` is not a default target, because
importing that proof loads about 150,000 compiled modules:

```bash
mkdir -p .lake/packages/tree/.lake
ln -sfn "$PWD/.lake/packages" .lake/packages/tree/.lake/packages
(cd .lake/packages/tree && lake exe cache get)   # about 5 GB to download, 86 GB on disk
lake build Assembly
```

The cache tool of the proof needs Python 3.11 or newer. On macOS, loading the proof
exceeds the default limit on open files; raise it first, until the next restart, with
`sudo sysctl kern.maxvnodes=1500000`.

## Running Comparator

Comparator needs Linux, at least 128 GB of memory and 300 GB of disk. On such a machine,
from the root of this repository:

```bash
scripts/comparator.sh setup        # packages, limits, Lean, exports, caches, build
scripts/comparator.sh companions   # short run: the three theorems that need Mathlib only
scripts/comparator.sh full         # long run: all four theorems
```

The script judges exports. The export of the challenge is made before anything of the
proof is downloaded, and Lean's kernel replays every declaration of the export of the
solution, so the verdict does not rest on the prebuilt cache.

## Background

- G. Gonthier, *Formal proof — the Four-Color Theorem*, Notices of the AMS 55(11), 2008,
  and the files `real.v` and `realplane.v` of [math-comp/fourcolor](https://github.com/math-comp/fourcolor).
- The file `stripped_odd_order_theorem.v` of [math-comp/odd-order](https://github.com/math-comp/odd-order).
- B. H. Gomes and A. Kontorovich, [lean-riemann-hypothesis](https://github.com/bhgomes/lean-riemann-hypothesis),
  an earlier statement of the Riemann Hypothesis in Lean 3 that avoids the analytic
  continuation.
- Lean FRO and Mathlib Initiative, [Lean verification of the Riemann Hypothesis](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/).
