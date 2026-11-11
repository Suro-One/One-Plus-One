# One Plus One

*Formalization of "1 + 1" and why "1 + 1" is not a single fact.*

The expression `1 + 1` silently bundles three choices:

1. **a carrier**, the type the two ones live in;
2. **an operation**, what "+" means on that carrier;
3. **an account of occurrence**, whether the two *uses* of the symbol `1`
   are remembered as two things or forgotten as one.

Ordinary arithmetic fixes all three at once (counting, in ℕ, with tags
kept), and the answer `2` then looks like a law of nature rather than a
consequence of those choices. This file separates the choices and proves,
from first principles, what each one yields.

No Mathlib, no built-in arithmetic, no `sorry`, no user-declared axiom.
Every type and every operation is defined here, from scratch.

## What is in this file

1. **Peano naturals** (`MyNat`). Recursive addition, `1 + 1 = 2`, and the
   standard algebra (identities, successor laws, associativity,
   commutativity). `1 + 1` is neither `1` nor `0`.
2. **Coproducts, tags and the codiagonal** (`Coprod`, `Unit'`, `copair`,
   `codiag`, `Coprod.tag`). Counting is *tagging*. The two ones of
   `1 + 1` are distinguished only by tags, and forgetting the tags
   (`codiag`) collapses them to a single point. The tag is exactly the
   information that was lost.
3. **A Boolean carrier with two operations** (`bor`, `bxor`). The *same*
   inputs, `true` and `true`, give different outputs under different
   operations on one carrier. This is the honest replacement for the
   earlier one-element "idempotent union", on which every operation is
   idempotent for free.
4. **ℤ/2ℤ** (`Z2`). Addition modulo 2, its full algebra, and a proof that
   it is *the same structure* as Boolean XOR.
5. **Classification by the behaviour of `x + x`** (`Merges`, `Cancels`,
   `Keeps`). Every element of every magma falls into one of three regimes:
   it merges with itself, it cancels against itself, or it keeps its
   multiplicity. Merge and cancel are mutually exclusive away from the
   neutral element, and the classification is exhaustive.
6. **Invariance** (`merges_hom`, `cancels_hom`, `keeps_hom_inj`).
   Homomorphisms preserve the regime. Consequences: no homomorphism from
   Boolean OR to ℤ/2 can send `true` to `one`, and ℤ/2 cannot embed in
   Peano addition. These are the real theorems of the file. They say
   the different answers to `1 + 1` are *not* relabelings of one another.
7. **A table of results** (`results`, `summary`), now typed by regime
   and pointing at the theorem that witnesses each row.

## Reading guide

- Sections 1 to 4 are the four worlds, each self-contained.
- Section 5 is the common language in which the worlds are compared.
- Section 6 is the payoff: statements that hold *across* worlds.
- Notation: `+ₙ` is Peano addition, `+₂` is ℤ/2 addition. Both are
  `scoped` to their namespaces so they never collide with each other or
  with the core `+`.

## What this file does not claim

It is a statement about formally specified structures. It does not claim
that any one of them is "the" meaning of `1 + 1`, nor that the choice of
regime has consequences outside the formal setting.