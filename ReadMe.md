# One Plus One

### A small Lean 4 formalization of what an expression like `1 + 1` leaves implicit

`1 + 1 = 2` is familiar enough to look inevitable. But the expression only has a definite result after some structure has been chosen: a type of values, a binary operation on those values, and—when we are counting occurrences—a decision about whether two appearances of the same value remain distinguishable.

This project makes those choices explicit and proves what follows from each one. It develops several tiny mathematical worlds from first principles, then compares them using homomorphisms. The result is not a claim that ordinary arithmetic is arbitrary. It is a demonstration that the result of combining two equal inputs depends on the structure in which the combination is interpreted.

> **Central idea:** the behaviour of `x ⊕ x` is structural. It can merge, cancel, or preserve multiplicity, and structure-preserving maps cannot freely turn one behaviour into another.

---

## At a glance

| Structure | Chosen value | Operation | Self-combination | Behaviour |
|---|---:|---|---:|---|
| Peano naturals | `one` | recursive addition | `two` | Keep |
| Boolean carrier | `true` | OR | `true` | Merge |
| Boolean carrier | `true` | XOR | `false` | Cancel |
| Two-element `Z2` | `one` | addition modulo two | `zero` | Cancel |
| Coproduct of two singletons | the unique value in each summand | tagged disjoint union | two distinct tagged elements | Preserve tags |

The coproduct row is deliberately described separately from the three operation regimes: it is a construction for keeping occurrences distinct, not an example of a binary operation `op` evaluated at `x` twice.

## What is formalized

Everything lives in the `OnePlusOne` namespace in [`OnePlusOne.lean`](OnePlusOne.lean).

### 1. Counting: Peano naturals

`MyNat` is defined with only two constructors:

- `zero`
- `succ n`

Addition is recursive on its second argument. The file proves the defining successor equations, the left and right identity laws, associativity, and commutativity. It then establishes:

```lean
OnePlusOne.MyNat.one_add_one_eq_two
OnePlusOne.MyNat.one_add_one_ne_one
OnePlusOne.MyNat.one_add_one_ne_zero
```

The key point is that the result `two` is obtained by computation from the recursive definition. No arithmetic library or natural-number theorem is imported to establish it.

### 2. Occurrences: coproducts, tags, and counting

`Coprod α β` is a disjoint union with constructors `inl` and `inr`. The constructor records which summand an element came from. Consequently, the two copies of the unique element in `Coprod Unit' Unit'` are different:

```lean
coprodOne ≠ coprodTwo
```

The `codiag` map forgets the tags. It sends both copies to the same underlying value. The theorem `codiag_tag_determines` proves the complementary fact: the codiagonal image together with the tag is enough to reconstruct the original coproduct element.

The file also makes the counting connection explicit rather than relying only on the fact that the two constructors are distinct:

1. `MyList` is a small list type whose length is measured using the custom `MyNat`.
2. `length_append` proves that concatenating two finite lists adds their lengths.
3. Each singleton summand receives a one-element enumeration.
4. Those enumerations are mapped into the coproduct, retaining their respective tags, and concatenated.
5. The resulting enumeration has length `MyNat.two`.

The central results are:

```lean
coprodEnumeration_explicit
coprodCard_eq_sum_of_component_lengths
coprodEnumeration_length
coprodCard_eq_twoSingletonCardSum
```

This is a concrete finite-counting argument for this coproduct. It is not an implementation of general cardinal arithmetic or a theorem about arbitrary infinite coproducts.

### 3. One carrier, two operations: Boolean OR and XOR

Both operations act on `Bool`, with `true` chosen as the value represented by `1`.

- Under `bor`, `true` combined with itself is `true`. The operation is idempotent: a duplicate is absorbed.
- Under `bxor`, `true` combined with itself is `false`. The equal inputs cancel.

The file proves commutativity and associativity for both operations, along with OR idempotence and XOR self-cancellation. In particular, `same_inputs_different_outputs` establishes that the same carrier and same inputs can produce different outputs when the operation changes.

### 4. The two-element additive structure `Z2`

`Z2` is defined directly with `zero` and `one`; its addition table is defined by pattern matching. The file proves the additive identity laws, commutativity, associativity, and self-cancellation:

```lean
OnePlusOne.Z2.one_add_one_eq_zero
OnePlusOne.Z2.add_self
```

It then defines maps in both directions between `Bool` and `Z2`. The two round-trip theorems show that these maps are inverses, while `toZ2_hom` and `ofZ2_hom` show that they preserve the operations. Thus Boolean XOR and this additive `Z2` structure are isomorphic as the explicitly defined binary-operation structures.

**Scope note:** this file formalizes the additive structure of `Z2`. It does not define multiplication or prove that `Z2` is a field.

### 5. A general classification of `x op x`

For an arbitrary type `α`, binary operation `op`, designated comparison value `z`, and element `x`, the file defines three predicates:

| Predicate | Definition | Interpretation |
|---|---|---|
| `Merges op x` | `op x x = x` | The second occurrence is absorbed. |
| `Cancels op z x` | `op x x = z` | The two occurrences produce the designated value. |
| `Keeps op z x` | `op x x ≠ x ∧ op x x ≠ z` | The result is neither the original value nor the designated value. |

`trichotomy` proves that at least one of these predicates holds for every `op`, `z`, and `x` (assuming decidable equality so Lean can split the equality tests). This result requires no associativity, commutativity, or identity law.

There is one important edge case: merge and cancel can both hold when `x = z`. The file states this accurately rather than claiming unconditional mutual exclusivity. `exactly_one_regime` proves that precisely one regime holds whenever `x ≠ z`.

The examples are collected in `faces_of_one_plus_one`:

- Boolean OR merges `true`.
- Boolean XOR cancels `true` to `false`.
- `Z2` addition cancels `one` to `zero`.
- Peano addition keeps the multiplicity of `one`: its double is neither `one` nor `zero`.

The singleton results, `singleton_always_merges` and `singleton_always_cancels`, explain why a one-element carrier cannot distinguish these behaviours: every value is equal to the only possible result.

### 6. Invariance under homomorphisms

The comparison becomes stronger when maps between structures are considered. A homomorphism preserves the operation, so it must preserve the relevant self-combination behaviour:

- `merges_hom`: homomorphisms preserve merging.
- `cancels_hom`: homomorphisms preserve cancellation when the designated value is mapped to the designated value in the target.
- `keeps_hom_inj`: injective homomorphisms preserve keeping multiplicity.

These general lemmas support two concrete non-existence/collapse results:

**OR cannot send `true` to `Z2.one`.** `no_hom_or_to_z2` proves that no homomorphism from Boolean OR to `Z2` addition can map the merging value `true` to the non-merging value `one`.

**A zero-preserving homomorphism from `Z2` to Peano addition collapses the two elements.** `z2_collapses_in_nat` proves that such a map sends `one` to `zero`; `z2_not_injective_in_nat` then proves that it cannot be injective.

These statements are about the specified operations and the stated homomorphism conditions. They are not claims about arbitrary functions between the underlying types.

## The summary generated by Lean

At the end of the file, `results` stores a typed summary table. Each row includes a name, displayed result, category, theorem witness, and explanation. `Rule` has four constructors:

- `merge`
- `cancel`
- `keep`
- `tagged`

The separate `tagged` category is intentional: it prevents the coproduct example from being misreported as a magma whose self-combination preserves multiplicity.

The declaration `summary` renders the table as text, and:

```lean
#eval OnePlusOne.summary
```

prints it when the file is compiled or evaluated.

---

## Running the file

### Requirements

- Lean 4.
- No Mathlib dependency.
- No third-party package dependency.

The file uses Lean's standard core environment and tactics, but it does not import Mathlib or declare any additional project dependencies.

### Run directly

From the directory containing `OnePlusOne.lean`:

```bash
lean OnePlusOne.lean
```

If you are working inside an existing Lake project, run it in that project's environment:

```bash
lake env lean OnePlusOne.lean
```

The file includes `#eval summary` and several `#print axioms` commands. Lean will therefore both evaluate the summary and display the axiom dependencies of selected theorems as part of processing the file.

### Axiom audit

The source declares no `axiom` constants and contains no `sorry`. At the end, it asks Lean to print the dependencies of representative results, including:

```lean
#print axioms OnePlusOne.faces_of_one_plus_one
#print axioms OnePlusOne.no_hom_or_to_z2
#print axioms OnePlusOne.z2_collapses_in_nat
#print axioms OnePlusOne.codiag_tag_determines
#print axioms OnePlusOne.coprodCard_eq_twoSingletonCardSum
#print axioms OnePlusOne.exactly_one_regime
```

These commands are useful because a source-level search for the words `axiom` or `sorry` is not a substitute for checking a theorem's actual dependency list. Inspect Lean's output to see which foundational declarations, if any, a result depends on.

---

## Main theorem map

| Topic | Main declarations |
|---|---|
| Peano arithmetic | `MyNat.one_add_one_eq_two`, `MyNat.add_assoc`, `MyNat.add_comm` |
| Distinct tagged occurrences | `coprod_distinct`, `coprod_card_two`, `tags_are_the_information` |
| Recovering tagged data | `codiag_tag_determines` |
| Coproduct counting | `MyList.length_append`, `coprodCard_eq_sum_of_component_lengths`, `coprodEnumeration_length`, `coprodCard_eq_twoSingletonCardSum` |
| Different Boolean operations | `bor_idem`, `bxor_self`, `same_inputs_different_outputs` |
| XOR and `Z2` | `toZ2_hom`, `ofZ2_hom`, `ofZ2_toZ2`, `toZ2_ofZ2` |
| Regime classification | `trichotomy`, `merge_cancel_exclusive`, `exactly_one_regime`, `faces_of_one_plus_one` |
| Homomorphism invariance | `merges_hom`, `cancels_hom`, `keeps_hom_inj` |
| Structural separation | `no_hom_or_to_z2`, `z2_collapses_in_nat`, `z2_not_injective_in_nat` |

---

## What this project does not claim

The formalization is intentionally modest about its interpretation.

- It does **not** claim that ordinary arithmetic is subjective or that the usual natural-number interpretation is optional once its structure has been fixed.
- It does **not** claim that every use of the symbol `1` in mathematics denotes the same kind of object.
- It does **not** identify a coproduct with a numerical sum without specifying how its finite elements are enumerated and counted.
- It does **not** classify every possible algebraic structure beyond the particular question of how a chosen element behaves under `op x x` relative to `x` and a designated `z`.
- It does **not** formalize the full theory of sets, cardinal numbers, groups, rings, or fields.

What it does prove is precise: once the carrier, operation, and relevant occurrence information are specified, the resulting equations and structural constraints can be derived—and some of those behaviours cannot be transformed into others by homomorphisms satisfying the stated conditions.

## Project structure

```text
.
├── OnePlusOne.lean   # Complete self-contained Lean 4 development
└── README.md         # Project overview, theorem guide, and run instructions
```


*The point is not that `1 + 1` has no answer. The point is that an answer belongs to a structure—and the structure tells us why that answer is the one we get.*
