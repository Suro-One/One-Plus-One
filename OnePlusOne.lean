/-!
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
-/

namespace OnePlusOne

/- ============================================================================
   1. PEANO NATURAL NUMBERS
   ============================================================================

   The counting world. Two is the successor of the successor of zero, and
   addition is defined by recursion on the second argument, so that
   `n + succ m = succ (n + m)` holds by definition (`add_succ`, `rfl`).
   Everything about `1 + 1 = 2` here is computation, not axiom. -/

/-- Peano natural numbers. -/
inductive MyNat where
  /-- Zero. -/
  | zero : MyNat
  /-- The successor of a natural number. -/
  | succ : MyNat → MyNat
  deriving Repr, DecidableEq

namespace MyNat

/-- Addition, by recursion on the second argument. -/
def add : MyNat → MyNat → MyNat
  | n, zero   => n
  | n, succ m => succ (add n m)

-- Peano addition notation, active only inside `namespace MyNat`.
scoped infixl:65 " +ₙ " => add

/-- The number one: the successor of zero. -/
def one : MyNat := succ zero

/-- The number two: the successor of one. -/
def two : MyNat := succ one

/-- The number three (for illustration). -/
def three : MyNat := succ two

/-- Adding zero on the right is the identity, by definition. -/
theorem add_zero (n : MyNat) : n +ₙ zero = n := rfl

/-- Adding a successor on the right pushes the successor outward, by
    definition. This is the defining recursion equation. -/
theorem add_succ (n m : MyNat) : n +ₙ succ m = succ (n +ₙ m) := rfl

/-- **`1 + 1 = 2`** in the Peano world, by pure computation. -/
theorem one_add_one_eq_two : one +ₙ one = two := rfl

/-- Zero is also a left identity (proved by induction; not definitional,
    because recursion is on the *second* argument). -/
theorem zero_add (n : MyNat) : zero +ₙ n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih]

/-- A successor on the left can be pulled outward. -/
theorem succ_add (n m : MyNat) : succ n +ₙ m = succ (n +ₙ m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [add_succ (succ n) m, ih, add_succ n m]

/-- Addition is associative. -/
theorem add_assoc (a b c : MyNat) : (a +ₙ b) +ₙ c = a +ₙ (b +ₙ c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [add_succ (a +ₙ b) c, add_succ b c, add_succ a (b +ₙ c), ih]

/-- Addition is commutative. -/
theorem add_comm (a b : MyNat) : a +ₙ b = b +ₙ a := by
  induction b with
  | zero => rw [add_zero, zero_add]
  | succ b ih => rw [add_succ a b, succ_add b a, ih]

/-- One is not zero. -/
theorem one_ne_zero : one ≠ zero := by decide

/-- **`1 + 1 ≠ 1`**: counting does not merge a thing with itself. -/
theorem one_add_one_ne_one : one +ₙ one ≠ one := by decide

/-- **`1 + 1 ≠ 0`**: counting does not cancel a thing against itself. -/
theorem one_add_one_ne_zero : one +ₙ one ≠ zero := by decide

/-- In Peano arithmetic the only element that cancels itself is zero.
    (Used in Section 6 to show ℤ/2 cannot embed in ℕ.) -/
theorem add_self_eq_zero {n : MyNat} (h : n +ₙ n = zero) : n = zero := by
  cases n with
  | zero => rfl
  | succ m => cases h

end MyNat

/- ============================================================================
   2. COPRODUCTS, TAGS AND THE CODIAGONAL
   ============================================================================

   The tagging world. The idea behind the whole file: the *number* 1 is one
   thing, but the *expression* `1 + 1` uses it twice. What makes the two
   uses distinct is extra structure that neither input carries, namely a
   tag. The coproduct (tagged sum, disjoint union) is the construction that
   supplies tags. Forgetting them, via the codiagonal, gives the
   set-theoretic union and collapses the two ones to a single point. -/

/-- Coproduct (disjoint union / tagged sum). The constructors `inl` and
    `inr` are the tags: they preserve *which occurrence* an element
    came from. -/
inductive Coprod (α β : Type) where
  /-- Left occurrence. -/
  | inl : α → Coprod α β
  /-- Right occurrence. -/
  | inr : β → Coprod α β
  deriving Repr, DecidableEq

/-- The one-element type. -/
inductive Unit' where
  /-- The unique inhabitant. -/
  | star : Unit'
  deriving Repr, DecidableEq

/-- Any two inhabitants of `Unit'` are equal. -/
theorem unit'_subsingleton (x y : Unit') : x = y := by
  cases x
  cases y
  rfl

/-- The first of the two tagged copies of the single element. -/
def coprodOne : Coprod Unit' Unit' := Coprod.inl Unit'.star

/-- The second of the two tagged copies of the single element. -/
def coprodTwo : Coprod Unit' Unit' := Coprod.inr Unit'.star

/-- **The two tagged copies are distinct**: counting `1 + 1` as a coproduct
    yields two elements, though the carrier has only one. -/
theorem coprod_distinct : coprodOne ≠ coprodTwo := by
  intro h
  cases h

/-- Every inhabitant of the coproduct of two singletons is one of the two
    tagged copies. Together with `coprod_distinct` this says the coproduct
    has exactly two elements. (Name kept from the first version of this
    file, where it was called `coprod_card_two`.) -/
theorem coprod_card_two :
    ∀ (x : Coprod Unit' Unit'), x = coprodOne ∨ x = coprodTwo := by
  intro x
  cases x with
  | inl a => left; rw [unit'_subsingleton a Unit'.star]; rfl
  | inr a => right; rw [unit'_subsingleton a Unit'.star]; rfl

/-- The tag of an element: `false` for the left occurrence, `true` for
    the right. -/
def Coprod.tag {α β : Type} : Coprod α β → Bool
  | Coprod.inl _ => false
  | Coprod.inr _ => true

/-- Copairing: a function out of a coproduct is determined by what it does
    on each side. -/
def copair {α β γ : Type} (f : α → γ) (g : β → γ) : Coprod α β → γ
  | Coprod.inl a => f a
  | Coprod.inr b => g b

/-- Copairing recovers the left leg. -/
theorem copair_inl {α β γ : Type} (f : α → γ) (g : β → γ) (a : α) :
    copair f g (Coprod.inl a) = f a := rfl

/-- Copairing recovers the right leg. -/
theorem copair_inr {α β γ : Type} (f : α → γ) (g : β → γ) (b : β) :
    copair f g (Coprod.inr b) = g b := rfl

/-- **Universal property** (uniqueness half): any map with the two legs
    `f` and `g` agrees pointwise with `copair f g`. This is what makes the
    coproduct *the* counting construction rather than one arbitrary
    encoding of two things. -/
theorem copair_unique {α β γ : Type} (f : α → γ) (g : β → γ)
    (h : Coprod α β → γ)
    (hl : ∀ a, h (Coprod.inl a) = f a)
    (hr : ∀ b, h (Coprod.inr b) = g b) (x : Coprod α β) :
    h x = copair f g x := by
  cases x with
  | inl a => exact hl a
  | inr b => exact hr b

/-- **Eta law**: copairing the two restrictions of `h` gives back `h`. -/
theorem copair_eta {α β γ : Type} (h : Coprod α β → γ) (x : Coprod α β) :
    copair (fun a => h (Coprod.inl a)) (fun b => h (Coprod.inr b)) x = h x := by
  cases x <;> rfl

/-- The **codiagonal**: forget the tags. Both occurrences of an element are
    sent to that element. This is the map from "counting" to "union". -/
def codiag {α : Type} : Coprod α α → α := copair id id

/-- The codiagonal sends the two tagged copies of an element to the same
    point. -/
theorem codiag_forgets {α : Type} (a : α) :
    codiag (Coprod.inl a) = codiag (Coprod.inr a) := rfl

/-- The codiagonal is onto: every element is the image of its left copy. -/
theorem codiag_surjective {α : Type} (a : α) : ∃ x, codiag x = a :=
  ⟨Coprod.inl a, rfl⟩

/-- **The tag is exactly the information lost.** The two copies of the one
    point are distinct, and the codiagonal identifies them. "Two" is "one,
    seen twice, with the seeing recorded". -/
theorem tags_are_the_information :
    coprodOne ≠ coprodTwo ∧ codiag coprodOne = codiag coprodTwo :=
  ⟨coprod_distinct, rfl⟩

/-- **Nothing else is lost.** An element of `Coprod α α` is determined by
    its image under the codiagonal together with its tag. -/
theorem codiag_tag_determines {α : Type} (x y : Coprod α α)
    (hc : codiag x = codiag y) (ht : Coprod.tag x = Coprod.tag y) : x = y := by
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Coprod.inl hc
    | inr b => cases ht          -- ht is definitionally false = true
  | inr a =>
    cases y with
    | inl b => cases ht          -- ht is definitionally true = false
    | inr b => exact congrArg Coprod.inr hc
/- ============================================================================
   3. A BOOLEAN CARRIER WITH TWO OPERATIONS
   ============================================================================

   The previous version of this file modelled idempotent union on a
   one-element type. That row was vacuous: on a one-element type every
   binary operation returns the unique element, so `x ∘ x = x` carries no
   information (see `singleton_always_merges` in Section 5).

   The honest comparison uses **one carrier and two operations**. On
   `Bool`, take `1 := true`. Then `1 + 1` is `true` under OR (merging) and
   `false` under XOR (cancelling), with identical inputs. -/

/-- Boolean OR. The idempotent, "union-like" operation. -/
def bor : Bool → Bool → Bool
  | true,  _ => true
  | false, b => b

/-- Boolean XOR. The self-cancelling operation. -/
def bxor : Bool → Bool → Bool
  | false, false => false
  | false, true  => true
  | true,  false => true
  | true,  true  => false

/-- OR is idempotent: `b ∨ b = b`. This is the *real* content of "union
    collapses duplicates". -/
theorem bor_idem (b : Bool) : bor b b = b := by
  cases b <;> rfl

/-- OR is commutative. -/
theorem bor_comm (a b : Bool) : bor a b = bor b a := by
  cases a <;> cases b <;> rfl

/-- OR is associative. -/
theorem bor_assoc (a b c : Bool) : bor (bor a b) c = bor a (bor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- XOR cancels: `b ⊕ b = false`. -/
theorem bxor_self (b : Bool) : bxor b b = false := by
  cases b <;> rfl

/-- XOR is commutative. -/
theorem bxor_comm (a b : Bool) : bxor a b = bxor b a := by
  cases a <;> cases b <;> rfl

/-- XOR is associative. -/
theorem bxor_assoc (a b c : Bool) : bxor (bxor a b) c = bxor a (bxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **Same inputs, different outputs.** With `1 := true` on a single
    carrier, `1 + 1` is `true` under OR and `false` under XOR. -/
theorem same_inputs_different_outputs : bor true true ≠ bxor true true := by
  decide

/- ============================================================================
   4. INTEGERS MODULO 2
   ============================================================================

   The cancelling world, defined directly (not as a quotient), together
   with its full elementary algebra and a proof that it is Boolean XOR under
   another name. -/

/-- Integers modulo 2. -/
inductive Z2 where
  /-- The class of even numbers. -/
  | zero : Z2
  /-- The class of odd numbers. -/
  | one  : Z2
  deriving Repr, DecidableEq

namespace Z2

/-- Addition modulo 2. -/
def add : Z2 → Z2 → Z2
  | zero, x    => x
  | one,  zero => one
  | one,  one  => zero

-- ℤ/2 addition notation, active only inside `namespace Z2`.
scoped infixl:65 " +₂ " => add

/-- **`1 + 1 = 0`** in ℤ/2. -/
theorem one_add_one_eq_zero : one +₂ one = zero := rfl

/-- Zero is a left identity (by definition). -/
theorem zero_add (x : Z2) : zero +₂ x = x := rfl

/-- Zero is a right identity. -/
theorem add_zero (x : Z2) : x +₂ zero = x := by
  cases x <;> rfl

/-- Addition is commutative. -/
theorem add_comm (a b : Z2) : a +₂ b = b +₂ a := by
  cases a <;> cases b <;> rfl

/-- Addition is associative. -/
theorem add_assoc (a b c : Z2) : (a +₂ b) +₂ c = a +₂ (b +₂ c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Every element is its own inverse: `x + x = 0`. -/
theorem add_self (x : Z2) : x +₂ x = zero := by
  cases x <;> rfl

/-- One is not zero. -/
theorem one_ne_zero : one ≠ zero := by decide

end Z2

/-- Boolean to ℤ/2: `false ↦ 0`, `true ↦ 1`. -/
def toZ2 : Bool → Z2
  | false => Z2.zero
  | true  => Z2.one

/-- ℤ/2 to Boolean: `0 ↦ false`, `1 ↦ true`. -/
def ofZ2 : Z2 → Bool
  | Z2.zero => false
  | Z2.one  => true

/-- Round trip Bool → ℤ/2 → Bool. -/
theorem ofZ2_toZ2 (b : Bool) : ofZ2 (toZ2 b) = b := by
  cases b <;> rfl

/-- Round trip ℤ/2 → Bool → ℤ/2. -/
theorem toZ2_ofZ2 (z : Z2) : toZ2 (ofZ2 z) = z := by
  cases z <;> rfl

/-- `toZ2` carries XOR to ℤ/2 addition. Together with the two round-trip
    laws this says: **ℤ/2 is Boolean XOR**, as structures. The cancelling
    world is one world seen from two sides. -/
theorem toZ2_hom (a b : Bool) :
    toZ2 (bxor a b) = Z2.add (toZ2 a) (toZ2 b) := by
  cases a <;> cases b <;> rfl

/-- `ofZ2` carries ℤ/2 addition to XOR. -/
theorem ofZ2_hom (a b : Z2) :
    ofZ2 (Z2.add a b) = bxor (ofZ2 a) (ofZ2 b) := by
  cases a <;> cases b <;> rfl

/- ============================================================================
   5. CLASSIFICATION BY THE BEHAVIOUR OF x + x
   ============================================================================

   Section 3 showed a single carrier with two behaviours for `1 + 1`. The
   general statement: for any binary operation `op`, any neutral
   candidate `z` and any element `x`, exactly one of three things happens
   when `x` is combined with itself:

   * **Merge**  : `op x x = x`    (the second occurrence is absorbed)
   * **Cancel** : `op x x = z`    (the two occurrences annihilate)
   * **Keep**   : neither         (the multiplicity survives)

   These are the three answers to the question "what happens when I add a
   thing to itself?", and they are the three faces of `1 + 1`. -/

/-- `x` merges with itself under `op`. -/
def Merges {α : Type} (op : α → α → α) (x : α) : Prop := op x x = x

/-- `x` cancels against itself under `op`, to the element `z`. -/
def Cancels {α : Type} (op : α → α → α) (z x : α) : Prop := op x x = z

/-- `x` keeps its multiplicity under `op`: it neither merges nor cancels
    (to `z`). -/
def Keeps {α : Type} (op : α → α → α) (z x : α) : Prop :=
  op x x ≠ x ∧ op x x ≠ z

/-- **Exhaustive**: every element is in at least one regime. -/
theorem trichotomy {α : Type} [DecidableEq α] (op : α → α → α) (z x : α) :
    Merges op x ∨ Cancels op z x ∨ Keeps op z x := by
  unfold Merges Cancels Keeps
  by_cases h1 : op x x = x
  · exact Or.inl h1
  · by_cases h2 : op x x = z
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- **Merge and cancel are exclusive away from the neutral element.**
    If an element both merges and cancels, it already was `z`. -/
theorem merge_cancel_exclusive {α : Type} (op : α → α → α) (z x : α)
    (h1 : Merges op x) (h2 : Cancels op z x) : x = z :=
  Eq.trans (Eq.symm h1) h2

/-- Keeping excludes merging. -/
theorem keeps_not_merges {α : Type} (op : α → α → α) (z x : α)
    (h : Keeps op z x) : ¬ Merges op x :=
  And.left h

/-- Keeping excludes cancelling. -/
theorem keeps_not_cancels {α : Type} (op : α → α → α) (z x : α)
    (h : Keeps op z x) : ¬ Cancels op z x :=
  And.right h

/-- **Why the old one-element "union" row was vacuous.** On a singleton,
    every operation merges every element, so `Merges` carries no
    information there. -/
theorem singleton_always_merges (op : Unit' → Unit' → Unit') (x : Unit') :
    Merges op x :=
  unit'_subsingleton _ _

/-- On a singleton every operation also cancels every element (to the
    unique element). Merge and cancel coincide only because `x = z`. -/
theorem singleton_always_cancels (op : Unit' → Unit' → Unit') (z x : Unit') :
    Cancels op z x :=
  unit'_subsingleton _ _

/-- **Merging instance.** In Boolean OR every element merges. -/
theorem bor_merges (b : Bool) : Merges bor b := by
  unfold Merges
  exact bor_idem b

/-- **Cancelling instance (Boolean).** In XOR, `true` cancels to `false`. -/
theorem bxor_cancels_true : Cancels bxor false true := by
  unfold Cancels
  rfl

/-- **Cancelling instance (ℤ/2).** `one` cancels to `zero`. -/
theorem z2_cancels_one : Cancels Z2.add Z2.zero Z2.one := by
  unfold Cancels
  rfl

/-- In ℤ/2, `one` does not merge. -/
theorem z2_not_merges_one : ¬ Merges Z2.add Z2.one := by
  unfold Merges
  decide

/-- **Keeping instance.** In Peano addition, `one` keeps its multiplicity:
    `1 + 1` is neither `1` nor `0`. -/
theorem nat_keeps_one : Keeps MyNat.add MyNat.zero MyNat.one := by
  unfold Keeps
  decide

/-- **The three faces of `1 + 1`**, in one statement. -/
theorem faces_of_one_plus_one :
    Merges bor true ∧
    Cancels bxor false true ∧
    Cancels Z2.add Z2.zero Z2.one ∧
    Keeps MyNat.add MyNat.zero MyNat.one :=
  ⟨bor_merges true, bxor_cancels_true, z2_cancels_one, nat_keeps_one⟩

/- ============================================================================
   6. INVARIANCE: THE REGIME IS NOT A MATTER OF LABELLING
   ============================================================================

   The classification is not merely descriptive. A homomorphism (a map
   respecting the operation) cannot change the regime of an element, so
   the three answers to `1 + 1` are *not* relabelings of one another. -/

/-- **Homomorphisms preserve merging.** -/
theorem merges_hom {α β : Type} (op : α → α → α) (op' : β → β → β)
    (f : α → β) (hf : ∀ a b, f (op a b) = op' (f a) (f b))
    (x : α) (h : Merges op x) : Merges op' (f x) :=
  Eq.trans (Eq.symm (hf x x)) (congrArg f h)

/-- **Homomorphisms preserve cancelling**, provided they send the neutral
    element to the neutral element. -/
theorem cancels_hom {α β : Type} (op : α → α → α) (op' : β → β → β)
    (f : α → β) (hf : ∀ a b, f (op a b) = op' (f a) (f b))
    (z : α) (z' : β) (hz : f z = z')
    (x : α) (h : Cancels op z x) : Cancels op' z' (f x) :=
  Eq.trans (Eq.symm (hf x x)) (Eq.trans (congrArg f h) hz)

/-- **Injective homomorphisms preserve keeping.** -/
theorem keeps_hom_inj {α β : Type} (op : α → α → α) (op' : β → β → β)
    (f : α → β) (hf : ∀ a b, f (op a b) = op' (f a) (f b))
    (hinj : ∀ a b, f a = f b → a = b)
    (z : α) (z' : β) (hz : f z = z')
    (x : α) (h : Keeps op z x) : Keeps op' z' (f x) := by
  unfold Keeps at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro h
    apply h1
    apply hinj
    exact Eq.trans (hf x x) h
  · intro h
    apply h2
    apply hinj
    exact Eq.trans (hf x x) (Eq.trans h (Eq.symm hz))

/-- **"1 + 1 = 1" and "1 + 1 = 0" are different worlds.** No homomorphism
    from Boolean OR to ℤ/2 sends `true` to `one`: `true` merges, `one`
    does not, and merging is preserved. -/
theorem no_hom_or_to_z2 (f : Bool → Z2)
    (hf : ∀ a b, f (bor a b) = Z2.add (f a) (f b)) :
    f true ≠ Z2.one := by
  intro h
  have hm : Merges Z2.add (f true) :=
    merges_hom bor Z2.add f hf true (bor_merges true)
  rw [h] at hm
  exact z2_not_merges_one hm

/-- **ℤ/2 cannot live inside counting.** Any homomorphism from ℤ/2 to Peano
    addition that sends zero to zero sends `one` to zero as well: `one`
    cancels, cancelling is preserved, and in ℕ only zero cancels. So the
    map is not injective. -/
theorem z2_collapses_in_nat (f : Z2 → MyNat)
    (hf : ∀ a b, f (Z2.add a b) = MyNat.add (f a) (f b))
    (hz : f Z2.zero = MyNat.zero) : f Z2.one = f Z2.zero := by
  have hc : Cancels MyNat.add MyNat.zero (f Z2.one) :=
    cancels_hom Z2.add MyNat.add f hf Z2.zero MyNat.zero hz Z2.one z2_cancels_one
  rw [hz]
  exact MyNat.add_self_eq_zero hc

/-- The same conclusion as an explicit non-injectivity statement. -/
theorem z2_not_injective_in_nat (f : Z2 → MyNat)
    (hf : ∀ a b, f (Z2.add a b) = MyNat.add (f a) (f b))
    (hz : f Z2.zero = MyNat.zero) : ¬ (∀ a b, f a = f b → a = b) := by
  intro hinj
  have h := z2_collapses_in_nat f hf hz
  exact Z2.one_ne_zero (hinj Z2.one Z2.zero h)

/- ============================================================================
   7. TABLE OF RESULTS
   ============================================================================

   A typed summary. Each row names its regime and the theorem that
   witnesses it. The strings are commentary; the theorems are the content. -/

/-- The three regimes of Section 5, as data. -/
inductive Rule where
  /-- `x + x = x`. -/
  | merge
  /-- `x + x = 0`. -/
  | cancel
  /-- `x + x` is neither `x` nor `0`. -/
  | keep
  deriving Repr, DecidableEq

/-- Human-readable name of a regime. -/
def Rule.label : Rule → String
  | Rule.merge  => "merge"
  | Rule.cancel => "cancel"
  | Rule.keep   => "keep"

/-- One row of the summary table. -/
structure OnePlusOneResult where
  /-- Name of the structure and operation. -/
  name : String
  /-- Result of `1 ⊕ 1`. -/
  result : String
  /-- Which regime this row exhibits. -/
  rule : Rule
  /-- Name of the Lean theorem witnessing the row. -/
  witness : String
  /-- Short explanation. -/
  explanation : String

/-- The table. -/
def results : List OnePlusOneResult :=
  [ { name := "Peano ℕ (counting)"
      result := "2"
      rule := Rule.keep
      witness := "MyNat.one_add_one_eq_two, nat_keeps_one"
      explanation := "Recursive successor preserves multiplicity" }
  , { name := "Coproduct (tagged sum)"
      result := "2 distinct elements"
      rule := Rule.keep
      witness := "coprod_distinct, coprod_card_two"
      explanation := "Constructors inl/inr supply the tags" }
  , { name := "Bool with OR (union-like)"
      result := "1"
      rule := Rule.merge
      witness := "bor_merges"
      explanation := "Idempotent: the second occurrence is absorbed" }
  , { name := "Bool with XOR"
      result := "0"
      rule := Rule.cancel
      witness := "bxor_cancels_true"
      explanation := "Self-cancelling: occurrences annihilate" }
  , { name := "ℤ/2ℤ"
      result := "0"
      rule := Rule.cancel
      witness := "z2_cancels_one, toZ2_hom"
      explanation := "The same structure as XOR (see toZ2_hom, ofZ2_hom)" }
  ]

/-- Render one row. -/
def OnePlusOneResult.render (r : OnePlusOneResult) : String :=
  s!"{r.name}: 1 ⊕ 1 = {r.result}  [{r.rule.label}]\n  ({r.explanation})\n  witness: {r.witness}\n"

/-- Pretty-print the table (for `#eval`). -/
def summary : String :=
  String.join (results.map OnePlusOneResult.render)

#eval summary

end OnePlusOne

/-
  ================================================================
  LEDGER: what kind of claim each part of this file is.

  DEFINITIONS : MyNat, Unit', Coprod, Coprod.tag, copair, codiag,
                bor, bxor, Z2, toZ2, ofZ2, Merges, Cancels, Keeps,
                Rule, OnePlusOneResult, results, summary.
  THEOREMS    : everything named `theorem`, all proved, no `sorry`.
  AXIOMS      : none declared in this file.
  CONJECTURES : none.

  KEY RESULTS
    one_add_one_eq_two            1 + 1 = 2 in counting
    tags_are_the_information      two is one seen twice, tag recorded
    codiag_tag_determines         tag + collapse recovers everything
    same_inputs_different_outputs one carrier, two operations
    toZ2_hom, ofZ2_hom            ℤ/2 is XOR
    trichotomy                    merge / cancel / keep is exhaustive
    merge_cancel_exclusive        and exclusive away from neutral
    faces_of_one_plus_one         the three faces in one statement
    no_hom_or_to_z2               OR cannot map to ℤ/2 with true ↦ one
    z2_collapses_in_nat           ℤ/2 cannot embed in counting

  INTERPRETATION: these are statements about formally specified
  structures. They do not select a "correct" meaning of 1 + 1.
  ================================================================
-/

#print axioms OnePlusOne.faces_of_one_plus_one
#print axioms OnePlusOne.no_hom_or_to_z2
#print axioms OnePlusOne.z2_collapses_in_nat
#print axioms OnePlusOne.codiag_tag_determines