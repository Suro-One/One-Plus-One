/-!
# One Plus One

*Formalization of why `1 + 1` is not a single fact.*

The expression `1 + 1` silently bundles three choices:

1. **A carrier:** the type in which the two inputs live.
2. **An operation:** what `+` means on that carrier.
3. **An account of occurrence:** whether two uses of the same value are
   distinguished by tags or identified when the tags are forgotten.

This file separates those choices. It defines its own Peano naturals,
finite lists, coproduct, Boolean operations, and two-element additive group.
It uses no Mathlib, imports no modules, declares no axioms, and contains no
`sorry`.

The comparison is structural, not merely numerical. In particular,
homomorphisms preserve merging and cancellation, while injective
homomorphisms preserve keeping multiplicity. The coproduct construction is
also connected to Peano addition by explicitly enumerating its two tagged
elements and counting that enumeration.

## Scope

The file proves facts about the structures defined below. It does not claim
that one structure is the uniquely correct interpretation of `1 + 1` in
every context.
-/

namespace OnePlusOne

/- ========================================================================== 
   1. PEANO NATURAL NUMBERS
   ========================================================================== -/

/-- Peano natural numbers. -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
  deriving Repr, DecidableEq

namespace MyNat

/-- Addition, recursively defined on the second argument. -/
def add : MyNat → MyNat → MyNat
  | n, zero   => n
  | n, succ m => succ (add n m)

scoped infixl:65 " +ₙ " => add

/-- One, the successor of zero. -/
def one : MyNat := succ zero

/-- Two, the successor of one. -/
def two : MyNat := succ one

/-- Three, for illustration. -/
def three : MyNat := succ two

theorem add_zero (n : MyNat) : n +ₙ zero = n := rfl

theorem add_succ (n m : MyNat) : n +ₙ succ m = succ (n +ₙ m) := rfl

/-- In the Peano counting structure, `1 + 1 = 2` by computation. -/
theorem one_add_one_eq_two : one +ₙ one = two := rfl

theorem zero_add (n : MyNat) : zero +ₙ n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add_succ, ih]

theorem succ_add (n m : MyNat) : succ n +ₙ m = succ (n +ₙ m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [add_succ (succ n) m, ih, add_succ n m]

theorem add_assoc (a b c : MyNat) :
    (a +ₙ b) +ₙ c = a +ₙ (b +ₙ c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [add_succ (a +ₙ b) c, add_succ b c,
        add_succ a (b +ₙ c), ih]

theorem add_comm (a b : MyNat) : a +ₙ b = b +ₙ a := by
  induction b with
  | zero => rw [add_zero, zero_add]
  | succ b ih => rw [add_succ a b, succ_add b a, ih]

theorem one_ne_zero : one ≠ zero := by
  decide

theorem one_add_one_ne_one : one +ₙ one ≠ one := by
  decide

theorem one_add_one_ne_zero : one +ₙ one ≠ zero := by
  decide

/-- Only zero can add to itself to produce zero in Peano addition. -/
theorem add_self_eq_zero {n : MyNat} (h : n +ₙ n = zero) : n = zero := by
  cases n with
  | zero => rfl
  | succ m => cases h

end MyNat

/- ========================================================================== 
   2. FINITE ENUMERATIONS, COPRODUCTS, TAGS, AND THE CODIAGONAL
   ========================================================================== -/

/-- A minimal list type whose length is measured in the Peano naturals above. -/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

namespace MyList

/-- Length of a finite list, valued in our own Peano naturals. -/
def length : MyList α → MyNat
  | nil => MyNat.zero
  | cons _ xs => MyNat.succ (length xs)

/-- Map a function over a finite list. -/
def map (f : α → β) : MyList α → MyList β
  | nil => nil
  | cons a xs => cons (f a) (map f xs)

/-- Concatenate two finite lists. -/
def append : MyList α → MyList α → MyList α
  | nil, ys => ys
  | cons a xs, ys => cons a (append xs ys)

/-- Mapping does not change the length of a finite list. -/
theorem length_map (f : α → β) (xs : MyList α) :
    length (map f xs) = length xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change MyNat.succ (length (map f xs)) = MyNat.succ (length xs)
    exact congrArg MyNat.succ ih

/-- The length of a concatenation is the Peano sum of the two lengths. -/
theorem length_append (xs ys : MyList α) :
    length (append xs ys) = MyNat.add (length xs) (length ys) := by
  induction xs with
  | nil => exact (MyNat.zero_add (length ys)).symm
  | cons a xs ih =>
    change MyNat.succ (length (append xs ys)) =
      MyNat.add (MyNat.succ (length xs)) (length ys)
    exact Eq.trans (congrArg MyNat.succ ih)
      (Eq.symm (MyNat.succ_add (length xs) (length ys)))

end MyList

/-- A coproduct (disjoint union / tagged sum). -/
inductive Coprod (α β : Type) where
  | inl : α → Coprod α β
  | inr : β → Coprod α β
  deriving Repr, DecidableEq

/-- The one-element type, defined independently of Lean's `Unit`. -/
inductive Unit' where
  | star : Unit'
  deriving Repr, DecidableEq

theorem unit'_subsingleton (x y : Unit') : x = y := by
  cases x
  cases y
  rfl

/-- The two tagged copies of the unique element. -/
def coprodOne : Coprod Unit' Unit' := Coprod.inl Unit'.star

def coprodTwo : Coprod Unit' Unit' := Coprod.inr Unit'.star

/-- The two tagged occurrences are distinct. -/
theorem coprod_distinct : coprodOne ≠ coprodTwo := by
  intro h
  cases h

/-- Every element of the coproduct of two singletons is one of these copies. -/
theorem coprod_card_two :
    ∀ x : Coprod Unit' Unit', x = coprodOne ∨ x = coprodTwo := by
  intro x
  cases x with
  | inl a =>
    left
    rw [unit'_subsingleton a Unit'.star]
    rfl
  | inr a =>
    right
    rw [unit'_subsingleton a Unit'.star]
    rfl

/-- The tag records which side of the coproduct an element came from. -/
def Coprod.tag {α β : Type} : Coprod α β → Bool
  | Coprod.inl _ => false
  | Coprod.inr _ => true

/-- Copairing: define a map out of a coproduct by giving its two legs. -/
def copair {α β γ : Type} (f : α → γ) (g : β → γ) : Coprod α β → γ
  | Coprod.inl a => f a
  | Coprod.inr b => g b

theorem copair_inl {α β γ : Type} (f : α → γ) (g : β → γ) (a : α) :
    copair f g (Coprod.inl a) = f a := rfl

theorem copair_inr {α β γ : Type} (f : α → γ) (g : β → γ) (b : β) :
    copair f g (Coprod.inr b) = g b := rfl

/-- The uniqueness half of the coproduct universal property. -/
theorem copair_unique {α β γ : Type} (f : α → γ) (g : β → γ)
    (h : Coprod α β → γ)
    (hl : ∀ a, h (Coprod.inl a) = f a)
    (hr : ∀ b, h (Coprod.inr b) = g b) (x : Coprod α β) :
    h x = copair f g x := by
  cases x with
  | inl a => exact hl a
  | inr b => exact hr b

theorem copair_eta {α β γ : Type} (h : Coprod α β → γ) (x : Coprod α β) :
    copair (fun a => h (Coprod.inl a)) (fun b => h (Coprod.inr b)) x = h x := by
  cases x <;> rfl

/-- The codiagonal forgets the tags by identifying both copies. -/
def codiag {α : Type} : Coprod α α → α := copair id id

theorem codiag_forgets {α : Type} (a : α) :
    codiag (Coprod.inl a) = codiag (Coprod.inr a) := rfl

theorem codiag_surjective {α : Type} (a : α) : ∃ x, codiag x = a :=
  ⟨Coprod.inl a, rfl⟩

/-- The tags are distinct before applying the codiagonal and identified after. -/
theorem tags_are_the_information :
    coprodOne ≠ coprodTwo ∧ codiag coprodOne = codiag coprodTwo :=
  ⟨coprod_distinct, rfl⟩

/-- The codiagonal image together with the tag determines the original value. -/
theorem codiag_tag_determines {α : Type} (x y : Coprod α α)
    (hc : codiag x = codiag y) (ht : Coprod.tag x = Coprod.tag y) : x = y := by
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Coprod.inl hc
    | inr b => cases ht
  | inr a =>
    cases y with
    | inl b => cases ht
    | inr b => exact congrArg Coprod.inr hc

/-- A two-valued index type used to enumerate the coproduct. -/
inductive TwoIndex where
  | left
  | right
  deriving Repr, DecidableEq

/-- Turn an index into its corresponding tagged singleton. -/
def TwoIndex.toCoprod : TwoIndex → Coprod Unit' Unit'
  | TwoIndex.left => coprodOne
  | TwoIndex.right => coprodTwo

/-- Recover the index from a tagged singleton. -/
def Coprod.toTwoIndex : Coprod Unit' Unit' → TwoIndex
  | Coprod.inl _ => TwoIndex.left
  | Coprod.inr _ => TwoIndex.right

theorem toTwoIndex_toCoprod (i : TwoIndex) :
    Coprod.toTwoIndex (TwoIndex.toCoprod i) = i := by
  cases i <;> rfl

theorem toCoprod_toTwoIndex (x : Coprod Unit' Unit') :
    TwoIndex.toCoprod (Coprod.toTwoIndex x) = x := by
  cases x with
  | inl a => cases a; rfl
  | inr a => cases a; rfl

/-- The explicit enumeration of the two possible indices. -/
def twoIndexEnumeration : MyList TwoIndex :=
  MyList.cons TwoIndex.left (MyList.cons TwoIndex.right MyList.nil)

theorem twoIndexEnumeration_covers (i : TwoIndex) :
    i = TwoIndex.left ∨ i = TwoIndex.right := by
  cases i with
  | left => exact Or.inl rfl
  | right => exact Or.inr rfl

theorem twoIndex_entries_distinct : TwoIndex.left ≠ TwoIndex.right := by
  decide

theorem twoIndexEnumeration_length :
    MyList.length twoIndexEnumeration = MyNat.two := rfl

/-- A one-entry enumeration of the left singleton summand. -/
def leftSingletonEnumeration : MyList Unit' :=
  MyList.cons Unit'.star MyList.nil

/-- A one-entry enumeration of the right singleton summand. -/
def rightSingletonEnumeration : MyList Unit' :=
  MyList.cons Unit'.star MyList.nil

theorem leftSingletonEnumeration_length :
    MyList.length leftSingletonEnumeration = MyNat.one := rfl

theorem rightSingletonEnumeration_length :
    MyList.length rightSingletonEnumeration = MyNat.one := rfl

/-- Enumerate the left summand after adding its coproduct tag. -/
def leftCoprodEnumeration : MyList (Coprod Unit' Unit') :=
  MyList.map Coprod.inl leftSingletonEnumeration

/-- Enumerate the right summand after adding its coproduct tag. -/
def rightCoprodEnumeration : MyList (Coprod Unit' Unit') :=
  MyList.map Coprod.inr rightSingletonEnumeration

/-- The finite enumeration of the coproduct is the concatenation of the
    separately tagged enumerations of its two summands. -/
def coprodEnumeration : MyList (Coprod Unit' Unit') :=
  MyList.append leftCoprodEnumeration rightCoprodEnumeration

theorem coprodEnumeration_explicit :
    coprodEnumeration =
      MyList.cons coprodOne (MyList.cons coprodTwo MyList.nil) := rfl

/-- The coproduct's cardinality is the length of this enumeration. -/
def coprodCard : MyNat := MyList.length coprodEnumeration

/-- **Coproduct cardinality is additive:** the enumeration length is the
    Peano sum of the lengths of the two component enumerations. -/
theorem coprodCard_eq_sum_of_component_lengths :
    coprodCard = MyNat.add
      (MyList.length leftSingletonEnumeration)
      (MyList.length rightSingletonEnumeration) := by
  calc
    coprodCard = MyNat.add
        (MyList.length leftCoprodEnumeration)
        (MyList.length rightCoprodEnumeration) := by
      unfold coprodCard coprodEnumeration
      exact MyList.length_append leftCoprodEnumeration rightCoprodEnumeration
    _ = MyNat.add
        (MyList.length leftSingletonEnumeration)
        (MyList.length rightSingletonEnumeration) := by
      unfold leftCoprodEnumeration rightCoprodEnumeration
      simp only [MyList.length_map]

theorem coprodEnumeration_length : coprodCard = MyNat.two := by
  calc
    coprodCard = MyNat.add
        (MyList.length leftSingletonEnumeration)
        (MyList.length rightSingletonEnumeration) :=
      coprodCard_eq_sum_of_component_lengths
    _ = MyNat.add MyNat.one MyNat.one := by
      rw [leftSingletonEnumeration_length, rightSingletonEnumeration_length]
    _ = MyNat.two := MyNat.one_add_one_eq_two

theorem coprodEnumeration_covers (x : Coprod Unit' Unit') :
    x = coprodOne ∨ x = coprodTwo :=
  coprod_card_two x

theorem coprodEnumeration_entries_distinct : coprodOne ≠ coprodTwo :=
  coprod_distinct

/-- The cardinality of one singleton is one. -/
def singletonCard : MyNat := MyNat.one

/-- The sum of the cardinalities of two singleton summands. -/
def twoSingletonCardSum : MyNat :=
  MyNat.add singletonCard singletonCard

/-- **Finite coproduct cardinality agrees with Peano addition:**
    the two tagged singleton summands have cardinality `1 + 1 = 2`. -/
theorem coprodCard_eq_twoSingletonCardSum :
    coprodCard = twoSingletonCardSum := by
  calc
    coprodCard = MyNat.add
        (MyList.length leftSingletonEnumeration)
        (MyList.length rightSingletonEnumeration) :=
      coprodCard_eq_sum_of_component_lengths
    _ = twoSingletonCardSum := by
      rw [leftSingletonEnumeration_length, rightSingletonEnumeration_length]
      rfl

/- ========================================================================== 
   3. ONE BOOLEAN CARRIER, TWO DIFFERENT OPERATIONS
   ========================================================================== -/

/-- Boolean OR, an idempotent union-like operation. -/
def bor : Bool → Bool → Bool
  | true,  _ => true
  | false, b => b

/-- Boolean XOR, a self-cancelling operation. -/
def bxor : Bool → Bool → Bool
  | false, false => false
  | false, true  => true
  | true,  false => true
  | true,  true  => false

theorem bor_idem (b : Bool) : bor b b = b := by
  cases b <;> rfl

theorem bor_comm (a b : Bool) : bor a b = bor b a := by
  cases a <;> cases b <;> rfl

theorem bor_assoc (a b c : Bool) :
    bor (bor a b) c = bor a (bor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bxor_self (b : Bool) : bxor b b = false := by
  cases b <;> rfl

theorem bxor_comm (a b : Bool) : bxor a b = bxor b a := by
  cases a <;> cases b <;> rfl

theorem bxor_assoc (a b c : Bool) :
    bxor (bxor a b) c = bxor a (bxor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The same Boolean inputs produce different outputs under OR and XOR. -/
theorem same_inputs_different_outputs : bor true true ≠ bxor true true := by
  decide

/- ========================================================================== 
   4. THE ADDITIVE STRUCTURE Z/2Z AND ITS IDENTIFICATION WITH XOR
   ========================================================================== -/

/-- The two residue classes modulo two, defined directly. -/
inductive Z2 where
  | zero : Z2
  | one  : Z2
  deriving Repr, DecidableEq

namespace Z2

/-- Addition modulo two. -/
def add : Z2 → Z2 → Z2
  | zero, x    => x
  | one,  zero => one
  | one,  one  => zero

scoped infixl:65 " +₂ " => add

theorem one_add_one_eq_zero : one +₂ one = zero := rfl

theorem zero_add (x : Z2) : zero +₂ x = x := rfl

theorem add_zero (x : Z2) : x +₂ zero = x := by
  cases x <;> rfl

theorem add_comm (a b : Z2) : a +₂ b = b +₂ a := by
  cases a <;> cases b <;> rfl

theorem add_assoc (a b c : Z2) :
    (a +₂ b) +₂ c = a +₂ (b +₂ c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem add_self (x : Z2) : x +₂ x = zero := by
  cases x <;> rfl

theorem one_ne_zero : one ≠ zero := by
  decide

end Z2

/-- Boolean false/true mapped to the two residue classes. -/
def toZ2 : Bool → Z2
  | false => Z2.zero
  | true  => Z2.one

/-- The inverse map from the two residue classes to Boolean values. -/
def ofZ2 : Z2 → Bool
  | Z2.zero => false
  | Z2.one  => true

theorem ofZ2_toZ2 (b : Bool) : ofZ2 (toZ2 b) = b := by
  cases b <;> rfl

theorem toZ2_ofZ2 (z : Z2) : toZ2 (ofZ2 z) = z := by
  cases z <;> rfl

/-- `toZ2` preserves the binary operation: XOR corresponds to addition mod 2. -/
theorem toZ2_hom (a b : Bool) :
    toZ2 (bxor a b) = Z2.add (toZ2 a) (toZ2 b) := by
  cases a <;> cases b <;> rfl

theorem ofZ2_hom (a b : Z2) :
    ofZ2 (Z2.add a b) = bxor (ofZ2 a) (ofZ2 b) := by
  cases a <;> cases b <;> rfl

/- ========================================================================== 
   5. CLASSIFICATION BY THE BEHAVIOUR OF x OP x
   ========================================================================== -/

/-- `x` merges with itself under `op`. -/
def Merges {α : Type} (op : α → α → α) (x : α) : Prop :=
  op x x = x

/-- `x` cancels against itself to the designated element `z`. -/
def Cancels {α : Type} (op : α → α → α) (z x : α) : Prop :=
  op x x = z

/-- `x` keeps its multiplicity: the result is neither `x` nor `z`. -/
def Keeps {α : Type} (op : α → α → α) (z x : α) : Prop :=
  op x x ≠ x ∧ op x x ≠ z

/-- Every binary operation, element, and designated `z` falls into at least
    one of the three predicates. No associativity or identity law is needed. -/
theorem trichotomy {α : Type} [DecidableEq α]
    (op : α → α → α) (z x : α) :
    Merges op x ∨ Cancels op z x ∨ Keeps op z x := by
  unfold Merges Cancels Keeps
  by_cases h1 : op x x = x
  · exact Or.inl h1
  · by_cases h2 : op x x = z
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- If an element both merges and cancels, it must equal the designated `z`. -/
theorem merge_cancel_exclusive {α : Type} (op : α → α → α)
    (z x : α) (hm : Merges op x) (hc : Cancels op z x) : x = z :=
  Eq.trans (Eq.symm hm) hc

theorem merge_not_cancel_of_ne {α : Type} (op : α → α → α)
    (z x : α) (hne : x ≠ z) (hm : Merges op x) :
    ¬ Cancels op z x := by
  intro hc
  exact hne (merge_cancel_exclusive op z x hm hc)

theorem cancel_not_merge_of_ne {α : Type} (op : α → α → α)
    (z x : α) (hne : x ≠ z) (hc : Cancels op z x) :
    ¬ Merges op x := by
  intro hm
  exact hne (merge_cancel_exclusive op z x hm hc)

theorem keeps_not_merges {α : Type} (op : α → α → α)
    (z x : α) (h : Keeps op z x) : ¬ Merges op x :=
  And.left h

theorem keeps_not_cancels {α : Type} (op : α → α → α)
    (z x : α) (h : Keeps op z x) : ¬ Cancels op z x :=
  And.right h

/-- **Exact classification away from `z`.** When `x ≠ z`, exactly one of
    merge, cancel, and keep holds. At `x = z`, merge and cancel may overlap. -/
theorem exactly_one_regime {α : Type} [DecidableEq α]
    (op : α → α → α) (z x : α) (hne : x ≠ z) :
    (Merges op x ∧ ¬ Cancels op z x ∧ ¬ Keeps op z x) ∨
    (Cancels op z x ∧ ¬ Merges op x ∧ ¬ Keeps op z x) ∨
    (Keeps op z x ∧ ¬ Merges op x ∧ ¬ Cancels op z x) := by
  rcases trichotomy op z x with hm | hc | hk
  · exact Or.inl ⟨hm,
      merge_not_cancel_of_ne op z x hne hm,
      (fun hkeep => keeps_not_merges op z x hkeep hm)⟩
  · exact Or.inr (Or.inl ⟨hc,
      cancel_not_merge_of_ne op z x hne hc,
      (fun hkeep => keeps_not_cancels op z x hkeep hc)⟩)
  · exact Or.inr (Or.inr ⟨hk,
      keeps_not_merges op z x hk,
      keeps_not_cancels op z x hk⟩)

/-- On a singleton, every operation merges the unique element. -/
theorem singleton_always_merges
    (op : Unit' → Unit' → Unit') (x : Unit') : Merges op x :=
  unit'_subsingleton _ _

/-- On a singleton, every operation also cancels to the unique element.
    The two predicates overlap because every pair of elements is equal. -/
theorem singleton_always_cancels
    (op : Unit' → Unit' → Unit') (z x : Unit') : Cancels op z x :=
  unit'_subsingleton _ _

/-- Every Boolean is idempotent under OR. -/
theorem bor_merges (b : Bool) : Merges bor b := by
  unfold Merges
  exact bor_idem b

/-- `true` cancels to `false` under XOR. -/
theorem bxor_cancels_true : Cancels bxor false true := by
  rfl

/-- `one` cancels to `zero` in Z/2Z. -/
theorem z2_cancels_one : Cancels Z2.add Z2.zero Z2.one := by
  rfl

theorem z2_not_merges_one : ¬ Merges Z2.add Z2.one := by
  unfold Merges
  decide

/-- Peano `one` keeps its multiplicity: its double is neither one nor zero. -/
theorem nat_keeps_one : Keeps MyNat.add MyNat.zero MyNat.one := by
  unfold Keeps
  decide

/-- The three behaviours occur in the specified examples. -/
theorem faces_of_one_plus_one :
    Merges bor true ∧
    Cancels bxor false true ∧
    Cancels Z2.add Z2.zero Z2.one ∧
    Keeps MyNat.add MyNat.zero MyNat.one :=
  ⟨bor_merges true, bxor_cancels_true, z2_cancels_one, nat_keeps_one⟩

/- ========================================================================== 
   6. INVARIANCE UNDER HOMOMORPHISMS
   ========================================================================== -/

/-- Homomorphisms preserve merging. -/
theorem merges_hom {α β : Type} (op : α → α → α)
    (op' : β → β → β) (f : α → β)
    (hf : ∀ a b, f (op a b) = op' (f a) (f b))
    (x : α) (h : Merges op x) : Merges op' (f x) :=
  Eq.trans (Eq.symm (hf x x)) (congrArg f h)

/-- Homomorphisms preserve cancellation if they map the designated `z` to `z'`. -/
theorem cancels_hom {α β : Type} (op : α → α → α)
    (op' : β → β → β) (f : α → β)
    (hf : ∀ a b, f (op a b) = op' (f a) (f b))
    (z : α) (z' : β) (hz : f z = z')
    (x : α) (h : Cancels op z x) : Cancels op' z' (f x) :=
  Eq.trans (Eq.symm (hf x x)) (Eq.trans (congrArg f h) hz)

/-- Injective homomorphisms preserve keeping multiplicity. -/
theorem keeps_hom_inj {α β : Type} (op : α → α → α)
    (op' : β → β → β) (f : α → β)
    (hf : ∀ a b, f (op a b) = op' (f a) (f b))
    (hinj : ∀ a b, f a = f b → a = b)
    (z : α) (z' : β) (hz : f z = z')
    (x : α) (h : Keeps op z x) : Keeps op' z' (f x) := by
  unfold Keeps at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro h'
    apply h1
    apply hinj
    exact Eq.trans (hf x x) h'
  · intro h'
    apply h2
    apply hinj
    exact Eq.trans (hf x x) (Eq.trans h' (Eq.symm hz))

/-- No OR-homomorphism from Bool to Z/2Z can send `true` to `one`:
    OR merges `true`, whereas addition modulo two does not merge `one`. -/
theorem no_hom_or_to_z2 (f : Bool → Z2)
    (hf : ∀ a b, f (bor a b) = Z2.add (f a) (f b)) :
    f true ≠ Z2.one := by
  intro h
  have hm : Merges Z2.add (f true) :=
    merges_hom bor Z2.add f hf true (bor_merges true)
  rw [h] at hm
  exact z2_not_merges_one hm

/-- A zero-preserving homomorphism from Z/2Z to Peano addition collapses
    `one` to zero, because Peano addition has no nonzero self-cancelling value. -/
theorem z2_collapses_in_nat (f : Z2 → MyNat)
    (hf : ∀ a b, f (Z2.add a b) = MyNat.add (f a) (f b))
    (hz : f Z2.zero = MyNat.zero) : f Z2.one = f Z2.zero := by
  have hc : Cancels MyNat.add MyNat.zero (f Z2.one) :=
    cancels_hom Z2.add MyNat.add f hf Z2.zero MyNat.zero hz
      Z2.one z2_cancels_one
  rw [hz]
  exact MyNat.add_self_eq_zero hc

theorem z2_not_injective_in_nat (f : Z2 → MyNat)
    (hf : ∀ a b, f (Z2.add a b) = MyNat.add (f a) (f b))
    (hz : f Z2.zero = MyNat.zero) :
    ¬ (∀ a b, f a = f b → a = b) := by
  intro hinj
  have h := z2_collapses_in_nat f hf hz
  exact Z2.one_ne_zero (hinj Z2.one Z2.zero h)

/- ========================================================================== 
   7. TYPED SUMMARY TABLE
   ========================================================================== -/

/-- The three `x op x` regimes, plus a separate tag-preservation category
    for the coproduct example (which is not presented as a magma operation). -/
inductive Rule where
  | merge
  | cancel
  | keep
  | tagged
  deriving Repr, DecidableEq

def Rule.label : Rule → String
  | Rule.merge  => "merge"
  | Rule.cancel => "cancel"
  | Rule.keep   => "keep"
  | Rule.tagged => "tagged"

/-- One row of the human-readable summary. -/
structure OnePlusOneResult where
  name : String
  result : String
  rule : Rule
  witness : String
  explanation : String

def results : List OnePlusOneResult :=
  [ { name := "Peano naturals (counting)"
      result := "2"
      rule := Rule.keep
      witness := "MyNat.one_add_one_eq_two, nat_keeps_one"
      explanation := "Successor-based addition preserves multiplicity" }
  , { name := "Coproduct of two singletons"
      result := "2 distinct tagged elements"
      rule := Rule.tagged
      witness := "coprodEnumeration_explicit, coprod_distinct, MyList.length_append, coprodCard_eq_sum_of_component_lengths"
      explanation := "Concatenating the two separately tagged singleton enumerations gives length 1 + 1" }
  , { name := "Bool with OR"
      result := "true (the chosen value 1)"
      rule := Rule.merge
      witness := "bor_merges"
      explanation := "Idempotence absorbs the second occurrence" }
  , { name := "Bool with XOR"
      result := "false (the chosen value 0)"
      rule := Rule.cancel
      witness := "bxor_cancels_true"
      explanation := "The two equal inputs cancel" }
  , { name := "Z/2Z addition"
      result := "zero"
      rule := Rule.cancel
      witness := "z2_cancels_one, toZ2_hom, ofZ2_hom"
      explanation := "The additive structure is isomorphic to Boolean XOR" }
  ]

def OnePlusOneResult.render (r : OnePlusOneResult) : String :=
  s!"{r.name}: 1 ⊕ 1 = {r.result}  [{r.rule.label}]\n  ({r.explanation})\n  witness: {r.witness}\n"

def summary : String :=
  String.join (results.map OnePlusOneResult.render)

#eval summary

end OnePlusOne

/-
  ============================================================================
  LEDGER
  ============================================================================

  DEFINITIONS:
    MyNat, MyList, Coprod, Unit', TwoIndex, copair, codiag, bor, bxor,
    Z2, toZ2, ofZ2, Merges, Cancels, Keeps, Rule, OnePlusOneResult,
    results, summary.

  THEOREMS:
    All declarations named `theorem` above are proved in Lean.

  AXIOMS:
    None declared by this file.

  CONJECTURES / SORRIES:
    None.

  IMPORTANT QUALIFICATIONS:
    * `trichotomy` proves exhaustiveness for any binary operation and any
      designated comparison value. It requires decidable equality to split
      the two equality tests.
    * `exactly_one_regime` proves exclusivity when x ≠ z. At x = z, merge
      and cancel can overlap; they need not both hold for an arbitrary op.
    * The coproduct is not assigned an `x op x` regime. Its row is tagged:
      two distinct summands are enumerated, and a generic list-length theorem
      proves that concatenating the component enumerations adds their sizes.
    * Z2's formalized algebra here is its additive structure, not a full
      field structure with multiplication.
    * The homomorphism results concern the explicitly defined operations.

  KEY CROSS-STRUCTURE RESULTS:
    coprodEnumeration_explicit
    coprodCard_eq_twoSingletonCardSum
    same_inputs_different_outputs
    toZ2_hom, ofZ2_hom
    exactly_one_regime
    merges_hom, cancels_hom, keeps_hom_inj
    no_hom_or_to_z2
    z2_collapses_in_nat
    z2_not_injective_in_nat
  ============================================================================
-/

#print axioms OnePlusOne.faces_of_one_plus_one
#print axioms OnePlusOne.no_hom_or_to_z2
#print axioms OnePlusOne.z2_collapses_in_nat
#print axioms OnePlusOne.codiag_tag_determines
#print axioms OnePlusOne.coprodCard_eq_twoSingletonCardSum
#print axioms OnePlusOne.exactly_one_regime
