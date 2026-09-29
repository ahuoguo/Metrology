module

public import Mathlib.Order.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Std.Data.ExtTreeMap

/-!
# Locations

Ported from clutch/theories/common/locations.v

The design mirrors `Iris.HeapLang.Loc` from iris-lean (a structure over `Int`), but the type
is defined afresh as `ConProbLang.Loc` so that `con_prob_lang` does not depend on iris-lean's
`heap_lang`.

Rocq → Lean:
* `loc`, `Loc`, `loc_car` → `Loc`, `Loc.mk`, `Loc.loc_car` (the field; `Loc.n` is an alias);
* `loc_eq_spec` → `loc_eq_spec` (also `Loc.ext_iff`);
* `loc_eq_decision`, `loc_inhabited` → derived `DecidableEq`, `Inhabited`;
* `loc_countable` → Mathlib `Countable Loc` (and `Encodable Loc`);
* `loc_infinite` → Mathlib `Infinite Loc`;
* `loc_add l off`, notation `l +ₗ off` → `loc_add`, notation `l +ₗ off` (also `HAdd Loc Int Loc`
  so that `l + off` works as in iris-lean; both are definitionally equal);
* `loc_le`, `loc_lt`, `≤ₗ`, `<ₗ` → `loc_le`, `loc_lt`, notations `≤ₗ`, `<ₗ`. The Mathlib
  order instance `LinearOrder Loc` agrees definitionally (`loc_le l1 l2 ↔ l1 ≤ l2` is `Iff.rfl`).
  The `compare` of this `LinearOrder` is the `Ord Loc` instance used to key heaps
  `Std.ExtTreeMap Loc V` (with the default comparator `compare`).
* `loc_add_inj` (an `Inj` instance) → theorem `loc_add_inj : Function.Injective (loc_add l)`;
* `fresh_locs (ls : gset loc)` → `fresh_locs (ls : List Loc)` (as iris-lean's `Loc.fresh`);
* `fresh_loc (σ : gmap loc V)` → `fresh_loc (σ : Std.ExtTreeMap Loc V)`, `dom σ` membership
  becomes `l ∈ σ`; `fresh_loc_eq_dom` takes `∀ l, l ∈ σ ↔ l ∈ σ'`. Rocq defines
  `fresh_loc σ := fresh (dom σ)` (stdpp's `infinite_fresh`), whereas here
  `fresh_loc σ := fresh_locs σ.keys` (one past the maximal key). The concrete location chosen may
  therefore differ from Rocq's; this is irrelevant since `fresh_loc` is irreducible and only the
  freshness lemmas (`fresh_loc_is_fresh`, `fresh_loc_offset_is_fresh`, `fresh_loc_eq_dom`, all
  ported) are used downstream;
* `loc_le_dec`, `loc_lt_dec`, `loc_le_po`, `loc_le_total` → instances derived from
  `LinearOrder Loc` (`loc_le_dec`, `loc_lt_dec` are also given explicitly);
* `Global Opaque fresh_locs fresh_loc` → the definitions are `@[irreducible]`.
-/

@[expose] public section

namespace ConProbLang

/-- Rocq: `loc`. -/
@[ext]
structure Loc where
  /-- Rocq: `Loc`. -/
  mk ::
  /-- Rocq: `loc_car`. -/
  loc_car : Int
deriving Inhabited, Repr, DecidableEq

namespace Loc

/-- Alias for `loc_car` (iris-lean's name for the field). -/
abbrev n (l : Loc) : Int := l.loc_car

@[simp] theorem n_eq (l : Loc) : l.n = l.loc_car := rfl

@[simp] theorem mk_loc_car (l : Loc) : Loc.mk l.loc_car = l := rfl

/-- `Loc ≃ Int`. -/
def equivInt : Loc ≃ Int where
  toFun := loc_car
  invFun := Loc.mk
  left_inv _ := rfl
  right_inv _ := rfl

end Loc

open Loc

/-- Rocq: `loc_eq_spec`. -/
theorem loc_eq_spec (l1 l2 : Loc) : l1 = l2 ↔ l1.loc_car = l2.loc_car := Loc.ext_iff

/-- Rocq: `loc_countable`. -/
instance loc_encodable : Encodable Loc := Encodable.ofEquiv Int Loc.equivInt

/-- Rocq: `loc_countable`. -/
instance loc_countable : Countable Loc := inferInstance

/-- Rocq: `loc_infinite`. -/
instance loc_infinite : Infinite Loc := Infinite.of_injective Loc.mk (fun _ _ h => by cases h; rfl)

/-- Rocq: `loc_add`. -/
def loc_add (l : Loc) (off : Int) : Loc := ⟨l.loc_car + off⟩

/-- Rocq: `loc_le`. -/
def loc_le (l1 l2 : Loc) : Prop := l1.loc_car ≤ l2.loc_car

/-- Rocq: `loc_lt`. -/
def loc_lt (l1 l2 : Loc) : Prop := l1.loc_car < l2.loc_car

@[inherit_doc] infixl:65 " +ₗ " => loc_add
@[inherit_doc] infix:50 " ≤ₗ " => loc_le
@[inherit_doc] infix:50 " <ₗ " => loc_lt

instance : HAdd Loc Int Loc where
  hAdd := loc_add

instance : HAdd Loc Nat Loc where
  hAdd l i := loc_add l i

@[simp] theorem loc_add_loc_car (l : Loc) (off : Int) : (l +ₗ off).loc_car = l.loc_car + off := rfl

@[simp] theorem loc_hadd_eq (l : Loc) (off : Int) : l + off = l +ₗ off := rfl

@[simp] theorem loc_hadd_nat_eq (l : Loc) (off : Nat) : l + off = l +ₗ (off : Int) := rfl

instance : Zero Loc := ⟨⟨0⟩⟩

/-- The (linear) order on locations, the `Int` order on `loc_car`. Its `compare` is the
`Ord Loc` instance used to key heaps. -/
instance : LinearOrder Loc :=
  LinearOrder.lift' Loc.loc_car (fun _ _ h => Loc.ext h)

instance : Std.LawfulEqCmp (compare : Loc → Loc → Ordering) where
  eq_of_compare h := compare_eq_iff_eq.1 h
  compare_self := compare_eq_iff_eq.2 rfl

theorem Loc.le_iff {l1 l2 : Loc} : l1 ≤ l2 ↔ l1.loc_car ≤ l2.loc_car := Iff.rfl

theorem Loc.lt_iff {l1 l2 : Loc} : l1 < l2 ↔ l1.loc_car < l2.loc_car := Iff.rfl

theorem loc_le_iff (l1 l2 : Loc) : l1 ≤ₗ l2 ↔ l1 ≤ l2 := Iff.rfl

theorem loc_lt_iff (l1 l2 : Loc) : l1 <ₗ l2 ↔ l1 < l2 := Iff.rfl

/-- Rocq: `loc_add_assoc`. -/
theorem loc_add_assoc (l : Loc) (i j : Int) : l +ₗ i +ₗ j = l +ₗ (i + j) := by
  ext; simp [Int.add_assoc]

/-- Rocq: `loc_add_0`. -/
@[simp] theorem loc_add_0 (l : Loc) : l +ₗ 0 = l := by ext; simp

/-- Rocq: `loc_add_inj`. -/
theorem loc_add_inj (l : Loc) : Function.Injective (loc_add l) := by
  intro i j h
  have := congrArg Loc.loc_car h
  simp only [loc_add_loc_car] at this
  omega

/-- Rocq: `fresh_locs`. Rocq folds over a `gset loc`; here the argument is a list of
locations (e.g. the key list of a heap, `Std.ExtTreeMap.keys`). -/
@[irreducible] def fresh_locs (ls : List Loc) : Loc :=
  ⟨(ls.map Loc.loc_car).foldr max 0 + 1⟩

private theorem mem_le_foldr_max (xs : List Int) (x : Int) (h : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

private theorem foldr_max_le (xs : List Int) (b : Int) (hb : 0 ≤ b) (h : ∀ x ∈ xs, x ≤ b) :
    xs.foldr max 0 ≤ b := by
  induction xs with
  | nil => simpa using hb
  | cons y ys ih =>
    simp only [List.foldr_cons]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

private theorem foldr_max_nonneg (xs : List Int) : 0 ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih => simpa using Or.inr ih

theorem fresh_locs_gt (ls : List Loc) (l : Loc) (h : l ∈ ls) :
    l.loc_car < (fresh_locs ls).loc_car := by
  unfold fresh_locs
  have := mem_le_foldr_max _ _ (List.mem_map_of_mem (f := Loc.loc_car) h)
  simp only
  omega

/-- Rocq: `fresh_locs_fresh`. -/
theorem fresh_locs_fresh (ls : List Loc) (i : Int) (hi : 0 ≤ i) : fresh_locs ls +ₗ i ∉ ls :=
  fun hmem => by
    have := fresh_locs_gt ls _ hmem
    simp only [loc_add_loc_car] at this
    omega

/-- `fresh_locs` only depends on the elements of the list. -/
theorem fresh_locs_ext (ls ls' : List Loc) (h : ∀ l, l ∈ ls ↔ l ∈ ls') :
    fresh_locs ls = fresh_locs ls' := by
  have key : ∀ ls ls' : List Loc, (∀ l, l ∈ ls → l ∈ ls') →
      (ls.map Loc.loc_car).foldr max 0 ≤ (ls'.map Loc.loc_car).foldr max 0 := by
    intro ls ls' h
    apply foldr_max_le _ _ (foldr_max_nonneg _)
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact mem_le_foldr_max _ _ (List.mem_map_of_mem (h l hl))
  unfold fresh_locs
  have h1 := key ls ls' (fun l => (h l).1)
  have h2 := key ls' ls (fun l => (h l).2)
  ext; simp only; omega

variable {V : Type*}

/-- Rocq: `fresh_loc`. Rocq uses `fresh (dom σ)`; here we use `fresh_locs` of the keys,
which additionally gives freshness of all non-negative offsets. -/
@[irreducible] def fresh_loc (σ : Std.ExtTreeMap Loc V) : Loc := fresh_locs σ.keys

/-- Rocq: `fresh_loc_offset_is_fresh`. -/
theorem fresh_loc_offset_is_fresh (σ : Std.ExtTreeMap Loc V) (i : Int) (hi : 0 ≤ i) :
    fresh_loc σ +ₗ i ∉ σ := by
  rw [← Std.ExtTreeMap.mem_keys]
  unfold fresh_loc
  exact fresh_locs_fresh _ i hi

/-- Rocq: `fresh_loc_is_fresh`. -/
theorem fresh_loc_is_fresh (σ : Std.ExtTreeMap Loc V) : fresh_loc σ ∉ σ := by
  simpa using fresh_loc_offset_is_fresh σ 0 le_rfl

/-- Rocq: `fresh_loc_eq_dom`. -/
theorem fresh_loc_eq_dom {V' : Type*} (ls : Std.ExtTreeMap Loc V) (ls' : Std.ExtTreeMap Loc V')
    (h : ∀ l, l ∈ ls ↔ l ∈ ls') : fresh_loc ls = fresh_loc ls' := by
  unfold fresh_loc
  apply fresh_locs_ext
  intro l
  rw [Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_keys]
  exact h l

/-- Rocq: `loc_le_dec`. -/
instance loc_le_dec (l1 l2 : Loc) : Decidable (l1 ≤ₗ l2) :=
  inferInstanceAs (Decidable (l1.loc_car ≤ l2.loc_car))

/-- Rocq: `loc_lt_dec`. -/
instance loc_lt_dec (l1 l2 : Loc) : Decidable (l1 <ₗ l2) :=
  inferInstanceAs (Decidable (l1.loc_car < l2.loc_car))

/-- Rocq: `loc_le_po`. -/
theorem loc_le_po : (∀ l, l ≤ₗ l) ∧ (∀ l1 l2 l3, l1 ≤ₗ l2 → l2 ≤ₗ l3 → l1 ≤ₗ l3) ∧
    (∀ l1 l2, l1 ≤ₗ l2 → l2 ≤ₗ l1 → l1 = l2) :=
  ⟨fun _ => le_refl _, fun _ _ _ => le_trans (α := Loc), fun _ _ => le_antisymm (α := Loc)⟩

/-- Rocq: `loc_le_total`. -/
theorem loc_le_total (l1 l2 : Loc) : l1 ≤ₗ l2 ∨ l2 ≤ₗ l1 := le_total l1 l2

/-- Rocq: `loc_le_ngt`. -/
theorem loc_le_ngt (l1 l2 : Loc) : l1 ≤ₗ l2 ↔ ¬ l2 <ₗ l1 := not_lt.symm

/-- Rocq: `loc_le_lteq`. -/
theorem loc_le_lteq (l1 l2 : Loc) : l1 ≤ₗ l2 ↔ l1 <ₗ l2 ∨ l1 = l2 := le_iff_lt_or_eq (α := Loc)

/-- Rocq: `loc_add_le_mono`. -/
theorem loc_add_le_mono (l1 l2 : Loc) (i1 i2 : Int) (hl : l1 ≤ₗ l2) (hi : i1 ≤ i2) :
    l1 +ₗ i1 ≤ₗ l2 +ₗ i2 := Int.add_le_add hl hi

/-! Sanity check: heaps keyed by `Loc` have the lawful comparator instances. -/
example : Std.TransCmp (compare : Loc → Loc → Ordering) := inferInstance
example : Std.LawfulEqCmp (compare : Loc → Loc → Ordering) := inferInstance

end ConProbLang
