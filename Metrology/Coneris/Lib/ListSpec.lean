module

public import Metrology.Coneris.Lib.List

/-!
# Lists in `con_prob_lang` (basic specs)

Ported from clutch/theories/coneris/lib/list.v (section `list_specs`, first part).

## Rocq → Lean
* `Context `{!conerisGS Σ}` is `{GF : BundledGFunctors} [conerisGS GF]`; `Context `[!Inject A
  val]` is `{A : Type} [Inject A val]`.
* `is_list` is a structurally recursive `Prop`-valued function, as in Rocq.
* Texan triples `{{{ P }}} e @ E {{{ x, RET v; Q }}}` are iris-lean's
  `{{ P }} e @ E {{ x, RET v; Q }}` (the same `□ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e @ E {{ Φ }}`
  up to the outer `□`, which a top-level `⊢` makes irrelevant).
* `#v` for `v : nat` is `LitV (LitInt (v : ℤ))`; `length` is `List.length`, `tail` is
  `List.tail`.

## Added (not in Rocq)
* `is_list_of_inject`.
-/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs

variable {GF : BundledGFunctors} [conerisGS GF] {A : Type} [Inject A val]

/-- Rocq: `is_list`. -/
def is_list : List A → val → Prop
  | [], v => v = NONEV
  | a :: l', v => ∃ lv, v = SOMEV (PairV (inject a) lv) ∧ is_list l' lv

/-- Rocq: `is_list_inject`. -/
theorem is_list_inject (xs : List A) (v : val) : is_list xs v ↔ v = inject xs := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs IH =>
    constructor
    · rintro ⟨lv, rfl, h⟩
      rw [(IH lv).1 h]
      rfl
    · rintro rfl
      exact ⟨_, rfl, (IH _).2 rfl⟩

/-- `is_list l (inject l)`. -/
theorem is_list_of_inject (xs : List A) : is_list xs (inject xs) := (is_list_inject xs _).2 rfl

variable {E : CoPset}

/-- Rocq: `wp_list_nil`. -/
theorem wp_list_nil :
    {{ (True : IProp GF) }} list_nil @ E {{ v, RET v; ⌜is_list ([] : List A) v⌝ }} := by
  iintro %Φ - HΦ
  unfold list_nil
  wp_pures
  iapply HΦ
  ipureintro
  rfl

/-- Rocq: `wp_list_cons`. -/
theorem wp_list_cons (a : A) (l : List A) (lv : val) :
    {{ (⌜is_list l lv⌝ : IProp GF) }}
      cpl(v(&list_cons) v(&(inject a)) v(&lv)) @ E
    {{ v, RET v; ⌜is_list (a :: l) v⌝ }} := by
  iintro %Φ %Hl HΦ
  wp_lam
  wp_pures
  iapply HΦ
  ipureintro
  exact ⟨lv, rfl, Hl⟩

/-- Rocq: `wp_list_singleton`. -/
theorem wp_list_singleton (a : A) :
    {{ (True : IProp GF) }}
      cpl(v(&list_cons) v(&(inject a)) &list_nil) @ E
    {{ v, RET v; ⌜is_list [a] v⌝ }} := by
  iintro %Φ - HΦ
  unfold list_nil
  wp_pures
  wp_apply wp_list_cons a [] _ $$ [] with %v' %Hv'
  · ipureintro
    rfl
  iapply HΦ
  ipureintro
  exact Hv'

/-- Rocq: `wp_list_head`. -/
theorem wp_list_head (lv : val) (l : List A) :
    {{ (⌜is_list l lv⌝ : IProp GF) }}
      cpl(v(&list_head) v(&lv)) @ E
    {{ v, RET v; ⌜(l = [] ∧ v = NONEV) ∨ (∃ a l', l = a :: l' ∧ v = SOMEV (inject a))⌝ }} := by
  iintro %Φ %Ha HΦ
  wp_lam
  cases l with
  | nil =>
    subst Ha
    wp_pures
    iapply HΦ
    ipureintro
    exact Or.inl ⟨rfl, rfl⟩
  | cons a l =>
    obtain ⟨lv', rfl, -⟩ := Ha
    wp_pures
    iapply HΦ
    ipureintro
    exact Or.inr ⟨a, l, rfl, rfl⟩

/-- Rocq: `wp_list_tail`. -/
theorem wp_list_tail (lv : val) (l : List A) :
    {{ (⌜is_list l lv⌝ : IProp GF) }}
      cpl(v(&list_tail) v(&lv)) @ E
    {{ v, RET v; ⌜is_list l.tail v⌝ }} := by
  iintro %Φ %Ha HΦ
  wp_lam
  cases l with
  | nil =>
    subst Ha
    wp_match
    wp_inj
    iapply HΦ
    ipureintro
    rfl
  | cons a l =>
    obtain ⟨lv', rfl, Htail⟩ := Ha
    wp_match
    wp_proj
    iapply HΦ
    ipureintro
    exact Htail

/-- Rocq: `wp_list_length`. -/
theorem wp_list_length (l : List A) (lv : val) :
    {{ (⌜is_list l lv⌝ : IProp GF) }}
      cpl(v(&list_length) v(&lv)) @ E
    {{ v, RET LitV (LitInt ((v : ℕ) : ℤ)); ⌜v = l.length⌝ }} := by
  induction l generalizing lv with
  | nil =>
    iintro %Φ %Ha HΦ
    subst Ha
    wp_rec
    wp_match
    iapply HΦ $$ %0
    ipureintro
    rfl
  | cons a l' IH =>
    iintro %Φ %Ha HΦ
    obtain ⟨lv', rfl, Hlcoh⟩ := Ha
    wp_rec
    wp_match
    wp_proj
    wp_bind (App (Val list_length) _)
    iapply IH lv' $$ [] [HΦ]
    · ipureintro
      exact Hlcoh
    iintro !> %v %Hv
    wp_op
    ihave HΦ' := HΦ $$ %(1 + v)
    rw [Nat.cast_add, Nat.cast_one]
    iapply HΦ'
    ipureintro
    simp [Hv, Nat.add_comm]

end list_specs

end Coneris.Lib.List
