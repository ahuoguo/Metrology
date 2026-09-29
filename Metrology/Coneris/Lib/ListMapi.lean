module

public import Metrology.Coneris.Lib.ListIter

/-!
# Lists in `con_prob_lang` (specs of `list_mapi`)

Ported from clutch/theories/coneris/lib/list.v (section `list_specs_extra`).

## Rocq → Lean
* `l !! i` is `l[i]?`.
* The `let r := f (k + i) x in ...` and `let l' := mapi_loop f k l in ...` of the Rocq
  postconditions are inlined.
* `inject (k + i)%nat` is `inject (k + i)` at `Inject ℕ val`, i.e. `LitV (LitInt ↑(k + i))`.
-/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs_extra

variable {GF : BundledGFunctors} [conerisGS GF] {A : Type} [Inject A val] {E : CoPset}

/-- Rocq: `mapi_loop`. -/
def mapi_loop {B : Type} (f : ℕ → A → B) (k : ℕ) : List A → List B
  | h :: t => f k h :: mapi_loop f (k + 1) t
  | [] => []

omit [Inject A val] in
/-- Rocq: `mapi_loop_i`. -/
theorem mapi_loop_i {B : Type} (f : ℕ → A → B) (l : List A) (i k : ℕ) (Hlt : i < l.length) :
    ∃ v w, l[i]? = some v ∧ (mapi_loop f k l)[i]? = some w ∧ w = f (k + i) v := by
  induction l generalizing k i with
  | nil => exact absurd Hlt (Nat.not_lt_zero _)
  | cons h t IH =>
    cases i with
    | zero => exact ⟨h, f k h, rfl, rfl, by rw [Nat.add_zero]⟩
    | succ i' =>
      obtain ⟨v, w, Hv, Hw, Heq⟩ := IH i' (k + 1) (Nat.succ_lt_succ_iff.1 Hlt)
      refine ⟨v, w, Hv, Hw, ?_⟩
      rw [Heq]
      congr 1
      omega

/-- Rocq: `mapi`. -/
def mapi {B : Type} (f : ℕ → A → B) (l : List A) : List B := mapi_loop f 0 l

omit [Inject A val] in
/-- Rocq: `mapi_i`. -/
theorem mapi_i {B : Type} (f : ℕ → A → B) (l : List A) (i : ℕ) (Hlt : i < l.length) :
    ∃ v w, l[i]? = some v ∧ (mapi f l)[i]? = some w ∧ w = f i v := by
  obtain ⟨v, w, H1, H2, H3⟩ := mapi_loop_i f l i 0 Hlt
  exact ⟨v, w, H1, H2, by rw [H3, Nat.zero_add]⟩

/-- Rocq: `wp_list_mapi_loop`. -/
theorem wp_list_mapi_loop {B : Type} [Inject B val] (f : ℕ → A → B) (k : ℕ) (l : List A)
    (fv lv : val) (γ : ℕ → A → IProp GF) (ψ : ℕ → B → IProp GF) :
    {{ □ (∀ (i : ℕ) (x : A),
            {{ γ (k + i) x }} cpl(v(&fv) v(&(inject (k + i))) v(&(inject x))) @ E
            {{ fr, RET fr; ⌜fr = inject (f (k + i) x)⌝ ∗ ψ (k + i) (f (k + i) x) }}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗list] i ↦ a ∈ l, γ (k + i) a) }}
      cpl(v(&list_mapi_loop) v(&fv) #(k : ℕ) v(&lv)) @ E
    {{ rv, RET rv; ⌜is_list (mapi_loop f k l) rv⌝ ∗
        ([∗list] i ↦ a ∈ mapi_loop f k l, ψ (k + i) a) }} := by
  induction l generalizing lv k with
  | nil =>
    iintro %Φ ⟨#Hf, %Hil, -⟩ HΦ
    subst Hil
    wp_rec
    wp_pures'
    iapply HΦ
    imodintro
    isplit
    · ipureintro
      rfl
    · iempintro
  | cons h l' IH =>
    iintro %Φ ⟨#Hf, %Hil, Hhead, Hown⟩ HΦ
    obtain ⟨lv', rfl, Hil'⟩ := Hil
    wp_rec
    wp_pures'
    rw [show ((k : ℕ) : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; rfl]
    wp_bind (App (App (App (Val list_mapi_loop) _) _) _)
    iapply IH (k + 1) lv' $$ [Hown] [Hhead HΦ]
    · isplitr
      · imodintro
        iintro %i %x
        rw [show k + 1 + i = k + (i + 1) by omega]
        ihave H := Hf $$ %(i + 1) %x
        iexact H
      isplit
      · ipureintro
        exact Hil'
      rw [← bigSepL_shift_succ]
      iexact Hown
    iintro !> %rv ⟨%Hil'', Hown⟩
    wp_pures'
    ihave Hf0 := Hf $$ %0 %h
    isimp only [Nat.add_zero] at Hf0 Hhead
    wp_apply Hf0 $$ Hhead with %fr ⟨%Hfr, HΨ⟩
    subst Hfr
    wp_apply wp_list_cons (f k h) (mapi_loop f (k + 1) l') rv $$ [] with %v %Hil'''
    · ipureintro
      exact Hil''
    iapply HΦ
    isplitr
    · ipureintro
      exact Hil'''
    rw [mapi_loop]
    iapply BigSepL.bigSepL_cons.2
    rw [Nat.add_zero, bigSepL_shift_succ]
    iframe HΨ Hown

/-- Rocq: `wp_list_mapi`. -/
theorem wp_list_mapi {B : Type} [Inject B val] (f : ℕ → A → B) (l : List A) (fv lv : val)
    (γ : ℕ → A → IProp GF) (ψ : ℕ → B → IProp GF) :
    {{ □ (∀ (i : ℕ) (x : A),
            {{ γ i x }} cpl(v(&fv) #(i : ℕ) v(&(inject x))) @ E
            {{ fr, RET fr; ⌜fr = inject (f i x)⌝ ∗ ψ i (f i x) }}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗list] i ↦ a ∈ l, γ i a) }}
      cpl(v(&list_mapi) v(&fv) v(&lv)) @ E
    {{ rv, RET rv; ⌜is_list (mapi f l) rv⌝ ∗ ([∗list] i ↦ a ∈ mapi f l, ψ i a) }} := by
  iintro %Φ ⟨#Hf, %Hil, Hown⟩ HΦ
  wp_rec
  wp_pures'
  unfold mapi
  have H := wp_list_mapi_loop (E := E) f 0 l fv lv γ ψ
  simp only [Nat.zero_add, Nat.cast_zero] at H
  iapply H $$ [Hown] [HΦ]
  · iframe Hf Hown
    ipureintro
    exact Hil
  imodintro
  iexact HΦ

omit [Inject A val] in
/-- Rocq: `list_lookup_succ`. -/
theorem list_lookup_succ (h : A) (l : List A) (i : ℕ) : (h :: l)[i + 1]? = l[i]? := rfl

end list_specs_extra

end Coneris.Lib.List
