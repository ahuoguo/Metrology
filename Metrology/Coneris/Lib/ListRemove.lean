module

public import Metrology.Coneris.Lib.ListSpec

/-!
# Lists in `con_prob_lang` (specs of `list_remove_nth`, `list_find_remove`, `list_rev`, ...)

Ported from clutch/theories/coneris/lib/list.v (end of section `list_specs`).

## Rocq → Lean
* `rev_append lM rM` is `List.reverseAux lM rM`; `reverse lM` is `List.reverse lM`;
  `List.filter P l` is `List.filter P l`.
* `if b then P else Q` for `b : bool` is Lean's `if b then P else Q` (with `b = true`).
* `wp_list_rev_aux` is `Local` in Rocq; here it is an ordinary theorem.

## Omitted
* `wp_list_mem` (commented out in Rocq).
-/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs

variable {GF : BundledGFunctors} [conerisGS GF] {A : Type} [Inject A val] {E : CoPset}

/-- Rocq: `wp_remove_nth`. -/
theorem wp_remove_nth (l : List A) (lv : val) (i : ℕ) :
    {{ (⌜is_list l lv ∧ i < l.length⌝ : IProp GF) }}
      cpl(v(&list_remove_nth) v(&lv) #(i : ℕ)) @ E
    {{ v, RET v; ∃ e lv' l1 l2,
        ⌜l = l1 ++ e :: l2 ∧ l1.length = i ∧ v = SOMEV (PairV (inject e) lv') ∧
          is_list (l1 ++ l2) lv'⌝ }} := by
  induction l generalizing i lv with
  | nil =>
    iintro %Φ %Ha Hφ
    exact absurd Ha.2 (Nat.not_lt_zero _)
  | cons a l' IH =>
    iintro %Φ %Ha Hφ
    obtain ⟨⟨lv', rfl, Hlcoh⟩, Hi⟩ := Ha
    cases i with
    | zero =>
      wp_rec
      wp_pures'
      iapply Hφ
      iexists a, lv', [], l'
      ipureintro
      exact ⟨rfl, rfl, rfl, Hlcoh⟩
    | succ i =>
      wp_rec
      wp_pures'
      wp_bind (App (App (Val list_remove_nth) _) _)
      iapply IH lv' i $$ [] [Hφ]
      · ipureintro
        exact ⟨Hlcoh, by simpa using Hi⟩
      iintro !> %v ⟨%e, %v', %l1, %l2, %H⟩
      obtain ⟨rfl, Hlen, rfl, Hil⟩ := H
      wp_pures'
      wp_apply wp_list_cons a (l1 ++ l2) v' $$ [] with %w %Hcons
      · ipureintro
        exact Hil
      wp_pures'
      iapply Hφ
      iexists e, w, a :: l1, l2
      ipureintro
      exact ⟨rfl, by simp [Hlen], rfl, Hcons⟩

/-- Rocq: `wp_remove_nth_total`. -/
theorem wp_remove_nth_total (l : List A) (lv : val) (i : ℕ) :
    {{ (⌜is_list l lv ∧ i < l.length⌝ : IProp GF) }}
      cpl(v(&list_remove_nth_total) v(&lv) #(i : ℕ)) @ E
    {{ v, RET v; ∃ e lv' l1 l2,
        ⌜l = l1 ++ e :: l2 ∧ l1.length = i ∧ v = lv' ∧ is_list (l1 ++ l2) lv'⌝ }} := by
  induction l generalizing i lv with
  | nil =>
    iintro %Φ %Ha Hφ
    exact absurd Ha.2 (Nat.not_lt_zero _)
  | cons a l' IH =>
    iintro %Φ %Ha Hφ
    obtain ⟨⟨lv', rfl, Hlcoh⟩, Hi⟩ := Ha
    cases i with
    | zero =>
      wp_rec
      wp_pures'
      iapply Hφ
      iexists a, lv', [], l'
      ipureintro
      exact ⟨rfl, rfl, rfl, Hlcoh⟩
    | succ i =>
      wp_rec
      wp_pures'
      wp_bind (App (App (Val list_remove_nth_total) _) _)
      iapply IH lv' i $$ [] [Hφ]
      · ipureintro
        exact ⟨Hlcoh, by simpa using Hi⟩
      iintro !> %v ⟨%e, %v', %l1, %l2, %H⟩
      obtain ⟨rfl, Hlen, rfl, Hil⟩ := H
      wp_pures'
      wp_apply wp_list_cons a (l1 ++ l2) v $$ [] with %w %Hcons
      · ipureintro
        exact Hil
      iapply Hφ
      iexists e, w, a :: l1, l2
      ipureintro
      exact ⟨rfl, by simp [Hlen], rfl, Hcons⟩

/-- Rocq: `wp_find_remove`. -/
theorem wp_find_remove (l : List A) (lv : val) (Ψ : A → IProp GF) (fv : val) :
    ⊢ (∀ (a : A),
        {{ True }} cpl(v(&fv) v(&(inject a))) @ E
        {{ (b : Bool), RET LitV (LitBool b); if b then Ψ a else True }}) -∗
      {{ ⌜is_list l lv⌝ }}
        cpl(v(&list_find_remove) v(&fv) v(&lv)) @ E
      {{ v, RET v; ⌜v = NONEV⌝ ∨
          ∃ e lv' l1 l2,
            ⌜l = l1 ++ e :: l2 ∧ v = SOMEV (PairV (inject e) lv') ∧ is_list (l1 ++ l2) lv'⌝
            ∗ Ψ e }} := by
  induction l generalizing lv with
  | nil =>
    iintro #Hf !> %Φ %Hl HΦ
    subst Hl
    wp_rec
    wp_pures'
    iapply HΦ
    imodintro
    ileft
    ipureintro
    rfl
  | cons a l' IH =>
    iintro #Hf !> %Φ %Hl HΦ
    obtain ⟨lv', rfl, Hl'⟩ := Hl
    wp_rec
    wp_pures'
    wp_apply Hf $$ %a [] with %b Hb
    · itrivial
    cases b with
    | true =>
      isimp only [↓reduceIte] at Hb
      wp_pures'
      iapply HΦ
      iright
      iexists a, lv', [], l'
      iframe Hb
      ipureintro
      exact ⟨rfl, rfl, Hl'⟩
    | false =>
      wp_pures'
      wp_bind (App (App (Val list_find_remove) _) _)
      iapply IH lv' $$ Hf [] [HΦ]
      · ipureintro
        exact Hl'
      iintro !> %w Hw
      icases Hw with (%Hw | ⟨%e, %lv'', %l1, %l2, %H, HHΨ⟩)
      · subst Hw
        wp_pures'
        iapply HΦ
        ileft
        ipureintro
        rfl
      · obtain ⟨rfl, rfl, Hlv''⟩ := H
        wp_pures'
        wp_apply wp_list_cons a (l1 ++ l2) lv'' $$ [] with %v %Hcoh
        · ipureintro
          exact Hlv''
        wp_pures'
        iapply HΦ
        iright
        iexists e, v, a :: l1, l2
        iframe HHΨ
        ipureintro
        exact ⟨rfl, rfl, Hcoh⟩

/-- Rocq: `wp_list_rev_aux` (`Local` in Rocq). -/
theorem wp_list_rev_aux (l : val) (lM : List A) (r : val) (rM : List A) :
    {{ (⌜is_list lM l ∧ is_list rM r⌝ : IProp GF) }}
      cpl(v(&list_rev_aux) v(&l) v(&r)) @ E
    {{ v, RET v; ⌜is_list (List.reverseAux lM rM) v⌝ }} := by
  induction lM generalizing l r rM with
  | nil =>
    iintro %Φ %H HΦ
    obtain ⟨rfl, Hr⟩ := H
    wp_rec
    wp_pures'
    iapply HΦ
    ipureintro
    exact Hr
  | cons a lM IH =>
    iintro %Φ %H HΦ
    obtain ⟨⟨l', rfl, Hl'⟩, Hr⟩ := H
    wp_rec
    wp_pures'
    wp_apply wp_list_cons a rM r $$ [] with %w %Hw
    · ipureintro
      exact Hr
    wp_pures'
    iapply IH l' w (a :: rM) $$ [] [HΦ]
    · ipureintro
      exact ⟨Hl', Hw⟩
    iintro !> %v %Hv
    iapply HΦ
    ipureintro
    exact Hv

/-- Rocq: `wp_list_rev`. -/
theorem wp_list_rev (l : val) (lM : List A) :
    {{ (⌜is_list lM l⌝ : IProp GF) }}
      cpl(v(&list_rev) v(&l)) @ E
    {{ v, RET v; ⌜is_list lM.reverse v⌝ }} := by
  iintro %Φ %Hl HΦ
  wp_rec
  wp_pures'
  iapply wp_list_rev_aux l lM NONEV [] $$ [] [HΦ]
  · ipureintro
    exact ⟨Hl, rfl⟩
  iintro !> %v %Hv
  iapply HΦ
  ipureintro
  simpa using Hv

/-- Rocq: `wp_list_append`. -/
theorem wp_list_append (l : val) (lM : List A) (r : val) (rM : List A) :
    {{ (⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝ : IProp GF) }}
      cpl(v(&list_append) v(&l) v(&r)) @ E
    {{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }} := by
  induction lM generalizing l r with
  | nil =>
    iintro %Φ ⟨%Hl, %Hr⟩ HΦ
    subst Hl
    wp_rec
    wp_pures'
    iapply HΦ
    ipureintro
    exact Hr
  | cons a lM IH =>
    iintro %Φ ⟨%Hl, %Hr⟩ HΦ
    obtain ⟨l', rfl, Hl'⟩ := Hl
    wp_rec
    wp_pures'
    wp_bind (App (App (Val list_append) _) _)
    iapply IH l' r $$ [] [HΦ]
    · iframe
      ipureintro
      exact ⟨Hl', Hr⟩
    iintro !> %v %Hv
    wp_apply wp_list_cons a (lM ++ rM) v $$ [] with %w %Hw
    · ipureintro
      exact Hv
    iapply HΦ
    ipureintro
    exact Hw

/-- Rocq: `wp_list_forall`. -/
theorem wp_list_forall (Φ Ψ : A → IProp GF) (l : List A) (lv fv : val) :
    ⊢ (∀ (a : A),
        {{ True }} cpl(v(&fv) v(&(inject a))) @ E
        {{ (b : Bool), RET LitV (LitBool b); if b then Φ a else Ψ a }}) -∗
      {{ ⌜is_list l lv⌝ }}
        cpl(v(&list_forall) v(&fv) v(&lv)) @ E
      {{ (b : Bool), RET LitV (LitBool b);
          if b then [∗list] a ∈ l, Φ a else ∃ a, ⌜a ∈ l⌝ ∗ Ψ a }} := by
  induction l generalizing lv with
  | nil =>
    iintro #Hfv !> %Ξ %Hl HΞ
    subst Hl
    wp_rec
    wp_pures'
    iapply HΞ $$ %true
    imodintro
    iempintro
  | cons a l' IH =>
    iintro #Hfv !> %Ξ %Hl HΞ
    obtain ⟨l'', rfl, Hl'⟩ := Hl
    wp_rec
    wp_pures'
    wp_apply Hfv $$ %a [] with %b Hb
    · itrivial
    cases b with
    | true =>
      isimp only [↓reduceIte] at Hb
      wp_pures'
      iapply IH l'' $$ Hfv [] [Hb HΞ]
      · ipureintro
        exact Hl'
      iintro !> %b' Hb'
      cases b' with
      | true =>
        isimp only [↓reduceIte] at Hb'
        iapply HΞ $$ %true
        isimp only [↓reduceIte]
        iframe Hb Hb'
      | false =>
        isimp only [Bool.false_eq_true, ↓reduceIte] at Hb'
        icases Hb' with ⟨%a', %Ha', HΨ⟩
        iapply HΞ $$ %false
        isimp only [Bool.false_eq_true, ↓reduceIte]
        iexists a'
        iframe HΨ
        ipureintro
        exact List.mem_cons_of_mem a Ha'
    | false =>
      isimp only [Bool.false_eq_true, ↓reduceIte] at Hb
      wp_pures'
      iapply HΞ $$ %false
      imodintro
      isimp only [Bool.false_eq_true, ↓reduceIte]
      iexists a
      iframe Hb
      ipureintro
      exact List.mem_cons_self

/-- Rocq: `wp_list_is_empty`. -/
theorem wp_list_is_empty (l : List A) (v : val) :
    {{ (⌜is_list l v⌝ : IProp GF) }}
      cpl(v(&list_is_empty) v(&v)) @ E
    {{ (v : Bool), RET LitV (LitBool v); ⌜v = match l with | [] => true | _ => false⌝ }} := by
  iintro %Φ %Hl HΦ
  wp_rec
  cases l with
  | nil =>
    subst Hl
    wp_pures'
    iapply HΦ
    ipureintro
    rfl
  | cons a l =>
    obtain ⟨_, rfl, _⟩ := Hl
    wp_pures'
    iapply HΦ
    ipureintro
    rfl

/-- Rocq: `is_list_eq`. -/
theorem is_list_eq (lM : List A) : ∀ l1 l2, is_list lM l1 → is_list lM l2 → l1 = l2 := by
  intro l1 l2 h1 h2
  rw [(is_list_inject lM l1).1 h1, (is_list_inject lM l2).1 h2]

/-- Rocq: `is_list_inv_l`. -/
theorem is_list_inv_l (l : val) : ∀ lM1 lM2 : List A, is_list lM1 l → lM1 = lM2 → is_list lM2 l := by
  rintro _ _ h rfl
  exact h

/-- Rocq: `is_list_snoc`. -/
theorem is_list_snoc (lM : List A) (x : A) : ∃ lv, is_list (lM ++ [x]) lv :=
  ⟨_, is_list_of_inject _⟩

/-- Rocq: `wp_list_filter`. -/
theorem wp_list_filter (l : List A) (P : A → Bool) (f lv : val) :
    {{ (∀ (x : A),
          {{ (True : IProp GF) }} cpl(v(&f) v(&(inject x))) @ E
          {{ w, RET w; ⌜w = (inject (P x) : val)⌝ }}) ∗
        ⌜is_list l lv⌝ }}
      cpl(v(&list_filter) v(&f) v(&lv)) @ E
    {{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }} := by
  induction l generalizing lv with
  | nil =>
    iintro %Φ ⟨#Hf, %Hil⟩ HΦ
    subst Hil
    wp_rec
    wp_pures'
    iapply HΦ
    ipureintro
    rfl
  | cons h t IH =>
    iintro %Φ ⟨#Hf, %Hil⟩ HΦ
    obtain ⟨lv', rfl, Hil⟩ := Hil
    wp_rec
    wp_pures'
    wp_bind (App (App (Val list_filter) _) _)
    iapply IH lv' $$ [] [HΦ]
    · iframe Hf
      ipureintro
      exact Hil
    iintro !> %rv %Hilp
    wp_pures'
    wp_apply Hf $$ %h [] with %w %Hw
    · itrivial
    subst Hw
    cases HP : P h with
    | true =>
      rw [show (inject true : val) = LitV (LitBool true) from rfl]
      wp_pures'
      wp_apply wp_list_cons h (List.filter P t) rv $$ [] with %v %Hil'
      · ipureintro
        exact Hilp
      iapply HΦ
      ipureintro
      simpa [List.filter_cons, HP] using Hil'
    | false =>
      rw [show (inject false : val) = LitV (LitBool false) from rfl]
      wp_pures'
      iapply HΦ
      ipureintro
      simpa [List.filter_cons, HP] using Hilp

/-- Rocq: `wp_list_split`. -/
theorem wp_list_split (n : ℕ) (lv : val) (l : List A) :
    {{ (⌜is_list l lv⌝ ∗ ⌜n ≤ l.length⌝ : IProp GF) }}
      cpl(v(&list_split) #(n : ℕ) v(&lv)) @ E
    {{ a b, RET PairV a b;
        ∃ l1 l2, ⌜is_list l1 a⌝ ∗ ⌜is_list l2 b⌝ ∗ ⌜l = l1 ++ l2⌝ ∗ ⌜l1.length = n⌝ }} := by
  induction n generalizing lv l with
  | zero =>
    iintro %Φ ⟨%Hlist, %Hlength⟩ HΦ
    wp_rec
    wp_pures'
    iapply HΦ
    iexists [], l
    ipureintro
    exact ⟨rfl, Hlist, rfl, rfl⟩
  | succ n IHn =>
    iintro %Φ ⟨%Hlist, %Hlength⟩ HΦ
    cases l with
    | nil => exact absurd Hlength (by simp)
    | cons x l =>
      obtain ⟨lv', rfl, Hlist⟩ := Hlist
      wp_rec
      wp_pures'
      wp_bind (App (App (Val list_split) _) _)
      iapply IHn lv' l $$ [] [HΦ]
      · ipureintro
        exact ⟨Hlist, by simpa using Hlength⟩
      iintro !> %a %b ⟨%l1, %l2, %Ha, %Hb, %Hl, %Hlen⟩
      wp_pures'
      wp_apply wp_list_cons x l1 a $$ [] with %w %Hw
      · ipureintro
        exact Ha
      wp_pures'
      iapply HΦ
      iexists x :: l1, l2
      ipureintro
      exact ⟨Hw, Hb, by simp [Hl], by simp [Hlen]⟩

end list_specs

end Coneris.Lib.List
