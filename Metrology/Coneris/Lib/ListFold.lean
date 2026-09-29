module

public import Metrology.Coneris.Lib.ListSpec

/-!
# Lists in `con_prob_lang` (specs of `list_fold`, `list_sub`, `list_nth`)

Ported from clutch/theories/coneris/lib/list.v (section `list_specs`).

## Rocq → Lean
* `option A` is `Option A`; `take k l` is `List.take k l`; `nth_error l i` is `l[i]?`.
* `wp_list_fold` is derived from `wp_list_fold_generalized'` (Rocq reproves it by induction
  after generalizing the processed prefix; the statement is the same).
-/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs

variable {GF : BundledGFunctors} [conerisGS GF] {A : Type} [Inject A val] {E : CoPset}

/-- Rocq: `wp_list_fold_generalized'`. -/
theorem wp_list_fold_generalized' (handler : val) (l lp : List A) (acc lv : val)
    (P : List A → val → Option A → List A → IProp GF) (Φ Ψ : A → IProp GF) :
    ⊢ □ (∀ (a : A) (acc : val) (lacc lrem : List A),
          (P lacc acc none (a :: lrem) -∗ P lacc acc (some a) lrem)) -∗
      (∀ (a : A) (acc : val) (lacc lrem : List A),
        {{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (some a) lrem ∗ Φ a }}
          cpl(v(&handler) v(&acc) v(&(inject a))) @ E
        {{ v, RET v; P (lacc ++ [a]) v none lrem ∗ Ψ a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P lp acc none l ∗ [∗list] a ∈ l, Φ a }}
        cpl(v(&list_fold) v(&handler) v(&acc) v(&lv)) @ E
      {{ v, RET v; P (lp ++ l) v none [] ∗ [∗list] a ∈ l, Ψ a }} := by
  induction l generalizing lp acc lv with
  | nil =>
    iintro #Hvs #Hcl !> %Ξ ⟨%Hl, Hacc, -⟩ HΞ
    subst Hl
    wp_rec
    wp_pures
    iapply HΞ
    rw [List.append_nil]
    iframe Hacc
    imodintro
    iempintro
  | cons x l IHl =>
    iintro #Hvs #Hcl !> %Ξ ⟨%Hl, Hacc, Hx, HΦ⟩ HΞ
    obtain ⟨lw, rfl, Hlw⟩ := Hl
    wp_rec
    wp_pures
    ihave Hacc := Hvs $$ %x %acc %lp %l Hacc
    wp_apply Hcl $$ %x %acc %lp %l [Hacc Hx] with %w ⟨Hacc, HΨ⟩
    · iframe Hacc Hx
      ipureintro
      rfl
    wp_pures
    have IH := IHl (lp ++ [x]) w lw
    simp only [List.append_assoc, List.singleton_append] at IH
    iapply IH $$ Hvs Hcl [HΦ Hacc] [HΨ HΞ]
    · iframe HΦ Hacc
      ipureintro
      exact Hlw
    iintro !> %v ⟨HP, HΨs⟩
    iapply HΞ
    iframe HP HΨ HΨs

/-- Rocq: `wp_list_fold'`. -/
theorem wp_list_fold' (handler : val) (l : List A) (acc lv : val)
    (P : List A → val → Option A → List A → IProp GF) (Φ Ψ : A → IProp GF) :
    ⊢ □ (∀ (a : A) (acc : val) (lacc lrem : List A),
          (P lacc acc none (a :: lrem) -∗ P lacc acc (some a) lrem)) -∗
      (∀ (a : A) (acc : val) (lacc lrem : List A),
        {{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (some a) lrem ∗ Φ a }}
          cpl(v(&handler) v(&acc) v(&(inject a))) @ E
        {{ v, RET v; P (lacc ++ [a]) v none lrem ∗ Ψ a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P [] acc none l ∗ [∗list] a ∈ l, Φ a }}
        cpl(v(&list_fold) v(&handler) v(&acc) v(&lv)) @ E
      {{ v, RET v; P l v none [] ∗ [∗list] a ∈ l, Ψ a }} := by
  have H := wp_list_fold_generalized' (E := E) handler l [] acc lv P Φ Ψ
  simp only [List.nil_append] at H
  exact H

/-- Rocq: `wp_list_fold`. -/
theorem wp_list_fold (P : List A → val → IProp GF) (Φ Ψ : A → IProp GF) (handler : val)
    (l : List A) (acc lv : val) :
    ⊢ (∀ (a : A) (acc : val) (lacc lrem : List A),
        {{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}
          cpl(v(&handler) v(&acc) v(&(inject a))) @ E
        {{ v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗list] a ∈ l, Φ a }}
        cpl(v(&list_fold) v(&handler) v(&acc) v(&lv)) @ E
      {{ v, RET v; P l v ∗ [∗list] a ∈ l, Ψ a }} := by
  iintro #Hcl
  iapply wp_list_fold' handler l acc lv (fun lacc acc _ _ => P lacc acc) Φ Ψ $$ [] Hcl
  imodintro
  iintro %a %acc %lacc %lrem H
  iexact H

/-- Rocq: `wp_list_sub`. -/
theorem wp_list_sub (k : ℕ) (l : List A) (lv : val) :
    {{ (⌜is_list l lv⌝ : IProp GF) }}
      cpl(v(&list_sub) #(k : ℕ) v(&lv)) @ E
    {{ v, RET v; ⌜is_list (l.take k) v⌝ }} := by
  induction l generalizing k lv with
  | nil =>
    iintro %Φ %Hcoh HΦ
    subst Hcoh
    cases k with
    | zero =>
      wp_rec
      wp_pures'
      iapply HΦ
      ipureintro
      rfl
    | succ k =>
      wp_rec
      wp_pures'
      iapply HΦ
      ipureintro
      rfl
  | cons a l' IH =>
    iintro %Φ %Hcoh HΦ
    obtain ⟨lv', rfl, Hlcoh⟩ := Hcoh
    cases k with
    | zero =>
      wp_rec
      wp_pures'
      iapply HΦ
      ipureintro
      rfl
    | succ k =>
      wp_rec
      wp_pures'
      wp_bind (App (App (Val list_sub) _) _)
      iapply IH k lv' $$ [] [HΦ]
      · ipureintro
        exact Hlcoh
      iintro !> %tl %Hcoh_tl
      wp_pures'
      wp_apply wp_list_cons a (l'.take k) tl $$ [] with %v %Hv
      · ipureintro
        exact Hcoh_tl
      iapply HΦ
      ipureintro
      exact Hv

/-- Rocq: `wp_list_nth`. -/
theorem wp_list_nth (i : ℕ) (l : List A) (lv : val) :
    {{ (⌜is_list l lv⌝ : IProp GF) }}
      cpl(v(&list_nth) v(&lv) #(i : ℕ)) @ E
    {{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜l.length ≤ i⌝) ∨ ⌜∃ r, v = SOMEV (inject r) ∧ l[i]? = some r⌝ }} := by
  induction l generalizing i lv with
  | nil =>
    iintro %Φ %Ha HΦ
    subst Ha
    wp_rec
    wp_pures'
    iapply HΦ
    imodintro
    ileft
    isplit
    · ipureintro
      rfl
    · ipureintro
      exact Nat.zero_le _
  | cons a l' IH =>
    iintro %Φ %Ha HΦ
    obtain ⟨lv', rfl, Hlcoh⟩ := Ha
    cases i with
    | zero =>
      wp_rec
      wp_pures'
      iapply HΦ
      iright
      ipureintro
      exact ⟨a, rfl, rfl⟩
    | succ i =>
      wp_rec
      wp_pures'
      iapply IH i lv' $$ [] [HΦ]
      · ipureintro
        exact Hlcoh
      iintro !> %v Hv
      iapply HΦ
      icases Hv with (⟨%Hv, %Hs⟩ | %Hps)
      · ileft
        isplit
        · ipureintro
          exact Hv
        · ipureintro
          simpa using Hs
      · iright
        ipureintro
        simpa using Hps

/-- Rocq: `wp_list_nth_some`. -/
theorem wp_list_nth_some (i : ℕ) (l : List A) (lv : val) :
    {{ (⌜is_list l lv ∧ i < l.length⌝ : IProp GF) }}
      cpl(v(&list_nth) v(&lv) #(i : ℕ)) @ E
    {{ v, RET v; ⌜∃ r, v = SOMEV (inject r) ∧ l[i]? = some r⌝ }} := by
  iintro %Φ %H HΦ
  obtain ⟨Hcoh, Hi⟩ := H
  iapply wp_list_nth i l lv $$ [] [HΦ]
  · ipureintro
    exact Hcoh
  iintro !> %v Hv
  icases Hv with (⟨-, %H⟩ | %H)
  · exact absurd H (Nat.not_le.2 Hi)
  · iapply HΦ
    ipureintro
    exact H

end list_specs

end Coneris.Lib.List
