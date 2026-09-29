module

public import Metrology.Coneris.Lib.ListIter

/-!
# Lists in `con_prob_lang` (higher-order specs, for lists of values)

Ported from clutch/theories/coneris/lib/list.v (section `list_specs_HO`).

## Rocq → Lean
* `zip_with (λ v1 v2, (v1, v2)%V) l1 l2` is `List.zipWith (fun v1 v2 => PairV v1 v2) l1 l2`.
* `wp_list_zip_HO` keeps the unused Rocq parameters `P` and `Q`.
-/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs_HO

variable {GF : BundledGFunctors} [conerisGS GF] {E : CoPset}

/-- Rocq: `is_list_HO`. -/
def is_list_HO : List val → val → Prop
  | [], v => v = NONEV
  | w :: l', v => ∃ lv, v = SOMEV (PairV w lv) ∧ is_list_HO l' lv

/-- Rocq: `is_list_to_HO`. -/
theorem is_list_to_HO {A : Type} [Inject A val] (l : List A) (v : val) :
    is_list l v → is_list_HO (List.map (fun a => inject a) l) v := by
  induction l generalizing v with
  | nil => exact id
  | cons a l IH =>
    rintro ⟨v', rfl, Hv'⟩
    exact ⟨v', rfl, IH v' Hv'⟩

/-- Rocq: `wp_list_cons_HO`. -/
theorem wp_list_cons_HO (w : val) (l : List val) (lv : val) :
    {{ (⌜is_list_HO l lv⌝ : IProp GF) }}
      cpl(v(&list_cons) v(&w) v(&lv)) @ E
    {{ v, RET v; ⌜is_list_HO (w :: l) v⌝ }} := by
  iintro %Φ %Hl HΦ
  wp_rec
  wp_pures'
  iapply HΦ
  ipureintro
  exact ⟨lv, rfl, Hl⟩

/-- Rocq: `wp_list_seq_fun_HO`. -/
theorem wp_list_seq_fun_HO (n m : ℕ) (fv : val) (Q : ℕ → val → IProp GF) :
    {{ (∀ (i : ℕ), {{ True }} cpl(v(&fv) #(i : ℕ)) @ E {{ v, RET v; Q i v }}) }}
      cpl(v(&list_seq_fun) #(n : ℕ) #(m : ℕ) v(&fv)) @ E
    {{ v vs, RET v; ⌜is_list_HO vs v⌝ ∗ ⌜vs.length = m⌝ ∗ [∗list] k ↦ w ∈ vs, Q (n + k) w }} := by
  induction m generalizing n with
  | zero =>
    iintro %Φ #Hf Hφ
    wp_rec
    wp_pures'
    iapply Hφ $$ %_ %([] : List val)
    imodintro
    isplitr
    · ipureintro
      rfl
    isplitr
    · ipureintro
      rfl
    iempintro
  | succ p IHm =>
    iintro %Φ #Hf Hφ
    wp_rec
    wp_pures'
    rw [show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl]
    wp_bind (App (App (App (Val list_seq_fun) _) _) _)
    iapply IHm (n + 1) $$ Hf [Hφ]
    iintro !> %v %vs ⟨%Hv, %Hlenp, Hcont⟩
    wp_apply Hf $$ %n [] with %w Hw
    · itrivial
    wp_apply wp_list_cons_HO w vs v $$ [] with %v' %Hv'
    · ipureintro
      exact Hv
    iapply Hφ
    isplitr
    · ipureintro
      exact Hv'
    isplitr
    · ipureintro
      simp [Hlenp]
    iapply BigSepL.bigSepL_cons.2
    rw [Nat.add_zero, bigSepL_shift_succ]
    iframe Hw Hcont

/-- Rocq: `wp_list_seq_fun_HO_invariant`. -/
theorem wp_list_seq_fun_HO_invariant (Ψ : List val → IProp GF) (n m : ℕ) (fv : val)
    (Q : ℕ → val → IProp GF) :
    ⊢ (∀ (i : ℕ) (l : List val),
        {{ Ψ l }} cpl(v(&fv) #(i : ℕ)) @ E {{ v, RET v; Ψ (v :: l) ∗ Q i v }}) -∗
      {{ Ψ [] }}
        cpl(v(&list_seq_fun) #(n : ℕ) #(m : ℕ) v(&fv)) @ E
      {{ v vs, RET v; ⌜is_list_HO vs v⌝ ∗ ⌜vs.length = m⌝ ∗ Ψ vs ∗
          [∗list] k ↦ w ∈ vs, Q (n + k) w }} := by
  induction m generalizing n with
  | zero =>
    iintro #Hf !> %Φ HΨ HΦ
    wp_rec
    wp_pures'
    iapply HΦ $$ %_ %([] : List val)
    imodintro
    isplitr
    · ipureintro
      rfl
    isplitr
    · ipureintro
      rfl
    iframe HΨ
    iempintro
  | succ p IHm =>
    iintro #Hf !> %Φ HΨ HΦ
    wp_rec
    wp_pures'
    rw [show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl]
    wp_bind (App (App (App (Val list_seq_fun) _) _) _)
    iapply IHm (n + 1) $$ Hf HΨ [HΦ]
    iintro !> %v %vs ⟨%Hv, %Hlenp, HΨ, Hcont⟩
    wp_apply Hf $$ %n %vs HΨ with %w ⟨HΨ, Hw⟩
    wp_apply wp_list_cons_HO w vs v $$ [] with %v' %Hv'
    · ipureintro
      exact Hv
    iapply HΦ
    isplitr
    · ipureintro
      exact Hv'
    isplitr
    · ipureintro
      simp [Hlenp]
    iframe HΨ
    iapply BigSepL.bigSepL_cons.2
    rw [Nat.add_zero, bigSepL_shift_succ]
    iframe Hw Hcont

/-- Rocq: `wp_list_map_HO`. -/
theorem wp_list_map_HO (l : List val) (fv lv : val) (P : val → IProp GF)
    (Q : val → val → IProp GF) :
    {{ (∀ v, {{ P v }} cpl(v(&fv) v(&v)) @ E {{ w, RET w; Q v w }}) ∗
        ⌜is_list_HO l lv⌝ ∗
        [∗list] x ∈ l, P x }}
      cpl(v(&list_map) v(&fv) v(&lv)) @ E
    {{ rv lres, RET rv; ⌜is_list_HO lres rv⌝ ∗ [∗list] p ∈ List.zip l lres, Q p.1 p.2 }} := by
  induction l generalizing lv with
  | nil =>
    iintro %Φ ⟨#Hf, %Hil, -⟩ HΦ
    subst Hil
    wp_rec
    wp_pures'
    iapply HΦ $$ %_ %([] : List val)
    imodintro
    isplit
    · ipureintro
      rfl
    · iempintro
  | cons h t IH =>
    iintro %Φ ⟨#Hf, %Hil, HP, HP'⟩ HΦ
    obtain ⟨lv', rfl, Hil'⟩ := Hil
    wp_rec
    wp_pures'
    wp_bind (App (App (Val list_map) _) _)
    iapply IH lv' $$ [HP'] [HP HΦ]
    · iframe Hf HP'
      ipureintro
      exact Hil'
    iintro !> %rv %lres ⟨%Hil_rv, Hzip⟩
    wp_pures'
    wp_apply Hf $$ %h HP with %w HQ
    wp_apply wp_list_cons_HO w lres rv $$ [] with %v %Hilf
    · ipureintro
      exact Hil_rv
    iapply HΦ $$ %_ %(w :: lres)
    isplitr
    · ipureintro
      exact Hilf
    rw [List.zip_cons_cons]
    iapply BigSepL.bigSepL_cons.2
    iframe HQ Hzip

/-- Rocq: `wp_list_zip_HO`. -/
theorem wp_list_zip_HO (l1 l2 : List val) (fv lv1 lv2 : val) (_P : val → IProp GF)
    (_Q : val → val → IProp GF) :
    {{ (⌜is_list_HO l1 lv1⌝ ∗ ⌜is_list_HO l2 lv2⌝ : IProp GF) }}
      cpl(v(&list_zip) v(&fv) v(&lv1) v(&lv2)) @ E
    {{ rv, RET rv; ⌜is_list_HO (List.zipWith (fun v1 v2 => PairV v1 v2) l1 l2) rv⌝ }} := by
  induction l1 generalizing l2 lv2 lv1 with
  | nil =>
    iintro %Φ ⟨%Hl1, %Hl2⟩ HΦ
    subst Hl1
    wp_rec
    wp_pures'
    iapply HΦ
    ipureintro
    rfl
  | cons a1 l1' IH =>
    iintro %Φ ⟨%Hl1, %Hl2⟩ HΦ
    obtain ⟨lv1', rfl, Hl1'⟩ := Hl1
    cases l2 with
    | nil =>
      subst Hl2
      wp_rec
      wp_pures'
      iapply HΦ
      ipureintro
      rfl
    | cons a2 l2' =>
      obtain ⟨lv2', rfl, Hl2'⟩ := Hl2
      wp_rec
      wp_pures'
      wp_bind (App (App (App (Val list_zip) _) _) _)
      iapply IH l2' lv1' lv2' $$ [] [HΦ]
      · iframe
        ipureintro
        exact ⟨Hl1', Hl2'⟩
      iintro !> %rv %Hr
      wp_pures'
      wp_apply wp_list_cons_HO (PairV a1 a2) _ rv $$ [] with %v %Hv
      · ipureintro
        exact Hr
      iapply HΦ
      ipureintro
      exact Hv

/-- Rocq: `wp_list_iter_invariant_HO'`. -/
theorem wp_list_iter_invariant_HO' (Ψ : List val → List val → IProp GF) (l : List val)
    (fv lv : val) (lrest : List val) :
    ⊢ (∀ (lpre : List val) (w : val) (lsuf : List val),
        {{ Ψ lpre (w :: lsuf) }} cpl(v(&fv) v(&w)) @ E {{ v, RET v; Ψ (lpre ++ [w]) lsuf }}) -∗
      {{ ⌜is_list_HO l lv⌝ ∗ Ψ lrest l }}
        cpl(v(&list_iter) v(&fv) v(&lv)) @ E
      {{ RET LitV LitUnit; Ψ (lrest ++ l) [] }} := by
  induction l generalizing lv lrest with
  | nil =>
    iintro #Helem !> %Φ' ⟨%Hlist, HΨ⟩ HΦ'
    subst Hlist
    wp_rec
    wp_pures'
    iapply HΦ'
    rw [List.append_nil]
    iexact HΨ
  | cons a l' IH =>
    iintro #Helem !> %Φ' ⟨%Hlist, HΨ⟩ HΦ'
    obtain ⟨lv', rfl, Hlcoh⟩ := Hlist
    wp_rec
    wp_pures'
    wp_apply Helem $$ %lrest %a %l' HΨ with %v HΨ
    wp_pures'
    iapply IH lv' (lrest ++ [a]) $$ Helem [HΨ] [HΦ']
    · iframe HΨ
      ipureintro
      exact Hlcoh
    iintro !> HΨ
    iapply HΦ'
    isimp only [List.append_assoc, List.singleton_append] at HΨ
    iexact HΨ

/-- Rocq: `wp_list_iter_invariant_HO`. -/
theorem wp_list_iter_invariant_HO (Ψ : List val → List val → IProp GF) (l : List val)
    (fv lv : val) :
    ⊢ (∀ (lpre : List val) (w : val) (lsuf : List val),
        {{ Ψ lpre (w :: lsuf) }} cpl(v(&fv) v(&w)) @ E {{ v, RET v; Ψ (lpre ++ [w]) lsuf }}) -∗
      {{ ⌜is_list_HO l lv⌝ ∗ Ψ [] l }}
        cpl(v(&list_iter) v(&fv) v(&lv)) @ E
      {{ RET LitV LitUnit; Ψ l [] }} := by
  have H := wp_list_iter_invariant_HO' (E := E) Ψ l fv lv []
  simp only [List.nil_append] at H
  exact H

end list_specs_HO

end Coneris.Lib.List
