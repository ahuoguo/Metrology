module

public import Metrology.Coneris.Lib.ListSpec

/-!
# Lists in `con_prob_lang` (specs of `list_iter`, `list_iteri`)

Ported from clutch/theories/coneris/lib/list.v (section `list_specs`).

## Rocq → Lean
* The Rocq `(Val handler) (inject a)` (with `inject a` coerced to an expression) is
  `App (Val handler) (Val (inject a))`.
* Nested Texan triples in premises are iris-lean's in-`iprop` Texan triples
  (`□ ∀ Φ, P -∗ ▷ (∀ x, Q -∗ Φ v) -∗ WP e @ E {{ Φ }}`), as in Rocq.
* `nonnegreal` error bounds are `ℝ≥0∞`; `nnreal_nat (length l)` is `(l.length : ℝ≥0∞)`.
* `wp_list_iter_idx_aux` is proved by induction on the list (Rocq: Löb induction).
* `wp_list_iter_err`, `wp_list_iter_err_constant` drop the unused (and uninferable) Rocq
  section parameter `Inject B val`.

## Added (not in Rocq)
* `bigSepL_shift_succ` (reindexing, Rocq: `big_sepL_impl` + `lia` inline).
* `ec_split_list` (the inner induction of `wp_list_iter_err_constant` and
  `wp_list_map_err_constant`).
-/

@[expose] public section

open scoped ENNReal
open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs

variable {GF : BundledGFunctors} [conerisGS GF] {A : Type} [Inject A val] {E : CoPset}

/-- Rocq: `wp_list_iter_invariant'`. -/
theorem wp_list_iter_invariant' (Φ1 Φ2 : A → IProp GF) (Ψ : List A → IProp GF) (P : IProp GF)
    (l : List A) (lv handler : val) (lrest : List A) :
    ⊢ (∀ (a : A) (l' : List A),
        {{ ⌜∃ b, lrest ++ l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}
          cpl(v(&handler) v(&(inject a))) @ E
        {{ v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P ∗ Ψ lrest ∗ [∗list] a ∈ l, Φ1 a }}
        cpl(v(&list_iter) v(&handler) v(&lv)) @ E
      {{ RET LitV LitUnit; P ∗ Ψ (lrest ++ l) ∗ [∗list] a ∈ l, Φ2 a }} := by
  induction l generalizing lv lrest with
  | nil =>
    iintro #Helem !> %Φ' ⟨%Ha, HP, Hl, -⟩ Hk
    subst Ha
    wp_rec
    wp_pures
    rw [List.append_nil]
    iapply Hk
    iframe HP Hl
    imodintro
    iempintro
  | cons a l' IH =>
    iintro #Helem !> %Φ' ⟨%Ha, HP, Hl, Ha1, HΦ⟩ Hk
    obtain ⟨lv', rfl, Hlcoh⟩ := Ha
    wp_rec
    wp_pures
    wp_apply Helem $$ %a %lrest [HP Hl Ha1] with %v ⟨HP, Ha, HΦ2⟩
    · iframe HP Hl Ha1
      ipureintro
      exact ⟨l', rfl⟩
    wp_pures
    ihave IH' := IH lv' (lrest ++ [a])
    ispecialize IH' $$ []
    · iintro %a' %lrest' !> %Φ'' ⟨%Hin', HP, Hlrest', HΦ1⟩ Hk'
      iapply Helem $$ %a' %lrest' [HP Hlrest' HΦ1] Hk'
      iframe HP Hlrest' HΦ1
      ipureintro
      obtain ⟨b, Hin'⟩ := Hin'
      exact ⟨b, by simpa using Hin'⟩
    iapply IH' $$ [HP Ha HΦ] [HΦ2 Hk]
    · iframe HP Ha HΦ
      ipureintro
      exact Hlcoh
    iintro !> ⟨HP, Hl, HΦ⟩
    iapply Hk
    isimp only [List.append_assoc, List.singleton_append] at Hl
    iframe HP Hl HΦ HΦ2

/-- Rocq: `wp_list_iter_invariant`. -/
theorem wp_list_iter_invariant (Φ1 Φ2 : A → IProp GF) (Ψ : List A → IProp GF) (P : IProp GF)
    (l : List A) (lv handler : val) :
    ⊢ (∀ (a : A) (l' : List A),
        {{ ⌜∃ b, l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}
          cpl(v(&handler) v(&(inject a))) @ E
        {{ v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P ∗ Ψ [] ∗ [∗list] a ∈ l, Φ1 a }}
        cpl(v(&list_iter) v(&handler) v(&lv)) @ E
      {{ RET LitV LitUnit; P ∗ Ψ l ∗ [∗list] a ∈ l, Φ2 a }} := by
  have H := wp_list_iter_invariant' (E := E) Φ1 Φ2 Ψ P l lv handler []
  simp only [List.nil_append] at H
  exact H

omit [Inject A val] in
/-- Reindexing a big separating conjunction (used for the `n + i` shifts in Rocq's proofs,
which are done there with `big_sepL_impl` and `lia`). -/
theorem bigSepL_shift_succ {PROP : Type _} [BI PROP] (Φ : ℕ → A → PROP) (n : ℕ) (l : List A) :
    ([∗list] k ↦ a ∈ l, Φ (n + (k + 1)) a) = [∗list] k ↦ a ∈ l, Φ (n + 1 + k) a := by
  congr 1
  funext k a
  rw [Nat.add_comm k 1, Nat.add_assoc]

/-- Rocq: `wp_list_iter_idx_aux`. (Rocq proves it by Löb induction; here by induction on the
list.) -/
theorem wp_list_iter_idx_aux (n : ℕ) (Φ Ψ : ℕ → A → IProp GF) (P : IProp GF) (l : List A)
    (lv handler : val) :
    ⊢ (∀ (i : ℕ) (a : A),
        {{ P ∗ Φ i a }} cpl(v(&handler) v(&(inject a))) @ E {{ v, RET v; P ∗ Ψ i a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P ∗ [∗list] i ↦ a ∈ l, Φ (n + i) a }}
        cpl(v(&list_iter) v(&handler) v(&lv)) @ E
      {{ RET LitV LitUnit; P ∗ [∗list] i ↦ a ∈ l, Ψ (n + i) a }} := by
  induction l generalizing lv n with
  | nil =>
    iintro #Helem !> %Φ' ⟨%Ha, HP, -⟩ HΦ
    subst Ha
    wp_rec
    wp_pures
    iapply HΦ
    iframe HP
    imodintro
    iempintro
  | cons a l' IH =>
    iintro #Helem !> %Φ' ⟨%Ha, HP, Ha1, Hl'⟩ HΦ
    obtain ⟨lv', rfl, Hlcoh⟩ := Ha
    wp_rec
    wp_pures
    wp_apply Helem $$ %(n + 0) %a [HP Ha1] with %v ⟨HP, Ha⟩
    · iframe HP Ha1
    wp_pures
    rw [bigSepL_shift_succ]
    iapply IH (n + 1) lv' $$ Helem [HP Hl'] [Ha HΦ]
    · iframe HP Hl'
      ipureintro
      exact Hlcoh
    iintro !> ⟨HP, Hl⟩
    iapply HΦ
    rw [← bigSepL_shift_succ]
    iframe HP Ha Hl

/-- Rocq: `wp_list_iter_idx`. -/
theorem wp_list_iter_idx (Φ Ψ : ℕ → A → IProp GF) (P : IProp GF) (l : List A)
    (lv handler : val) :
    ⊢ (∀ (i : ℕ) (a : A),
        {{ P ∗ Φ i a }} cpl(v(&handler) v(&(inject a))) @ E {{ v, RET v; P ∗ Ψ i a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P ∗ [∗list] i ↦ a ∈ l, Φ i a }}
        cpl(v(&list_iter) v(&handler) v(&lv)) @ E
      {{ RET LitV LitUnit; P ∗ [∗list] i ↦ a ∈ l, Ψ i a }} := by
  have H := wp_list_iter_idx_aux (E := E) 0 Φ Ψ P l lv handler
  simp only [Nat.zero_add] at H
  exact H

/-- Rocq: `wp_list_iter`. -/
theorem wp_list_iter (Φ Ψ : A → IProp GF) (P : IProp GF) (l : List A) (lv handler : val) :
    ⊢ (∀ (a : A),
        {{ P ∗ Φ a }} cpl(v(&handler) v(&(inject a))) @ E {{ v, RET v; P ∗ Ψ a }}) -∗
      {{ ⌜is_list l lv⌝ ∗ P ∗ [∗list] a ∈ l, Φ a }}
        cpl(v(&list_iter) v(&handler) v(&lv)) @ E
      {{ RET LitV LitUnit; P ∗ [∗list] a ∈ l, Ψ a }} := by
  iintro #H
  iapply wp_list_iter_idx (fun _ a => Φ a) (fun _ a => Ψ a) P l lv handler
  iintro %i %a
  iapply H

/-- Rocq: `wp_list_iter_err`. The unused Rocq parameter `Inject B val` is dropped. -/
theorem wp_list_iter_err (l : List A) (fv lv : val) (P Q : A → IProp GF) (err : A → ℝ≥0∞) :
    {{ (∀ (x : A),
          {{ P x ∗ ↯ (err x) }} cpl(v(&fv) v(&(inject x))) @ E {{ fr, RET fr; Q x }}) ∗
        ⌜is_list l lv⌝ ∗
        [∗list] x ∈ l, (P x ∗ ↯ (err x)) }}
      cpl(v(&list_iter) v(&fv) v(&lv)) @ E
    {{ rv, RET rv; [∗list] x ∈ l, Q x }} := by
  iintro %Φ ⟨#Hf, %Hil, HP⟩ HΦ
  iapply wp_list_iter_idx (fun _ a => iprop(P a ∗ ↯ (err a))) (fun _ a => Q a) iprop(True) l lv
    fv $$ [] [HP] [HΦ]
  · iintro %i %a !> %φ ⟨-, Pa, erra⟩ Hφ
    iapply Hf $$ %a [Pa erra]
    · iframe Pa erra
    iintro !> %v Qa
    iapply Hφ
    iframe Qa
  · iframe HP
    ipureintro
    exact Hil
  · iintro !> ⟨-, HQ⟩
    iapply HΦ $$ HQ

omit [Inject A val] in
/-- Splitting `↯ (ε * length l)` into one `↯ ε` per element (the inner induction of Rocq's
`wp_list_iter_err_constant` and `wp_list_map_err_constant`). -/
theorem ec_split_list (P : A → IProp GF) (err : ℝ≥0∞) (l : List A) :
    ([∗list] x ∈ l, P x) ∗ ↯ (err * (l.length : ℝ≥0∞)) ⊢ [∗list] x ∈ l, (P x ∗ ↯ err) := by
  induction l with
  | nil =>
    iintro -
    iempintro
  | cons h t IH =>
    iintro ⟨⟨HP, HP'⟩, Herr⟩
    have Heq : err * ((h :: t).length : ℝ≥0∞) = err + err * (t.length : ℝ≥0∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm]
    rw [Heq]
    icases ErrorCredit.split $$ Herr with ⟨Herr, Herr'⟩
    iframe HP Herr
    iapply IH
    iframe HP' Herr'

/-- Rocq: `wp_list_iter_err_constant`. The unused Rocq parameter `Inject B val` is dropped. -/
theorem wp_list_iter_err_constant (l : List A) (fv lv : val) (P Q : A → IProp GF)
    (err : ℝ≥0∞) :
    {{ (∀ (x : A),
          {{ P x ∗ ↯ err }} cpl(v(&fv) v(&(inject x))) @ E {{ fr, RET fr; Q x }}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗list] x ∈ l, P x) ∗
        ↯ (err * (l.length : ℝ≥0∞)) }}
      cpl(v(&list_iter) v(&fv) v(&lv)) @ E
    {{ rv, RET rv; [∗list] x ∈ l, Q x }} := by
  iintro %Φ ⟨#Hf, %Hil, HP, Herr⟩ HΦ
  ihave HP := ec_split_list P err l $$ [HP Herr]
  · iframe HP Herr
  iapply wp_list_iter_err l fv lv P Q (fun _ => err) $$ [HP] HΦ
  iframe HP Hf
  ipureintro
  exact Hil

/-- Rocq: `wp_list_iteri_loop`. -/
theorem wp_list_iteri_loop (k : ℕ) (l : List A) (fv lv : val) (P : IProp GF)
    (Φ Ψ : ℕ → A → IProp GF) (Hl : is_list l lv) :
    ⊢ (∀ (i : ℕ) (x : A),
        {{ P ∗ Φ i x }} cpl(v(&fv) #(i : ℕ) v(&(inject x))) @ E {{ v, RET v; P ∗ Ψ i x }}) -∗
      {{ P ∗ [∗list] i ↦ a ∈ l, Φ (k + i) a }}
        cpl(v(&list_iteri_loop) v(&fv) #(k : ℕ) v(&lv)) @ E
      {{ RET LitV LitUnit; P ∗ [∗list] i ↦ a ∈ l, Ψ (k + i) a }} := by
  induction l generalizing lv k with
  | nil =>
    iintro #Hf !> %Φ' ⟨HP, -⟩ HΦ
    subst Hl
    wp_rec
    wp_pures
    iapply HΦ
    iframe HP
    imodintro
    iempintro
  | cons h l IH =>
    obtain ⟨l', rfl, Hl'⟩ := Hl
    iintro #Hf !> %Φ' ⟨HP, Ha, Hl'⟩ HΦ
    wp_rec
    wp_pures
    wp_apply Hf $$ %(k + 0) %h [HP Ha] with %v ⟨HP, HΨ⟩
    · iframe HP Ha
    wp_pures
    rw [show ((k : ℕ) : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; rfl, bigSepL_shift_succ]
    iapply IH (k + 1) l' Hl' $$ Hf [HP Hl'] [HΨ HΦ]
    · iframe HP Hl'
    iintro !> ⟨HP, Hl⟩
    iapply HΦ
    rw [← bigSepL_shift_succ]
    iframe HP HΨ Hl

/-- Rocq: `wp_list_iteri`. -/
theorem wp_list_iteri (l : List A) (fv lv : val) (P : IProp GF) (Φ Ψ : ℕ → A → IProp GF)
    (Hl : is_list l lv) :
    ⊢ (∀ (i : ℕ) (x : A),
        {{ P ∗ Φ i x }} cpl(v(&fv) #(i : ℕ) v(&(inject x))) @ E {{ v, RET v; P ∗ Ψ i x }}) -∗
      {{ P ∗ [∗list] i ↦ a ∈ l, Φ i a }}
        cpl(v(&list_iteri) v(&fv) v(&lv)) @ E
      {{ RET LitV LitUnit; P ∗ [∗list] i ↦ a ∈ l, Ψ i a }} := by
  iintro #Hf !> %Φ' ⟨HP, Hown⟩ HΦ
  wp_rec
  wp_pures
  have H := wp_list_iteri_loop (E := E) 0 l fv lv P Φ Ψ Hl
  simp only [Nat.zero_add, Nat.cast_zero] at H
  iapply H $$ Hf [HP Hown] HΦ
  iframe HP Hown

end list_specs

end Coneris.Lib.List
