module

public import Metrology.Coneris.Lib.ListIter

/-!
# Lists in `con_prob_lang` (specs of `list_map`)

Ported from clutch/theories/coneris/lib/list.v (section `list_specs_extra`, first part).

## Rocq → Lean
* `zip l (List.map f l)` is `List.zip l (List.map f l)`; `fst p`, `snd p` are `p.1`, `p.2`.
* `nonnegreal` error bounds are `ℝ≥0∞`; `nnreal_nat (length l)` is `(l.length : ℝ≥0∞)`.
* In `wp_list_map_err_constant`, the splitting of the credits is `ec_split_list`
  (`Coneris.Lib.ListIter`), shared with `wp_list_iter_err_constant`.
-/

@[expose] public section

open scoped ENNReal
open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs_extra

variable {GF : BundledGFunctors} [conerisGS GF] {A : Type} [Inject A val] {E : CoPset}

/-- Rocq: `wp_list_map`. -/
theorem wp_list_map {B : Type} [Inject B val] (l : List A) (f : A → B) (fv lv : val)
    (P : A → IProp GF) (Q : A → val → IProp GF) :
    {{ (∀ (x : A),
          {{ P x }} cpl(v(&fv) v(&(inject x))) @ E
          {{ fr, RET fr; ⌜fr = inject (f x)⌝ ∗ Q x fr }}) ∗
        ⌜is_list l lv⌝ ∗
        [∗list] x ∈ l, P x }}
      cpl(v(&list_map) v(&fv) v(&lv)) @ E
    {{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
        [∗list] p ∈ List.zip l (List.map f l), Q p.1 (inject p.2) }} := by
  induction l generalizing lv with
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
    iintro !> %rv ⟨%Hil_rv, Hzip⟩
    wp_pures'
    wp_apply Hf $$ %h HP with %fr ⟨%Hfr, HQ⟩
    subst Hfr
    wp_apply wp_list_cons (f h) (List.map f t) rv $$ [] with %v %Hilf
    · ipureintro
      exact Hil_rv
    iapply HΦ
    rw [List.map_cons, List.zip_cons_cons]
    isplitr
    · ipureintro
      exact Hilf
    iapply BigSepL.bigSepL_cons.2
    iframe HQ Hzip

/-- Rocq: `wp_list_map_pure`. -/
theorem wp_list_map_pure {B : Type} [Inject B val] (l : List A) (f : A → B) (fv lv : val) :
    {{ (∀ (x : A),
          {{ (True : IProp GF) }} cpl(v(&fv) v(&(inject x))) @ E
          {{ fr, RET fr; ⌜fr = inject (f x)⌝ }}) ∗
        ⌜is_list l lv⌝ }}
      cpl(v(&list_map) v(&fv) v(&lv)) @ E
    {{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ }} := by
  iintro %Φ ⟨#H, %Hl⟩ HΦ
  iapply wp_list_map l f fv lv (fun _ => iprop(True)) (fun _ _ => iprop(True)) $$ [] [HΦ]
  · isplitr
    · iintro %x !> %Ψ - K
      wp_apply H $$ %x [] with %fr %Hfr
      · itrivial
      iapply K
      isplit
      · ipureintro
        exact Hfr
      · itrivial
    isplit
    · ipureintro
      exact Hl
    · iapply BigSepL.bigSepL_intro (P := iprop(emp : IProp GF)) (fun _ _ _ => true_intro)
      iempintro
  iintro !> %rv ⟨%Hrv, -⟩
  iapply HΦ
  ipureintro
  exact Hrv

/-- Rocq: `wp_list_map_err`. -/
theorem wp_list_map_err {B : Type} [Inject B val] (l : List A) (f : A → B) (fv lv : val)
    (P : A → IProp GF) (Q : A → val → IProp GF) (err : A → ℝ≥0∞) :
    {{ (∀ (x : A),
          {{ P x ∗ ↯ (err x) }} cpl(v(&fv) v(&(inject x))) @ E
          {{ fr, RET fr; ⌜fr = inject (f x)⌝ ∗ Q x fr }}) ∗
        ⌜is_list l lv⌝ ∗
        [∗list] x ∈ l, (P x ∗ ↯ (err x)) }}
      cpl(v(&list_map) v(&fv) v(&lv)) @ E
    {{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
        [∗list] p ∈ List.zip l (List.map f l), Q p.1 (inject p.2) }} := by
  iintro %Φ ⟨#Hf, %Hil, HP⟩ HΦ
  iapply wp_list_map l f fv lv (fun x => iprop(P x ∗ ↯ (err x))) Q $$ [HP] HΦ
  iframe Hf HP
  ipureintro
  exact Hil

/-- Rocq: `wp_list_map_err_constant`. -/
theorem wp_list_map_err_constant {B : Type} [Inject B val] (l : List A) (f : A → B)
    (fv lv : val) (P : A → IProp GF) (Q : A → val → IProp GF) (err : ℝ≥0∞) :
    {{ (∀ (x : A),
          {{ P x ∗ ↯ err }} cpl(v(&fv) v(&(inject x))) @ E
          {{ fr, RET fr; ⌜fr = inject (f x)⌝ ∗ Q x fr }}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗list] x ∈ l, P x) ∗
        ↯ (err * (l.length : ℝ≥0∞)) }}
      cpl(v(&list_map) v(&fv) v(&lv)) @ E
    {{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ ∗
        [∗list] p ∈ List.zip l (List.map f l), Q p.1 (inject p.2) }} := by
  iintro %Φ ⟨#Hf, %Hil, HP, Herr⟩ HΦ
  ihave HP := ec_split_list P err l $$ [HP Herr]
  · iframe HP Herr
  iapply wp_list_map l f fv lv (fun x => iprop(P x ∗ ↯ err)) Q $$ [HP] HΦ
  iframe Hf HP
  ipureintro
  exact Hil

end list_specs_extra

end Coneris.Lib.List
