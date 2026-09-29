module

public import Metrology.Coneris.Lib.ListIter

/-!
# Lists in `con_prob_lang` (specs of `list_make`, `list_seq`, `list_seq_fun`)

Ported from clutch/theories/coneris/lib/list.v (end of section `list_specs_extra`).

## Rocq → Lean
* `repeat a n` is `List.replicate n a`; `seq n m` is `List.range' n m`.
* In `wp_list_seq_fun`, the list `vs` of the postcondition is a list of values
  (`List val`, with `Inject_val`), as forced in Rocq by `Q (n + k) v` with `Q : nat → val → iProp Σ`.
-/

@[expose] public section

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.List

section list_specs_extra

variable {GF : BundledGFunctors} [conerisGS GF] {A : Type} [Inject A val] {E : CoPset}

/-- Rocq: `wp_list_make`. -/
theorem wp_list_make (n : ℕ) (a : A) :
    {{ (True : IProp GF) }}
      cpl(v(&list_make) #(n : ℕ) v(&(inject a))) @ E
    {{ v, RET v; ⌜is_list (List.replicate n a) v⌝ }} := by
  induction n with
  | zero =>
    iintro %Φ - Hφ
    wp_rec
    wp_pures'
    iapply Hφ
    ipureintro
    rfl
  | succ p IHm =>
    iintro %Φ - Hφ
    wp_rec
    wp_pures'
    wp_bind (App (App (Val list_make) _) _)
    iapply IHm $$ [] [Hφ]
    · itrivial
    iintro !> %v %Hv
    wp_apply wp_list_cons a (List.replicate p a) v $$ [] with %v' %Hv'
    · ipureintro
      exact Hv
    iapply Hφ
    ipureintro
    exact Hv'

/-- Rocq: `wp_list_seq`. -/
theorem wp_list_seq (n m : ℕ) :
    {{ (True : IProp GF) }}
      cpl(v(&list_seq) #(n : ℕ) #(m : ℕ)) @ E
    {{ v, RET v; ⌜is_list (List.range' n m) v⌝ }} := by
  induction m generalizing n with
  | zero =>
    iintro %Φ - Hφ
    wp_rec
    wp_pures'
    iapply Hφ
    ipureintro
    rfl
  | succ p IHm =>
    iintro %Φ - Hφ
    wp_rec
    wp_pures'
    rw [show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl]
    wp_bind (App (App (Val list_seq) _) _)
    iapply IHm (n + 1) $$ [] [Hφ]
    · itrivial
    iintro !> %v %Hv
    wp_apply wp_list_cons n (List.range' (n + 1) p) v $$ [] with %v' %Hv'
    · ipureintro
      exact Hv
    iapply Hφ
    ipureintro
    exact Hv'

/-- Rocq: `wp_list_seq_fun`. -/
theorem wp_list_seq_fun (n m : ℕ) (f : ℕ → A) (fv : val) (Q : ℕ → val → IProp GF) :
    {{ (∀ (i : ℕ),
          {{ True }} cpl(v(&fv) #(i : ℕ)) @ E {{ fr, RET fr; ⌜fr = inject (f i)⌝ ∗ Q i fr }}) }}
      cpl(v(&list_seq_fun) #(n : ℕ) #(m : ℕ) v(&fv)) @ E
    {{ v (vs : List val), RET v; ⌜is_list vs v⌝ ∗ [∗list] k ↦ v ∈ vs, Q (n + k) v }} := by
  induction m generalizing n with
  | zero =>
    iintro %Φ #Hf Hφ
    wp_rec
    wp_pures'
    iapply Hφ $$ %_ %([] : List val)
    imodintro
    isplit
    · ipureintro
      rfl
    · iempintro
  | succ p IHm =>
    iintro %Φ #Hf Hφ
    wp_rec
    wp_pures'
    rw [show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl]
    wp_bind (App (App (App (Val list_seq_fun) _) _) _)
    iapply IHm (n + 1) $$ Hf [Hφ]
    iintro !> %v %vs ⟨%Hv, Hcont⟩
    wp_apply Hf $$ %n [] with %w ⟨%Hw, HQ⟩
    · itrivial
    subst Hw
    wp_apply wp_list_cons (inject (f n) : val) vs v $$ [] with %v' %Hv'
    · ipureintro
      exact Hv
    iapply Hφ
    isplitr
    · ipureintro
      exact Hv'
    iapply BigSepL.bigSepL_cons.2
    rw [Nat.add_zero, bigSepL_shift_succ]
    iframe HQ Hcont

end list_specs_extra

end Coneris.Lib.List
