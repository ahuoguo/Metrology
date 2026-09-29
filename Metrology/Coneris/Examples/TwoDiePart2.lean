module

public import Metrology.Coneris.Examples.TwoDie

/-!
# Two dice (the `con_prog` example of the Coneris paper)

Ported from clutch/theories/coneris/examples/two_die.v (second part: `two_die_prog'`,
section `simple'`)

See `Coneris.Examples.TwoDie` for the Rocq → Lean map, the deviations and the omissions of
the whole Rocq file.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par
open Iris.ExclAuth

namespace Coneris.Examples.TwoDie

/-- Rocq: `two_die_prog'`. This is the `con_prog` example in the paper of Coneris. -/
def two_die_prog' : expr := cpl(
  let l := ref(#0) in
  ((if #0 < rand(#5)
    then faa(l, #1)
    else #()) ‖
   (if #0 < rand(#5)
    then faa(l, #1)
    else #()));
  !l)

section simple'

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [ElemG GF (excl_authF Bool)]

/-- Rocq: `simple_parallel_add_inv'`. -/
def simple_parallel_add_inv' (l : Loc) (γ : GName) : IProp GF :=
  iprop(∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗
    (own_auth γ false ∨ own_auth γ true ∗ ⌜0 < n⌝))

/-- Rocq: `simple_parallel_add_spec'`. -/
theorem simple_parallel_add_spec' :
    {{ ↯ (1 / 6) }} two_die_prog'
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (⌜0 < n⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold two_die_prog'
  wp_pures
  wp_alloc l as Hl
  wp_pures
  imod ghost_var_alloc' false with ⟨%γ, Hauth, Hfrag⟩
  imod inv_alloc nroot ⊤ (simple_parallel_add_inv' l γ) $$ [Hauth Hl] with #I
  · inext
    unfold simple_parallel_add_inv'
    iexists 0
    iframe
  unfold simple_parallel_add_inv'
  wp_apply wp_par' (fun _ => iprop(own_frag γ true)) (fun _ => iprop(True)) $$ [Herr Hfrag] []
  · wp_apply wp_rand_err_nat 5 5 0 rfl
    isplitl [Herr]
    · iapply ErrorCredit.ext _ $$ Herr
      norm_num
    iintro %x %Hx
    wp_pures
    rw [decide_eq_true (by omega)]
    wp_pures
    iinv I with ⟨%n, >Hl, >H⟩ Hclose
    wp_faa
    icases H with (H | ⟨H, %_⟩)
    · imod ghost_var_update' γ true _ _ $$ H Hfrag with ⟨Hauth, Hfrag⟩
      imod Hclose $$ [Hl Hauth]
      · inext
        iexists n + 1
        push_cast
        iframe
        iright
        iframe
        ipureintro
        omega
      imodintro
      iexact Hfrag
    · ihave %H' := ghost_var_agree' $$ H Hfrag
      exact absurd H' (by decide)
  · wp_apply wp_rand 5 5 rfl $$ []
    · itrivial
    iintro %x -
    wp_pures
    by_cases hx : 0 < (x : ℕ)
    · rw [decide_eq_true (by omega)]
      wp_pures
      iinv I with ⟨%n, >Hl, >H⟩ Hclose
      wp_faa
      imod Hclose $$ [Hl H]
      · inext
        iexists n + 1
        push_cast
        iframe
        icases H with (H | ⟨H, %_⟩)
        · ileft
          iexact H
        · iright
          iframe
          ipureintro
          omega
      imodintro
      itrivial
    · rw [decide_eq_false (by omega)]
      wp_pures
      itrivial
  · iintro %v1 %v2 ⟨H, -⟩
    inext
    wp_pures
    iinv I with ⟨%n, >Hl, >(H' | ⟨H', %Hn⟩)⟩ Hclose
    · ihave %H'' := ghost_var_agree' $$ H' H
      exact absurd H'' (by decide)
    wp_load
    imod Hclose $$ [H' Hl]
    · inext
      iexists n
      iframe
      iright
      iframe
      ipureintro
      exact Hn
    imodintro
    iapply HΦ
    ipureintro
    exact Hn

end simple'

end Coneris.Examples.TwoDie
