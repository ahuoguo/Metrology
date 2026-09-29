module

public import Metrology.Coneris.Lifting

/-!
# Lifting lemmas for evaluation-context based languages

Ported from clutch/theories/coneris/ectx_lifting.v

Some derived lemmas for ectx-based languages: lifting lemmas phrased in terms of `head_step`
instead of `prim_step`.

## Design choices (Rocq → Lean)

* The Rocq file works in the canonical `ectx_language` of `con_prob_lang`; here
  `head_reducible e σ` is `conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e σ`, and
  `head_step` is the concrete `con_prob_lang.head_step` (definitionally
  `con_prob_ectx_lang.head_step`, see `con_prob_ectx_lang_head_step`).
* `head_step e1 σ1 (e2, σ2, efs) > 0` is `0 < head_step e1 σ1 (e2, σ2, efs)`;
  `from_option Φ False (to_val e2)` is `(to_val e2).elim iprop(False) Φ` (as in
  `Coneris.Lifting`).
* The section context `{Hinh : Inhabited (state con_prob_lang)}` is an instance argument of the
  two lemmas that use it (`Proof using Hinh`).
* As in `Coneris.Lifting`, the WP variables `s`, `E`, `e1`, `Φ` are implicit.

## Omitted
* `Local Hint Resolve head_prim_reducible head_reducible_prim_step head_stuck_stuck`: the
  lemmas are applied explicitly.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

section wp

variable {GF : BundledGFunctors} [conerisWpGS con_prob_lang GF]
variable {s : Stuckness} {E : CoPset} {e1 : expr} {Φ : val → IProp GF}

/-- Rocq: `wp_lift_head_step_fupd`. -/
theorem wp_lift_head_step_fupd :
    (∀ (σ1 : state) (ε1 : ℝ≥0∞), state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
      ⌜conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e1 σ1⌝ ∗
      state_step_coupl σ1 ε1 fun σ2 ε2 =>
        match con_prob_lang.to_val e1 with
        | some v => iprop(|={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ Φ v)
        | none => prog_coupl e1 σ2 ε2 fun e3 σ3 efs ε3 => iprop(
            ▷ state_step_coupl σ3 ε3 fun σ4 ε4 => iprop(
              |={∅, E}=> state_interp σ4 ∗ err_interp ε4 ∗ WP e3 @ s; E {{ Φ }} ∗
                [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})))
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupd_glm
  iintro %σ1 %ε Hσε
  imod H $$ %σ1 %ε Hσε with ⟨-, H⟩
  imodintro
  iexact H

/-- Rocq: `wp_lift_head_step`. -/
theorem wp_lift_head_step (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E, ∅}=∗
      ⌜conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e1 σ1⌝ ∗
      ▷ ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < head_step e1 σ1 (e2, σ2, efs)⌝ ={∅, E}=∗
          state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H'
  iapply wp_lift_step_fupd H
  iintro %σ1 Hσ
  imod H' $$ %σ1 Hσ with ⟨%Hred, H'⟩
  imodintro
  isplitr
  · ipureintro
    exact conEctxLanguage.head_prim_reducible (Λ := con_prob_ectx_lang) e1 σ1 Hred
  iintro %e2 %σ2 %efs %Hstep !> !>
  iapply H' $$ %e2 %σ2 %efs
    %(conEctxLanguage.head_reducible_prim_step (Λ := con_prob_ectx_lang) e1 σ1 (e2, σ2, efs) Hred Hstep)

/-- Rocq: `wp_lift_atomic_head_step_fupd`. -/
theorem wp_lift_atomic_head_step_fupd {E1 E2 : CoPset} (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E1}=∗
      ⌜conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e1 σ1⌝ ∗
      ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < head_step e1 σ1 (e2, σ2, efs)⌝ ={E1}[E2]▷=∗
          state_interp σ2 ∗ (to_val e2).elim iprop(False) Φ ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E1 {{ Φ }} := by
  iintro H'
  iapply wp_lift_atomic_step_fupd (E2 := E2) H
  iintro %σ1 Hσ1
  imod H' $$ %σ1 Hσ1 with ⟨%Hred, H'⟩
  imodintro
  isplitr
  · ipureintro
    exact conEctxLanguage.head_prim_reducible (Λ := con_prob_ectx_lang) e1 σ1 Hred
  iintro %e2 %σ2 %efs %Hstep
  iapply H' $$ %e2 %σ2 %efs
    %(conEctxLanguage.head_reducible_prim_step (Λ := con_prob_ectx_lang) e1 σ1 (e2, σ2, efs) Hred Hstep)

/-- Rocq: `wp_lift_atomic_head_step`. -/
theorem wp_lift_atomic_head_step (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E}=∗
      ⌜conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e1 σ1⌝ ∗
      ▷ ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < head_step e1 σ1 (e2, σ2, efs)⌝ ={E}=∗
          state_interp σ2 ∗ (to_val e2).elim iprop(False) Φ ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H'
  iapply wp_lift_atomic_step H
  iintro %σ1 Hσ1
  imod H' $$ %σ1 Hσ1 with ⟨%Hred, H'⟩
  imodintro
  isplitr
  · ipureintro
    exact conEctxLanguage.head_prim_reducible (Λ := con_prob_ectx_lang) e1 σ1 Hred
  inext
  iintro %e2 %σ2 %efs %Hstep
  iapply H' $$ %e2 %σ2 %efs
    %(conEctxLanguage.head_reducible_prim_step (Λ := con_prob_ectx_lang) e1 σ1 (e2, σ2, efs) Hred Hstep)

/-- Rocq: `wp_lift_pure_det_head_step_no_fork`. -/
theorem wp_lift_pure_det_head_step_no_fork [Inhabited state] {E' : CoPset} (e2 : expr)
    (_H : to_val e1 = none)
    (Hred : ∀ σ1 : state, conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e1 σ1)
    (Hpuredet : ∀ (σ1 : state) (e2' : expr) (σ2 : state) (efs : List expr),
      0 < head_step e1 σ1 (e2', σ2, efs) → σ2 = σ1 ∧ e2' = e2 ∧ efs = []) :
    (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }} :=
  wp_lift_pure_det_step_no_fork e2
    (fun σ1 => conEctxLanguage.head_prim_reducible (Λ := con_prob_ectx_lang) e1 σ1 (Hred σ1))
    (fun σ1 e2' σ2 efs h => Hpuredet σ1 e2' σ2 efs
      (conEctxLanguage.head_reducible_prim_step (Λ := con_prob_ectx_lang) e1 σ1 _ (Hred σ1) h))

/-- Rocq: `wp_lift_pure_det_head_step_no_fork'`. -/
theorem wp_lift_pure_det_head_step_no_fork' [Inhabited state] (e2 : expr)
    (H : to_val e1 = none)
    (Hred : ∀ σ1 : state, conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e1 σ1)
    (Hpuredet : ∀ (σ1 : state) (e2' : expr) (σ2 : state) (efs : List expr),
      0 < head_step e1 σ1 (e2', σ2, efs) → σ2 = σ1 ∧ e2' = e2 ∧ efs = []) :
    ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }} :=
  (step_fupd_intro LawfulSet.subset_refl).trans
    (wp_lift_pure_det_head_step_no_fork (E' := E) e2 H Hred Hpuredet)

end wp

end Coneris
