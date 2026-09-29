module

public import Metrology.Foxtrot.Weakestpre

/-!
# Lifting lemmas for the Foxtrot weakest precondition

Ported from clutch/theories/foxtrot/lifting.v

The "lifting lemmas" in this file serve to lift the rules of the operational semantics
(`prim_step` of `con_prob_lang`) to the program logic (the Foxtrot WP `Foxtrot.wp'`).

## Rocq → Lean map
All Rocq names are kept: `wp_lift_step_couple`, `wp_lift_step_spec_couple`,
`wp_lift_step_prog_couple`, `wp_lift_step_later`, `wp_lift_step`, `wp_lift_pure_step_no_fork`,
`wp_lift_atomic_step_fupd`, `wp_lift_atomic_step`, `wp_lift_pure_det_step_no_fork`,
`wp_pure_step_fupd`, `wp_pure_step_later`.

## Design choices / deviations (Rocq → Lean)
The file follows `Metrology/Coneris/Lifting.lean`:
* As in `Foxtrot.Weakestpre`, the WP variables `s`, `E`, `e1`, `Φ` are implicit; masks that only
  occur in premises (`E'`, `E2`) follow the Rocq explicitness (`E'` explicit in
  `wp_lift_pure_step_no_fork` and `wp_pure_step_fupd`, implicit elsewhere).
* RHS configurations are `CPState` (local notation for `(con_lang_mdp con_prob_lang).mdpstate`),
  errors are `ℝ≥0∞`.
* `prim_step e1 σ1 (e2, σ2, efs) > 0` is `0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)`,
  `reducible e1 σ1` is `reducible (Λ := con_prob_lang) e1 σ1`.
* `from_option Φ False (to_val e2)` is `(to_val e2).elim iprop(False) Φ`.
* The `PureExec φ n e1 e2` hypothesis of `wp_pure_step_fupd` / `wp_pure_step_later` is
  instance-implicit (as in iris-lean's `ProgramLogic/Lifting.lean`); the hypothesis `φ` is
  explicit. The iterated step-fupd `|={E}[E']▷=>^n` is iris-lean's `|={E}[E']▷=>^[n]`.
* Rocq's `inhabitant` (for `state con_prob_lang`) is the global instance `state_inhabited`
  (`default`); unlike Coneris no `Inhabited` argument is needed, matching Rocq Foxtrot.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

section lifting

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]
variable {s : Stuckness} {E : CoPset} {e1 : expr} {Φ : val → IProp GF}

/-- Rocq: `wp_lift_step_couple`. -/
theorem wp_lift_step_couple :
    (∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞),
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 fun σ2 ρ2 ε2 =>
        match con_prob_lang.to_val e1 with
        | some v => iprop(|={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ Φ v)
        | none => prog_coupl e1 σ2 ρ2 ε2 fun e3 σ3 efs ρ3 ε3 => iprop(
            ▷ spec_coupl σ3 ρ3 ε3 fun σ4 ρ4 ε4 => iprop(
              |={∅, E}=> state_interp σ4 ∗ spec_interp ρ4 ∗ err_interp ε4 ∗
                WP e3 @ s; E {{ Φ }} ∗
                [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})))
    ⊢ WP e1 @ s; E {{ Φ }} := by
  rw [wp_unfold s E e1 Φ]
  exact .rfl

/-- Rocq: `wp_lift_step_spec_couple`. -/
theorem wp_lift_step_spec_couple :
    (∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞),
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 fun σ2 ρ2 ε2 => iprop(
        |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ WP e1 @ s; E {{ Φ }}))
    ⊢ WP e1 @ s; E {{ Φ }} :=
  spec_coupl_wp

/-- Rocq: `wp_lift_step_prog_couple`. -/
theorem wp_lift_step_prog_couple (H : to_val e1 = none) :
    (∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞),
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      prog_coupl e1 σ1 ρ1 ε1 fun e2 σ2 efs ρ2 ε2 => iprop(
        ▷ |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗
          WP e2 @ s; E {{ Φ }} ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }}))
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H'
  iapply wp_lift_step_couple
  iintro %σ1 %ρ1 %ε1 Hs
  imod H' $$ %σ1 %ρ1 %ε1 Hs with H'
  imodintro
  iapply spec_coupl_ret
  simp only [H]
  iapply prog_coupl_mono $$ [] H'
  iintro %e2 %σ2 %efs %ρ2 %ε2 H !>
  iapply spec_coupl_ret
  iexact H

/-- Rocq: `wp_lift_step_later`. -/
theorem wp_lift_step_later (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E, ∅}=∗
      ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
      ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)⌝ ={∅}=∗ ▷ |={∅, E}=>
          state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H'
  iapply wp_lift_step_prog_couple H
  iintro %σ1 %ρ1 %ε1 ⟨Hσ, Hρ, Hε⟩
  imod H' $$ %σ1 Hσ with ⟨%Hs, H'⟩
  imodintro
  iapply prog_coupl_step_l e1 σ1 ρ1 ε1 _ Hs
  iintro %e2 %σ2 %efs %Hstep
  imod H' $$ %e2 %σ2 %efs %Hstep with H'
  iintro !> !>
  imod H' with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  iframe

/-! ### Derived lifting lemmas -/

/-- Rocq: `wp_lift_step`. -/
theorem wp_lift_step (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E, ∅}=∗
      ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
      ▷ ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)⌝ ={∅, E}=∗
          state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H'
  iapply wp_lift_step_later H
  iintro %σ1 Hσ
  imod H' $$ %σ1 Hσ with ⟨$, H'⟩
  iintro !> %e2 %σ2 %efs %Hstep !> !>
  iapply H' $$ %e2 %σ2 %efs %Hstep

/-- Rocq: `wp_lift_pure_step_no_fork`. -/
theorem wp_lift_pure_step_no_fork (E' : CoPset)
    (Hsafe : ∀ σ1 : state, reducible (Λ := con_prob_lang) e1 σ1)
    (Hstep : ∀ (σ1 : state) (e2 : expr) (σ2 : state) (efs : List expr),
      0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs) → σ2 = σ1 ∧ efs = []) :
    (|={E}[E']▷=> ∀ (e2 : expr) (σ : state) (efs : List expr),
      ⌜0 < prim_step (Λ := con_prob_lang) e1 σ (e2, σ, efs)⌝ → WP e2 @ s; E {{ Φ }})
    ⊢ WP e1 @ s; E {{ Φ }} := by
  have Hnv : to_val e1 = none := by
    obtain ⟨ρ, hρ⟩ := Hsafe default
    exact ConProbLang.val_stuck (Λ := con_prob_lang) e1 default ρ hρ
  iintro H
  iapply wp_lift_step Hnv
  iintro %σ1 Hσ
  imod H
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact Hsafe σ1
  inext
  iintro %e2 %σ2 %efs %Hprim
  obtain ⟨rfl, rfl⟩ := Hstep _ _ _ _ Hprim
  imod Hclose with -
  imod H
  imodintro
  ispecialize H $$ %e2 %σ2 %([] : List expr) %Hprim
  iframe
  iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
  iempintro

/-- Rocq: `wp_lift_atomic_step_fupd`. Atomic steps don't need any mask-changing business here,
one can use the generic lemmas here. -/
theorem wp_lift_atomic_step_fupd {E1 E2 : CoPset} (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E1}=∗
      ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
      ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)⌝ ={E1}[E2]▷=∗
          state_interp σ2 ∗ (to_val e2).elim iprop(False) Φ ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E1 {{ Φ }} := by
  iintro H'
  iapply wp_lift_step_later H
  iintro %σ1 Hσ1
  imod H' $$ %σ1 Hσ1 with ⟨$, H'⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose %e2 %σ2 %efs %Hs
  imod Hclose with -
  imod H' $$ %e2 %σ2 %efs %Hs with H'
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose !>
  imod Hclose with -
  imod H' with ⟨Hσ, HQ, Hefs⟩
  cases hv : to_val e2 with
  | none =>
    simp only [Option.elim]
    iexfalso
    iexact HQ
  | some v =>
    obtain rfl : Val v = e2 := ConProbLang.of_to_val (Λ := con_prob_lang) e2 v hv
    simp only [Option.elim]
    imodintro
    iframe Hσ Hefs
    iapply wp_value' $$ HQ

/-- Rocq: `wp_lift_atomic_step`. -/
theorem wp_lift_atomic_step (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E}=∗
      ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
      ▷ ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)⌝ ={E}=∗
          state_interp σ2 ∗ (to_val e2).elim iprop(False) Φ ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H'
  iapply wp_lift_atomic_step_fupd (E2 := E) H
  iintro %σ1 Hσ
  imod H' $$ %σ1 Hσ with ⟨$, H'⟩
  iintro !> %e2 %σ2 %efs %Hstep !> !>
  iapply H' $$ %e2 %σ2 %efs %Hstep

/-- Rocq: `wp_lift_pure_det_step_no_fork`. -/
theorem wp_lift_pure_det_step_no_fork {E' : CoPset} (e2 : expr)
    (Hsafe : ∀ σ1 : state, reducible (Λ := con_prob_lang) e1 σ1)
    (Hpuredet : ∀ (σ1 : state) (e2' : expr) (σ2 : state) (efs : List expr),
      0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2', σ2, efs) →
        σ2 = σ1 ∧ e2' = e2 ∧ efs = []) :
    (|={E}[E']▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_pure_step_no_fork E' Hsafe
    (fun σ1 e2' σ2 efs h => ⟨(Hpuredet σ1 e2' σ2 efs h).1, (Hpuredet σ1 e2' σ2 efs h).2.2⟩)
  iapply step_fupd_wand $$ H
  iintro H %e' %σ %efs %Hs
  obtain ⟨-, rfl, rfl⟩ := Hpuredet _ _ _ _ Hs
  iexact H

/-- Rocq: `wp_pure_step_fupd`. -/
theorem wp_pure_step_fupd (E' : CoPset) {e2 : expr} {φ : Prop} {n : ℕ}
    [Hexec : PureExec (Λ := con_prob_lang) φ n e1 e2] (Hφ : φ) :
    (|={E}[E']▷=>^[n] WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }} := by
  have Hexec' := Hexec.pure_exec Hφ
  clear Hexec
  induction Hexec' with
  | nsteps_O e => exact .rfl
  | nsteps_l n e1 e2 e3 Hstep _ IH =>
    obtain ⟨Hsafe, Hdet⟩ := Hstep
    simp only [Nat.repeat]
    refine .trans ?_ (wp_lift_pure_det_step_no_fork (E' := E') e2 Hsafe ?_)
    · exact step_fupd_mono IH
    · intro σ1 e2' σ2 efs Hpstep
      have := pmf_1_supp_eq _ _ _ (Hdet σ1) Hpstep
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl, rfl⟩ := this
      exact ⟨rfl, rfl, rfl⟩

/-- Rocq: `wp_pure_step_later`. -/
theorem wp_pure_step_later {e2 : expr} {φ : Prop} {n : ℕ}
    [Hexec : PureExec (Λ := con_prob_lang) φ n e1 e2] (Hφ : φ) :
    ▷^[n] WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_pure_step_fupd E Hφ)
  clear Hexec Hφ
  generalize (WP e2 @ s; E {{ Φ }}) = P
  induction n with
  | zero => exact .rfl
  | succ n IH =>
    simp only [Nat.repeat]
    rw [(laterN_succ_left n).to_eq]
    exact (later_mono IH).trans (step_fupd_intro LawfulSet.subset_refl)

end lifting

end Foxtrot
