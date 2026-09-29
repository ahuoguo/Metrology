module

public import Metrology.Coneris.Weakestpre

/-!
# Lifting lemmas for the Coneris weakest precondition

Ported from clutch/theories/coneris/lifting.v

The lifting lemmas turn the operational semantics of `con_prob_lang` (`prim_step`) into
program-logic rules for the Coneris WP (`Coneris.pgl_wp'`).

## Design choices (Rocq → Lean)

* As in `Coneris.Weakestpre`, the WP variables `s`, `E`, `e1`, `Φ` are implicit; masks that only
  occur in premises (`E'`, `E2`) follow the Rocq explicitness (`E'` explicit in
  `wp_lift_pure_step_no_fork` and `wp_pure_step_fupd`, implicit elsewhere).
* `prim_step e1 σ1 (e2, σ2, efs) > 0` is `0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)`,
  `reducible e1 σ1` is `reducible (Λ := con_prob_lang) e1 σ1`.
* `from_option Φ False (to_val e2)` is `(to_val e2).elim iprop(False) Φ`.
* The `PureExec φ n e1 e2` hypothesis of `wp_pure_step_fupd` / `wp_pure_step_later` is
  instance-implicit (as in iris-lean's `ProgramLogic/Lifting.lean`); the hypothesis `φ` is
  explicit. The iterated step-fupd `|={E}[E']▷=>^n` is iris-lean's `|={E}[E']▷=>^[n]`.
* `nnreal_zero` is `0 : ℝ≥0∞`; `lra` side goals are `simp`.
* `Inhabited (state con_prob_lang)` is kept as an instance argument where Rocq has it
  (`con_prob_lang.state` also has a global `Inhabited` instance).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

section lifting

variable {GF : BundledGFunctors} [conerisWpGS con_prob_lang GF]
variable {s : Stuckness} {E : CoPset} {e1 : expr} {Φ : val → IProp GF}

/-- Rocq: `wp_lift_step_fupd_glm`. -/
theorem wp_lift_step_fupd_glm :
    (∀ (σ1 : state) (ε1 : ℝ≥0∞), state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
      state_step_coupl σ1 ε1 fun σ2 ε2 =>
        match con_prob_lang.to_val e1 with
        | some v => iprop(|={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ Φ v)
        | none => prog_coupl e1 σ2 ε2 fun e3 σ3 efs ε3 => iprop(
            ▷ state_step_coupl σ3 ε3 fun σ4 ε4 => iprop(
              |={∅, E}=> state_interp σ4 ∗ err_interp ε4 ∗ WP e3 @ s; E {{ Φ }} ∗
                [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})))
    ⊢ WP e1 @ s; E {{ Φ }} := by
  rw [pgl_wp_unfold s E e1 Φ]
  exact .rfl

/-- Rocq: `wp_lift_step_fupd`. -/
theorem wp_lift_step_fupd (H : to_val e1 = none) :
    (∀ σ1 : state, state_interp σ1 ={E, ∅}=∗
      ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
      ∀ (e2 : expr) (σ2 : state) (efs : List expr),
        ⌜0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)⌝ ={∅}=∗ ▷ |={∅, E}=>
          state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
          [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})
    ⊢ WP e1 @ s; E {{ Φ }} := by
  iintro H'
  iapply wp_lift_step_fupd_glm
  iintro %σ1 %ε ⟨Hσ, Hε⟩
  imod H' $$ %σ1 Hσ with ⟨%Hs, H'⟩
  imodintro
  iapply state_step_coupl_ret
  simp only [H]
  iapply prog_coupl_prim_step
  · iintro !> %e2 %σ2 %efs !>
    iapply state_step_coupl_ret_err_ge_1 _ _ _ le_rfl
  iexists (fun ρ => True ∧ 0 < prim_step (Λ := con_prob_lang) e1 σ1 ρ), 0, ε
  isplitr
  · ipureintro
    exact Hs
  isplitr
  · ipureintro
    simp
  isplitr
  · ipureintro
    exact pgl_pos_R _ _ _ (pgl_trivial _ 0)
  iintro %e2 %σ2 %efs %⟨-, Hstep⟩
  imod H' $$ %e2 %σ2 %efs %Hstep with H'
  iintro !> !>
  iapply state_step_coupl_ret
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
  iapply wp_lift_step_fupd H
  iintro %σ1 Hσ
  imod H' $$ %σ1 Hσ with ⟨$, H'⟩
  iintro !> %e2 %σ2 %efs %Hstep !> !>
  iapply H' $$ %e2 %σ2 %efs %Hstep

/-- Rocq: `wp_lift_pure_step_no_fork`. -/
theorem wp_lift_pure_step_no_fork [Inhabited state] (E' : CoPset)
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
  iapply wp_lift_step_fupd H
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
    iapply pgl_wp_value' $$ HQ

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
theorem wp_lift_pure_det_step_no_fork [Inhabited state] {E' : CoPset} (e2 : expr)
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
theorem wp_pure_step_fupd [Inhabited state] (E' : CoPset) {e2 : expr} {φ : Prop} {n : ℕ}
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
theorem wp_pure_step_later [Inhabited state] {e2 : expr} {φ : Prop} {n : ℕ}
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

end Coneris
