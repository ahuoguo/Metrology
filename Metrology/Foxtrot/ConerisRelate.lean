module

public import Metrology.Foxtrot.Weakestpre
public import Metrology.Coneris.Weakestpre

/-!
# Relating the Coneris and Foxtrot weakest preconditions

Ported from clutch/theories/foxtrot/coneris_relate.v

Every Foxtrot ghost-state instance induces a Coneris one (`foxtrotGS_conerisGS`, forgetting
`spec_interp`), and a Coneris WP implies the Foxtrot WP (`coneris_implies_foxtrot`): the
Coneris state steps and program steps are replayed on the LHS while the RHS configuration
(held in `spec_interp`) stutters.

## Rocq → Lean map
* `foxtrotGS_conerisGS` ↦ `Foxtrot.foxtrotGS_conerisGS` (a global instance, as in Rocq).
* `foxtrot_wp` / `coneris_wp` ↦ `Foxtrot.foxtrot_wp` / `Foxtrot.coneris_wp`, i.e. `Wp.wp` at the
  instances `Foxtrot.wp'` / `Coneris.pgl_wp'`. Both are instances of
  `Wp (IProp GF) expr val Stuckness`, so the bare `WP` notation is ambiguous here; the
  statements use these two definitions.
* `state_step_coupl_implies_spec_coupl`, `coneris_prog_coupl_implies_prog_coupl`,
  `coneris_implies_foxtrot`: same names.

## Deviations
* Statements `A -∗ B -∗ C` are entailments `A ⊢ B -∗ C`.
* The Coneris modalities/ghost fields are referred to qualified (`Coneris.state_step_coupl`,
  `Coneris.prog_coupl`, ...), since `Coneris` is not opened (its `state_interp`, `fork_post`,
  `err_interp`, `prog_coupl`, `tape_oblivious_sch` clash with Foxtrot's).
* Rocq's `bool_decide (μ σ > 0)` is a classical `if 0 < μ σ`, the bound `Rmax r 1` is `⊤`,
  and the `SeriesC_ext` argument is `Coneris.Expval_ite_of_support`.
* The `iInduction efs` over the forked threads is `bigSepL_impl`.
* `Unshelve` side goals (`state_step_coupl_pre_mono`, non-expansiveness) are discharged by
  `Coneris.state_step_coupl_ind`.

## Added helpers (not in Rocq)
`foxtrotGS_conerisGS_state_interp`, `foxtrotGS_conerisGS_err_interp`,
`foxtrotGS_conerisGS_fork_post` (rfl lemmas).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

section relate

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]

/-- Rocq: `foxtrotGS_conerisGS`. -/
instance foxtrotGS_conerisGS : Coneris.conerisWpGS con_prob_lang GF where
  conerisWpGS_invGS := foxtrotWpGS.foxtrotWpGS_invGS
  state_interp := state_interp
  fork_post := fork_post
  err_interp := err_interp

/-- Helper (not in Rocq). -/
@[simp] theorem foxtrotGS_conerisGS_state_interp (σ : state) :
    Coneris.state_interp (GF := GF) (Λ := con_prob_lang) σ = state_interp σ := rfl

/-- Helper (not in Rocq). -/
@[simp] theorem foxtrotGS_conerisGS_err_interp (ε : ℝ≥0∞) :
    Coneris.err_interp (GF := GF) (Λ := con_prob_lang) ε = err_interp ε := rfl

/-- Helper (not in Rocq). -/
@[simp] theorem foxtrotGS_conerisGS_fork_post (v : val) :
    Coneris.fork_post (GF := GF) (Λ := con_prob_lang) v = fork_post (Λ := con_prob_lang) v := rfl

/-- Rocq: `foxtrot_wp`. -/
def foxtrot_wp : Stuckness → CoPset → expr → (val → IProp GF) → IProp GF :=
  Wp.wp (self := wp')

/-- Rocq: `coneris_wp`. -/
def coneris_wp : Stuckness → CoPset → expr → (val → IProp GF) → IProp GF :=
  Wp.wp (self := Coneris.pgl_wp')

open Classical in
/-- Rocq: `state_step_coupl_implies_spec_coupl`. -/
theorem state_step_coupl_implies_spec_coupl (σ : state) (ρ : CPState) (ε : ℝ≥0∞)
    (Φ1 : state → ℝ≥0∞ → IProp GF) (Φ2 : state → CPState → ℝ≥0∞ → IProp GF) :
    □ (∀ σ' ε', spec_interp ρ -∗ Φ1 σ' ε' -∗ Φ2 σ' ρ ε') ⊢
      Coneris.state_step_coupl σ ε Φ1 -∗ spec_interp ρ -∗ spec_coupl σ ρ ε Φ2 := by
  iintro #H H'
  iapply Coneris.state_step_coupl_ind
    (fun σ ε => iprop(spec_interp ρ -∗ spec_coupl σ ρ ε Φ2)) Φ1 $$ [] %σ %ε H'
  iintro !> %σ1 %ε1 H' Hspec
  icases H' with (%H' | H' | H' | ⟨%μ, %ε2, %Hμ, %Hr, %Hineq, H'⟩)
  · iapply spec_coupl_ret_err_ge_1 _ _ _ _ H'
  · iapply spec_coupl_ret
    iapply H $$ Hspec H'
  · iapply spec_coupl_amplify
    iintro %ε' %Hε'
    ispecialize H' $$ %ε' %Hε'
    icases H' with ⟨H', -⟩
    iapply H' $$ Hspec
  · iapply spec_coupl_step_l_dret_adv (fun _ => True) μ 0
      (fun σ => if 0 < μ σ then ε2 σ else 1) ρ σ1 Φ2 ε1 Hμ ⟨⊤, fun _ => le_top⟩
      (by rw [zero_add, Coneris.Expval_ite_of_support μ _ ε2 1 fun _ h => h]; exact Hineq)
      (pgl_trivial μ 0)
    iintro %σ2 -
    by_cases h : 0 < μ σ2
    · simp only [ite_eq_left h]
      ispecialize H' $$ %σ2
      imod H'
      icases H' with ⟨H', -⟩
      imodintro
      iapply H' $$ Hspec
    · simp only [ite_eq_right h]
      iclear H'
      imodintro
      iapply spec_coupl_ret_err_ge_1 _ _ _ _ le_rfl

/-- Rocq: `coneris_prog_coupl_implies_prog_coupl`. -/
theorem coneris_prog_coupl_implies_prog_coupl (e : expr) (σ : state) (ρ : CPState) (ε : ℝ≥0∞)
    (Φ1 : expr → state → List expr → ℝ≥0∞ → IProp GF)
    (Φ2 : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) :
    □ (∀ e2 σ2 efs, Φ1 e2 σ2 efs 1) ⊢
      (∀ e' σ' efs ε', spec_interp ρ -∗ Φ1 e' σ' efs ε' -∗ Φ2 e' σ' efs ρ ε') -∗
      Coneris.prog_coupl e σ ε Φ1 -∗
      spec_interp ρ -∗
      prog_coupl e σ ρ ε Φ2 := by
  iintro #foo H Hprog Hspec
  ihave H' := Coneris.prog_coupl_equiv1 e σ ε Φ1 $$ foo Hprog
  icases H' with ⟨%R2, %ε1, %ε2, %Hred, %Hr, %Hineq, %Hpgl, H'⟩
  iapply prog_coupl_step_l_dret_adv ε ε1 ε2 R2 e σ ρ Φ2 Hineq Hred Hr Hpgl
  iintro %e2 %σ2 %efs %HR
  imod H' $$ %e2 %σ2 %efs %HR with H'
  imodintro
  iapply H $$ Hspec H'

/-- Rocq: `coneris_implies_foxtrot`. -/
theorem coneris_implies_foxtrot (s : Stuckness) (E : CoPset) (e : expr) (Φ : val → IProp GF) :
    coneris_wp s E e Φ ⊢ foxtrot_wp s E e Φ := by
  unfold coneris_wp foxtrot_wp
  iloeb as IH generalizing %e %E %Φ
  rw [Coneris.pgl_wp_unfold, wp_unfold]
  iintro H %σ1 %ρ1 %ε1 ⟨H1, H2, H3⟩
  imod H $$ %σ1 %ε1 [H1 H3] with H
  · simp only [foxtrotGS_conerisGS_state_interp, foxtrotGS_conerisGS_err_interp]
    iframe
  imodintro
  iapply state_step_coupl_implies_spec_coupl $$ [] H H2
  iintro !> %σ2 %ε2 Hspec
  cases hv : to_val e with
  | some v =>
    iintro H
    imod H with ⟨Hσ, Hε, HΦ⟩
    imodintro
    iframe
  | none =>
    iintro H
    iapply coneris_prog_coupl_implies_prog_coupl $$ [] [] H Hspec
    · iintro !> %e2 %σ3 %efs !>
      iapply Coneris.state_step_coupl_ret_err_ge_1 _ _ _ le_rfl
    iintro %e' %σ' %efs %ε' Hspec H !>
    iapply state_step_coupl_implies_spec_coupl $$ [] H Hspec
    iintro !> %σ4 %ε4 Hspec H
    imod H with ⟨Hσ, Hε, Hwp, Hefs⟩
    imodintro
    iframe Hσ Hspec Hε
    isplitl [Hwp]
    · iapply IH $$ %e' %E %Φ Hwp
    iapply BigSepL.bigSepL_impl $$ Hefs
    iintro !> %k %ef %_ Hef
    iapply IH $$ %ef %⊤ %(fork_post (Λ := con_prob_lang)) Hef

end relate

end Foxtrot
