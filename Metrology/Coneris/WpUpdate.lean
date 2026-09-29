module

public import Metrology.Coneris.PrimitiveLaws
public import Iris.Instances.Lib.Invariants

/-!
# The `wp_update` and `state_update` modalities of Coneris

Ported from clutch/theories/coneris/wp_update.v

This file defines the probabilistic update modality from the Coneris paper, which is called
`state_update` in this development. `state_update` implies `wp_update`, a weaker modality
describing propositions that can be eliminated when the goal is a WP (e.g. state steps).

## Design choices (Rocq → Lean)

* Sealing (`seal`/`unseal`) is mimicked by a pair of `def`s: `wp_update_def` and
  `wp_update := wp_update_def` (resp. `state_update_def`, `state_update`), with the `rfl`
  equations `wp_update_unseal`/`state_update_unseal`. Being `def`s, they are opaque to instance
  search, as the sealed Rocq definitions.
* `wp_update_unfold` is stated as an equation (Rocq: `⊣⊢`), so that it can be used with `rw`.
* Proof-mode instances follow iris-lean's `ProofMode/InstancesUpdates.lean` (for `bupd`):
  `ElimModal` carries the `InOut` parameter, `IntoWand` the `WandMode` parameter,
  `FromPure` the `InOut` parameter of the pure proposition, `FromExist` is `FromExists`, and
  Rocq's `KnownRFromAssumption` is iris-lean's `FromAssumption` (with the `InOut` parameter).
  `into_wand_bupd_args`/`into_wand_bupd_args_state_update` are restricted to the
  `.matching s` modes and get `priority := low`, like iris-lean's `intoWand_bupd_args`.
* The instances whose goal is a WP (`elim_modal_wp_update_wp`, `elim_modal_state_update_wp`)
  are stated for an arbitrary stuckness `s` (the Coneris WP ignores it,
  `pgl_wp_stuckness_irrel` in `Metrology.Coneris.Weakestpre`), while `wp_update_def` uses the
  WP of the notation `WP e @ E {{ Φ }}` (Rocq: stuckness `()`).
* Errors are `ℝ≥0∞`: in `*_epsilon_err` the Rocq `nonnegreal` subtraction `(ε' - ε) H'` is
  the truncated subtraction `ε' - ε`.
* `state_update_ra_alloc` is stated for an iris-lean `ElemG GF F` and `a : F.ap (IProp GF)`
  (Rocq: `inG Σ A`, `a : A`), like iris-lean's `iOwn_alloc`.
* In `pgl_wp_pre'`, Rocq's `▷ state_interp σ3 ∗ …` is parenthesised as
  `(▷ state_interp σ3) ∗ …` (Rocq's `▷` binds tighter than `∗`).

## Omitted
* `wp_update_aux`/`state_update_aux` (the seals, see above).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

/-! ## The `wp_update` modality -/

section wp_update

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `wp_update_def`. -/
def wp_update_def (E : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ (e : expr) (Φ : val → IProp GF), (P -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }})

/-- Rocq: `wp_update`. -/
def wp_update (E : CoPset) (P : IProp GF) : IProp GF := wp_update_def E P

/-- Rocq: `wp_update_unseal`. -/
theorem wp_update_unseal : @wp_update GF _ = @wp_update_def GF _ := rfl

/-- Rocq: `elim_modal_wp_update_wp`. -/
instance elim_modal_wp_update_wp {p : Bool} {io : InOut} {s : Stuckness} {e : expr}
    {E : CoPset} {P : IProp GF} {Φ : val → IProp GF} :
    ElimModal True p io false (wp_update E P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }})
    where
  elim_modal _ := by
    rw [pgl_wp_stuckness_irrel s E e Φ]
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    unfold wp_update wp_update_def
    iintro ⟨Hu, Hw⟩
    iapply Hu $$ Hw

/-- Rocq: `wp_update_ret`. -/
theorem wp_update_ret (E : CoPset) (P : IProp GF) : P ⊢ wp_update E P := by
  unfold wp_update wp_update_def
  iintro HP %e %Φ Hwp
  iapply Hwp $$ HP

/-- Rocq: `wp_update_bind`. -/
theorem wp_update_bind (E : CoPset) (P Q : IProp GF) :
    wp_update E P ∗ (P -∗ wp_update E Q) ⊢ wp_update E Q := by
  show _ ⊢ wp_update_def E Q
  unfold wp_update_def
  iintro ⟨HP, HQ⟩ %e %Φ Hwp
  imod HP
  imod HQ $$ HP with HQ
  iapply Hwp $$ HQ

/-- Rocq: `wp_update_mono_fupd`. -/
theorem wp_update_mono_fupd (E : CoPset) (P Q : IProp GF) :
    wp_update E P ∗ (P ={E}=∗ Q) ⊢ wp_update E Q := by
  show _ ⊢ wp_update_def E Q
  unfold wp_update_def
  iintro ⟨HP, Hwand⟩ %e %Φ Hwp
  imod HP
  imod Hwand $$ HP with HQ
  iapply Hwp $$ HQ

/-- Rocq: `wp_update_mono`. -/
theorem wp_update_mono (E : CoPset) (P Q : IProp GF) :
    wp_update E P ∗ (P -∗ Q) ⊢ wp_update E Q := by
  iintro ⟨Hupd, HPQ⟩
  iapply wp_update_mono_fupd E P Q $$ [Hupd HPQ]
  iframe Hupd
  iintro HP
  imodintro
  iapply HPQ $$ HP

/-- Rocq: `fupd_wp_update`. -/
theorem fupd_wp_update (E : CoPset) (P : IProp GF) :
    (|={E}=> wp_update E P) ⊢ wp_update E P := by
  unfold wp_update wp_update_def
  iintro H %e %Φ Hwp
  imod H
  iapply H $$ Hwp

/-- Rocq: `fupd_wp_update_ret`. -/
theorem fupd_wp_update_ret (E : CoPset) (P : IProp GF) : (|={E}=> P) ⊢ wp_update E P := by
  iintro H
  iapply fupd_wp_update
  imod H
  imodintro
  iapply wp_update_ret $$ H

/-- Rocq: `wp_update_frame_l`. -/
theorem wp_update_frame_l (R : IProp GF) (E : CoPset) (P : IProp GF) :
    R ∗ wp_update E P ⊢ wp_update E iprop(P ∗ R) := by
  iintro ⟨HR, H⟩
  iapply wp_update_mono $$ [HR H]
  iframe H
  iintro HP
  iframe

/-- Rocq: `wp_update_unfold` (an equation; Rocq: `⊣⊢`). -/
theorem wp_update_unfold (E : CoPset) (P : IProp GF) :
    wp_update E P =
      iprop(∀ (e : expr) (Φ : val → IProp GF),
        (P -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}) :=
  rfl

/-- Rocq: `wp_update_state_step_coupl`. -/
theorem wp_update_state_step_coupl (P : IProp GF) (E : CoPset) :
    ⊢ (∀ (σ1 : state) (ε1 : ℝ≥0∞), state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
        state_step_coupl σ1 ε1 fun σ2 ε2 => iprop(
          |={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ P)) -∗
      wp_update E P := by
  unfold wp_update wp_update_def
  iintro H %e %Φ H'
  iapply state_step_coupl_pgl_wp
  iintro %σ1 %ε1 Hσε
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_bind $$ [H'] H
  iintro %σ2 %ε2 H
  iapply state_step_coupl_ret
  imod H with ⟨Hσ, Hε, HP⟩
  imodintro
  iframe Hσ Hε
  iapply H' $$ HP

/-- Rocq: `wp_update_epsilon_err`. -/
theorem wp_update_epsilon_err (E : CoPset) :
    ⊢ wp_update E iprop(∃ ε, ⌜0 < ε⌝ ∗ ↯ ε : IProp GF) := by
  iapply wp_update_state_step_coupl
  iintro %σ %ε ⟨Hstate, Herr⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply state_step_coupl_ampl'
  iintro %ε' %⟨Hlt, Hlt1⟩
  iapply state_step_coupl_ret
  have hle : ε ≤ ε' := Hlt.le
  have hsum : ε + (ε' - ε) < 1 := by rwa [add_tsub_cancel_of_le hle]
  imod ErrorCredit.supply_increase hsum $$ Herr with ⟨Herr, Hec⟩
  imod Hclose
  imodintro
  iframe Hstate
  isplitl [Herr]
  · iapply ErrorCredit.extAuth (add_tsub_cancel_of_le hle) $$ Herr
  · iexists ε' - ε
    iframe Hec
    ipureintro
    exact tsub_pos_of_lt Hlt

/-- Rocq: `from_modal_wp_update_wp_update`. -/
instance from_modal_wp_update_wp_update {io : InOut} {P : IProp GF} {E : CoPset} :
    FromModal io modality_id True (wp_update E P) (wp_update E P) P where
  from_modal _ := wp_update_ret E P

/-- Rocq: `elim_modal_wp_update_wp_update`. -/
instance elim_modal_wp_update_wp_update {b : Bool} {io : InOut} {P Q : IProp GF}
    {E : CoPset} :
    ElimModal True b io false (wp_update E P) P (wp_update E Q) (wp_update E Q) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans (wp_update_bind E P Q)

/-- Rocq: `frame_wp_update`. -/
instance frame_wp_update {p : Bool} {E : CoPset} {R P Q : IProp GF} [HR : Frame p R P Q] :
    Frame p R (wp_update E P) (wp_update E Q) where
  frame := by
    refine (wp_update_frame_l _ E Q).trans ?_
    iintro H
    iapply wp_update_mono $$ [H]
    iframe H
    iintro ⟨HQ, HR'⟩
    iapply HR.frame $$ [HQ HR']
    iframe

/-- Rocq: `from_pure_bupd`. -/
instance from_pure_bupd {b : Bool} {io : InOut} {E : CoPset} {P : IProp GF} {φ : Prop}
    [HP : FromPure b P io φ] : FromPure b (wp_update E P) io φ where
  from_pure := HP.from_pure.trans (wp_update_ret E P)

/-- Rocq: `into_wand_wp_update`. -/
instance into_wand_wp_update {p q : Bool} {m : WandMode} {E : CoPset} {R P Q : IProp GF}
    [HR : IntoWand false false R m P Q] :
    IntoWand p q (wp_update E R) m (wp_update E P) (wp_update E Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    refine (sep_mono_right intuitionisticallyIf_elim).trans ?_
    iintro ⟨HR', HP⟩
    imod HR'
    imod HP
    imodintro
    iapply HR.into_wand $$ HR' HP

/-- Rocq: `into_wand_bupd_persistent`. -/
instance into_wand_bupd_persistent {p q : Bool} {m : WandMode} {E : CoPset}
    {R P Q : IProp GF} [HR : IntoWand false q R m P Q] :
    IntoWand p q (wp_update E R) m P (wp_update E Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    iintro ⟨HR', HP⟩
    imod HR'
    imodintro
    iapply HR.into_wand $$ HR' HP

-- The mask `E` is not determined by the argument and result slots (as for iris-lean's
-- `intoWand_fupd_args`).
set_option synthInstance.checkSynthOrder false in
/-- Rocq: `into_wand_bupd_args`. -/
instance (priority := low) into_wand_bupd_args {p q : Bool} {s : WandMode.Side} {E : CoPset}
    {R P Q : IProp GF} [HR : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) (wp_update E P) (wp_update E Q) where
  into_wand := by
    refine wand_intro ?_
    refine (sep_mono HR.into_wand intuitionisticallyIf_elim).trans ?_
    iintro ⟨Hw, HP⟩
    iapply wp_update_mono $$ [Hw HP]
    iframe

/-- Rocq: `from_sep_bupd`. -/
instance from_sep_bupd {E : CoPset} {P Q1 Q2 : IProp GF} [HP : FromSep P Q1 Q2] :
    FromSep (wp_update E P) (wp_update E Q1) (wp_update E Q2) where
  from_sep := by
    iintro ⟨HQ1, HQ2⟩
    imod HQ1
    imod HQ2
    imodintro
    iapply HP.from_sep
    iframe

/-- Rocq: `is_except_0_wp_update`. -/
instance is_except_0_wp_update {E : CoPset} {Q : IProp GF} : IsExcept0 (wp_update E Q) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans (fupd_wp_update E Q))

/-- Rocq: `elim_modal_fupd_wp`. -/
instance elim_modal_fupd_wp {p : Bool} {io : InOut} {E : CoPset} {P Q : IProp GF} :
    ElimModal True p io false iprop(|={E}=> P) P (wp_update E Q) (wp_update E Q) where
  elim_modal _ := by
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    iintro ⟨Hu, Hw⟩
    iapply fupd_wp_update
    imod Hu
    imodintro
    iapply Hw $$ Hu

/-- Rocq: `from_exist_wp_update`. -/
instance from_exist_wp_update {B : Type _} {P : IProp GF} {E : CoPset} {Φ : B → IProp GF}
    [HP : FromExists P Φ] : FromExists (wp_update E P) (fun b => wp_update E (Φ b)) where
  from_exists := by
    iintro ⟨%x, Hx⟩
    imod Hx
    imodintro
    iapply HP.from_exists
    iexists x
    iexact Hx

/-- Rocq: `into_forall_wp_update`. -/
instance into_forall_wp_update {B : Type _} {P : IProp GF} {E : CoPset} {Φ : B → IProp GF}
    [HP : IntoForall P Φ] : IntoForall (wp_update E P) (fun b => wp_update E (Φ b)) where
  into_forall := by
    iintro H %b
    imod H
    imodintro
    iapply HP.into_forall $$ H

/-- Rocq: `from_assumption_wp_update` (Rocq: a `KnownRFromAssumption` instance). -/
instance from_assumption_wp_update {p : Bool} {io : InOut} {E : CoPset} {P Q : IProp GF}
    [HP : FromAssumption p io P Q] : FromAssumption p io P (wp_update E Q) where
  from_assumption := HP.from_assumption.trans (wp_update_ret E Q)

end wp_update

/-! ## The `state_update` modality -/

section state_update

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `state_update_def`. -/
def state_update_def (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ (σ1 : state) (ε1 : ℝ≥0∞), state_interp σ1 ∗ err_interp ε1 ={E1, ∅}=∗
    state_step_coupl σ1 ε1 fun σ2 ε2 => iprop(
      |={∅, E2}=> state_interp σ2 ∗ err_interp ε2 ∗ P))

/-- Rocq: `state_update`. -/
def state_update (E1 E2 : CoPset) (P : IProp GF) : IProp GF := state_update_def E1 E2 P

/-- Rocq: `state_update_unseal`. -/
theorem state_update_unseal : @state_update GF _ = @state_update_def GF _ := rfl

/-- Rocq: `wp_update_state_update`. -/
theorem wp_update_state_update (E : CoPset) (P : IProp GF) :
    ⊢ state_update E E P -∗ wp_update E P := by
  unfold state_update state_update_def
  iintro H
  iapply wp_update_state_step_coupl $$ H

/-- Rocq: `state_update_ret`. -/
theorem state_update_ret (E : CoPset) (P : IProp GF) : ⊢ P -∗ state_update E E P := by
  unfold state_update state_update_def
  iintro HP %σ1 %ε1 ⟨Hσ, Hε⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply state_step_coupl_ret
  imod Hclose
  imodintro
  iframe

/-- Rocq: `from_modal_state_update_state_update`. -/
instance from_modal_state_update_state_update {io : InOut} {P : IProp GF} {E : CoPset} :
    FromModal io modality_id True (state_update E E P) (state_update E E P) P where
  from_modal _ := wand_entails (state_update_ret E P)

/-- Rocq: `state_update_mono_fupd`. -/
theorem state_update_mono_fupd (E1 E2 E3 : CoPset) (P : IProp GF) (_Hsubseteq : E1 ⊆ E2) :
    ⊢ (|={E2, E1}=> state_update E1 E3 P) -∗ state_update E2 E3 P := by
  unfold state_update state_update_def
  iintro Hvs %σ1 %ε1 Hσε
  imod Hvs
  imod Hvs $$ %σ1 %ε1 Hσε with H
  imodintro
  iexact H

/-- Rocq: `state_update_mono`. -/
theorem state_update_mono (E1 E2 : CoPset) (P Q : IProp GF) :
    ⊢ (P ={E2}=∗ Q) -∗ state_update E1 E2 P -∗ state_update E1 E2 Q := by
  unfold state_update state_update_def
  iintro Hvs H %σ1 %ε1 Hσε
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_mono $$ [Hvs] H
  iintro %σ2 %ε2 >⟨Hσ, Hε, HP⟩
  iframe Hσ Hε
  iapply Hvs $$ HP

/-- Rocq: `state_update_mono_fupd'`. -/
theorem state_update_mono_fupd' (E1 E2 : CoPset) (P : IProp GF) (h : E1 ⊆ E2) :
    ⊢ state_update E1 E1 P -∗ state_update E2 E2 P := by
  iintro H
  iapply state_update_mono_fupd E1 E2 E2 P h
  iapply fupd_mask_intro h
  iintro Hclose
  unfold state_update state_update_def
  iintro %σ1 %ε1 Hσε
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_bind $$ [Hclose] H
  iintro %σ2 %ε2 H
  iapply state_step_coupl_ret
  imod H with ⟨Hσ, Hε, HP⟩
  imod Hclose
  imodintro
  iframe

/-- Rocq: `state_update_fupd`. -/
theorem state_update_fupd (E1 E2 : CoPset) (P : IProp GF) :
    ⊢ (|={E1}=> state_update E1 E2 P) -∗ state_update E1 E2 P := by
  iintro H
  iapply state_update_mono_fupd E1 E1 E2 P LawfulSet.subset_refl
  imod H
  imodintro
  iexact H

/-- Rocq: `state_update_epsilon_err`. -/
theorem state_update_epsilon_err (E : CoPset) :
    ⊢ state_update E E iprop(∃ ε, ⌜0 < ε⌝ ∗ ↯ ε : IProp GF) := by
  unfold state_update state_update_def
  iintro %σ %ε ⟨Hstate, Herr⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply state_step_coupl_ampl'
  iintro %ε' %⟨Hlt, Hlt1⟩
  iapply state_step_coupl_ret
  have hle : ε ≤ ε' := Hlt.le
  have hsum : ε + (ε' - ε) < 1 := by rwa [add_tsub_cancel_of_le hle]
  imod ErrorCredit.supply_increase hsum $$ Herr with ⟨Herr, Hec⟩
  imod Hclose
  imodintro
  iframe Hstate
  isplitl [Herr]
  · iapply ErrorCredit.extAuth (add_tsub_cancel_of_le hle) $$ Herr
  · iexists ε' - ε
    iframe Hec
    ipureintro
    exact tsub_pos_of_lt Hlt

/-- Rocq: `state_update_fupd_change`. -/
theorem state_update_fupd_change (E1 E2 E3 : CoPset) (P Q : IProp GF) :
    ⊢ (|={E1, E2}=> P) -∗ (P -∗ state_update E2 E3 Q) -∗ state_update E1 E3 Q := by
  unfold state_update state_update_def
  iintro H1 H2 %σ1 %ε1 Hσε
  imod H1
  imod H2 $$ H1 %σ1 %ε1 Hσε with H2
  imodintro
  iexact H2

/-- Rocq: `elim_modal_bupd_state_update`. -/
instance elim_modal_bupd_state_update {p : Bool} {io : InOut} {E1 E2 : CoPset}
    {P Q : IProp GF} :
    ElimModal True p io false iprop(|==> P) P (state_update E1 E2 Q) (state_update E1 E2 Q)
    where
  elim_modal _ := by
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    iintro ⟨H1, H2⟩
    iapply state_update_fupd
    imod H1
    imodintro
    iapply H2 $$ H1

/-- Rocq: `elim_modal_fupd_state_update`. -/
instance elim_modal_fupd_state_update {p : Bool} {io : InOut} {E1 E2 E3 : CoPset}
    {P Q : IProp GF} :
    ElimModal True p io false iprop(|={E1, E2}=> P) P (state_update E1 E3 Q)
      (state_update E2 E3 Q) where
  elim_modal _ := by
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    iintro ⟨H1, H2⟩
    iapply state_update_fupd_change $$ H1 H2

/-- Rocq: `state_update_mask_intro`. -/
theorem state_update_mask_intro (E1 E2 : CoPset) (P : IProp GF) (h : E2 ⊆ E1) :
    ⊢ (state_update E2 E1 emp -∗ P) -∗ state_update E1 E2 P := by
  iintro H
  iapply state_update_mono_fupd E2 E1 E2 P h
  iapply fupd_mask_intro h
  iintro K
  imodintro
  iapply H
  imod K
  imodintro
  iempintro

/-- Rocq: `state_update_bind`. -/
theorem state_update_bind (E1 E2 E3 : CoPset) (P Q : IProp GF) :
    state_update E1 E2 P ∗ (P -∗ state_update E2 E3 Q) ⊢ state_update E1 E3 Q := by
  unfold state_update state_update_def
  iintro ⟨H1, H2⟩ %σ1 %ε1 Hσε
  imod H1 $$ %σ1 %ε1 Hσε with H1
  imodintro
  iapply state_step_coupl_bind $$ [H2] H1
  iintro %σ2 %ε2 H1
  iapply fupd_state_step_coupl
  imod H1 with ⟨Hσ, Hε, HP⟩
  iapply H2 $$ HP %σ2 %ε2 [Hσ Hε]
  iframe

/-- Rocq: `elim_modal_state_update_state_update`. -/
instance elim_modal_state_update_state_update {p : Bool} {io : InOut} {E1 E2 E3 : CoPset}
    {P Q : IProp GF} :
    ElimModal True p io false (state_update E1 E2 Q) Q (state_update E1 E3 P)
      (state_update E2 E3 P) where
  elim_modal _ :=
    (sep_mono_left intuitionisticallyIf_elim).trans (state_update_bind E1 E2 E3 Q P)

/-- Rocq: `elim_modal_state_update_wp_update`. -/
instance elim_modal_state_update_wp_update {p : Bool} {io : InOut} {E1 E2 : CoPset}
    {P Q : IProp GF} :
    ElimModal (E1 ⊆ E2) p io false (state_update E1 E1 Q) Q (wp_update E2 P) (wp_update E2 P)
    where
  elim_modal h := by
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    iintro ⟨H1, H2⟩
    ihave H1 := state_update_mono_fupd' E1 E2 Q h $$ H1
    ihave H1 := wp_update_state_update E2 Q $$ H1
    imod H1
    iapply H2 $$ H1

/-- Rocq: `elim_modal_state_update_wp`. -/
instance elim_modal_state_update_wp {s : Stuckness} {e : expr} {Φ : val → IProp GF}
    {p : Bool} {io : InOut} {E1 E2 : CoPset} {P : IProp GF} :
    ElimModal (E1 ⊆ E2) p io false (state_update E1 E1 P) P (WP e @ s; E2 {{ Φ }})
      (WP e @ s; E2 {{ Φ }}) where
  elim_modal h := by
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    iintro ⟨H1, H2⟩
    ihave H1 := state_update_mono_fupd' E1 E2 P h $$ H1
    ihave H1 := wp_update_state_update E2 P $$ H1
    imod H1
    iapply H2 $$ H1

/-- Rocq: `state_update_wp`. -/
theorem state_update_wp (E : CoPset) (P : IProp GF) (e : expr) (Φ : val → IProp GF) :
    ⊢ state_update E E P -∗ (P -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }} := by
  iintro H1 H
  imod H1
  iapply H $$ H1

/-- Rocq: `is_except_0_state_update`. -/
instance is_except_0_state_update {E1 E2 : CoPset} {Q : IProp GF} :
    IsExcept0 (state_update E1 E2 Q) where
  is_except0 := (except0_mono fupd_intro).trans
    (BIFUpdate.except0.trans (wand_entails (state_update_fupd E1 E2 Q)))

/-- Rocq: `state_update_frame_l`. -/
theorem state_update_frame_l (R : IProp GF) (E1 E2 : CoPset) (P : IProp GF) :
    R ∗ state_update E1 E2 P ⊢ state_update E1 E2 iprop(P ∗ R) := by
  iintro ⟨HR, H⟩
  imod H
  imodintro
  iframe

/-- Rocq: `frame_state_update`. -/
instance frame_state_update {p : Bool} {E : CoPset} {R P Q : IProp GF} [HR : Frame p R P Q] :
    Frame p R (state_update E E P) (state_update E E Q) where
  frame := by
    refine (state_update_frame_l _ E E Q).trans ?_
    iintro >⟨HQ, HR'⟩
    imodintro
    iapply HR.frame $$ [HQ HR']
    iframe

/-- Rocq: `from_pure_bupd_state_update`. -/
instance from_pure_bupd_state_update {b : Bool} {io : InOut} {E : CoPset} {P : IProp GF}
    {φ : Prop} [HP : FromPure b P io φ] : FromPure b (state_update E E P) io φ where
  from_pure := HP.from_pure.trans (wand_entails (state_update_ret E P))

/-- Rocq: `into_wand_state_update`. -/
instance into_wand_state_update {p q : Bool} {m : WandMode} {E : CoPset} {R P Q : IProp GF}
    [HR : IntoWand false false R m P Q] :
    IntoWand p q (state_update E E R) m (state_update E E P) (state_update E E Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    refine (sep_mono_right intuitionisticallyIf_elim).trans ?_
    iintro ⟨HR', HP⟩
    imod HR'
    imod HP
    imodintro
    iapply HR.into_wand $$ HR' HP

/-- Rocq: `into_wand_bupd_persistent_state_update`. -/
instance into_wand_bupd_persistent_state_update {p q : Bool} {m : WandMode} {E : CoPset}
    {R P Q : IProp GF} [HR : IntoWand false q R m P Q] :
    IntoWand p q (state_update E E R) m P (state_update E E Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    iintro ⟨HR', HP⟩
    imod HR'
    imodintro
    iapply HR.into_wand $$ HR' HP

-- The mask `E` is not determined by the argument and result slots (as for iris-lean's
-- `intoWand_fupd_args`).
set_option synthInstance.checkSynthOrder false in
/-- Rocq: `into_wand_bupd_args_state_update`. -/
instance (priority := low) into_wand_bupd_args_state_update {p q : Bool} {s : WandMode.Side}
    {E : CoPset} {R P Q : IProp GF} [HR : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) (state_update E E P) (state_update E E Q) where
  into_wand := by
    refine wand_intro ?_
    refine (sep_mono HR.into_wand intuitionisticallyIf_elim).trans ?_
    iintro ⟨Hw, HP⟩
    imod HP
    imodintro
    iapply Hw $$ HP

/-- Rocq: `from_sep_bupd_state_update`. -/
instance from_sep_bupd_state_update {E : CoPset} {P Q1 Q2 : IProp GF} [HP : FromSep P Q1 Q2] :
    FromSep (state_update E E P) (state_update E E Q1) (state_update E E Q2) where
  from_sep := by
    iintro ⟨HQ1, HQ2⟩
    imod HQ1
    imod HQ2
    imodintro
    iapply HP.from_sep
    iframe

/-- Rocq: `from_exist_state_update`. -/
instance from_exist_state_update {B : Type _} {P : IProp GF} {E : CoPset} {Φ : B → IProp GF}
    [HP : FromExists P Φ] :
    FromExists (state_update E E P) (fun b => state_update E E (Φ b)) where
  from_exists := by
    iintro ⟨%x, Hx⟩
    imod Hx
    imodintro
    iapply HP.from_exists
    iexists x
    iexact Hx

/-- Rocq: `into_forall_state_update`. -/
instance into_forall_state_update {B : Type _} {P : IProp GF} {E : CoPset} {Φ : B → IProp GF}
    [HP : IntoForall P Φ] :
    IntoForall (state_update E E P) (fun b => state_update E E (Φ b)) where
  into_forall := by
    iintro H %b
    imod H
    imodintro
    iapply HP.into_forall $$ H

/-- Rocq: `from_assumption_state_update` (Rocq: a `KnownRFromAssumption` instance). -/
instance from_assumption_state_update {p : Bool} {io : InOut} {E : CoPset} {P Q : IProp GF}
    [HP : FromAssumption p io P Q] : FromAssumption p io P (state_update E E Q) where
  from_assumption := HP.from_assumption.trans (wand_entails (state_update_ret E Q))

/-- Rocq: `pgl_wp_state_update`. -/
theorem pgl_wp_state_update (Φ : val → IProp GF) (E : CoPset) (e : expr) :
    WP e @ E {{ x, state_update E E (Φ x) }} ⊢ WP e @ E {{ Φ }} := by
  iintro H
  iapply pgl_wp_strong_mono LawfulSet.subset_refl $$ H
  unfold state_update state_update_def
  iintro %σ1 %ε1 %v ⟨Hσ, Hε, H⟩
  iapply H $$ %σ1 %ε1 [Hσ Hε]
  iframe

/-- Rocq: `state_update_pgl_wp`. -/
theorem state_update_pgl_wp (Φ : val → IProp GF) (E : CoPset) (e : expr) :
    state_update E E (WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }} := by
  iintro >H
  iexact H

/-! State updates work for the allocation of invariants and ghost resources. -/

/-- Rocq: `state_update_inv_alloc`. -/
theorem state_update_inv_alloc (E : CoPset) (P : IProp GF) (N : Namespace) :
    ⊢ ▷ P -∗ state_update E E (inv N P) := by
  iintro HP
  imod inv_alloc N E P $$ HP with H
  imodintro
  iexact H

/-- Rocq: `state_update_inv_acc`. -/
theorem state_update_inv_acc (P : IProp GF) (E : CoPset) (I : IProp GF) (N : Namespace)
    (Hsubset : ↑N ⊆ E) :
    ⊢ inv N I -∗ (▷ I -∗ state_update (E \ ↑N) (E \ ↑N) iprop(P ∗ ▷ I)) -∗
      state_update E E P := by
  iintro #Hinv H
  imod inv_acc Hsubset $$ Hinv with ⟨HI, Hclose⟩
  imod H $$ HI with ⟨HP, HI⟩
  imod Hclose $$ HI with -
  imodintro
  iexact HP

/-- Rocq: `state_update_inv_acc'`. -/
theorem state_update_inv_acc' (E : CoPset) (I : IProp GF) (N : Namespace)
    (Hsubset : ↑N ⊆ E) :
    ⊢ inv N I -∗
      state_update E (E \ ↑N)
        iprop(▷ I ∗ (▷ I -∗ state_update (E \ ↑N) E iprop(True))) := by
  iintro #Hinv
  imod inv_acc Hsubset $$ Hinv with ⟨HI, Hvs⟩
  imodintro
  iframe HI
  iintro HI
  imod Hvs $$ HI with -
  imodintro
  ipureintro
  trivial

/-- Rocq: `state_update_ra_alloc`. -/
theorem state_update_ra_alloc {F : COFE.OFunctorPre} [RFunctorContractive F] [ElemG GF F]
    (E : CoPset) (a : F.ap (IProp GF)) (H : ✓ a) :
    ⊢ state_update E E iprop(∃ γ, iOwn γ a) := by
  imod iOwn_alloc a H with H
  imodintro
  iexact H

end state_update

/-! ## An alternative WP pre-functor -/

section alt_wp

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `pgl_wp_pre'`. -/
def pgl_wp_pre' (wp : CoPset → expr → (val → IProp GF) → IProp GF) :
    CoPset → expr → (val → IProp GF) → IProp GF := fun E e1 Φ =>
  state_update E ∅ iprop(
    ∀ (σ2 : state) (ε2 : ℝ≥0∞), state_interp σ2 ∗ err_interp ε2 -∗
      match to_val e1 with
      | some v => iprop(|={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ Φ v)
      | none => prog_coupl e1 σ2 ε2 fun e3 σ3 efs ε3 => iprop(
          (▷ state_interp σ3) ∗ err_interp ε3 ∗
            state_update ∅ E iprop(wp E e3 Φ ∗
              [∗list] ef ∈ efs, wp ⊤ ef (fork_post (Λ := con_prob_lang)))))

/-- Rocq: `pgl_wp_pre'_implies_pgl_wp_pre`. -/
theorem pgl_wp_pre'_implies_pgl_wp_pre (wp : CoPset → expr → (val → IProp GF) → IProp GF)
    (E : CoPset) (e : expr) (Φ : val → IProp GF) :
    ⊢ pgl_wp_pre' wp E e Φ -∗ pgl_wp_pre wp E e Φ := by
  unfold pgl_wp_pre' state_update state_update_def
  iintro H %σ1 %ε1 Hσε
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_bind $$ [] H
  iintro %σ2 %ε2 H
  iapply fupd_state_step_coupl
  imod H with ⟨Hσ, Hε, H⟩
  imodintro
  iapply state_step_coupl_ret
  ispecialize H $$ %σ2 %ε2 [Hσ Hε]
  · iframe
  cases hv : to_val e with
  | some v => iexact H
  | none =>
    iapply prog_coupl_mono $$ [] H
    iintro %e3 %σ3 %efs %ε3 ⟨Hσ, Hε, H⟩
    iintro !>
    iapply fupd_state_step_coupl
    iapply H $$ %σ3 %ε3 [Hσ Hε]
    iframe

end alt_wp

/- Sanity checks for the proof-mode instances. -/
section examples

variable {GF : BundledGFunctors} [conerisGS GF]

example {s : Stuckness} {E : CoPset} {e : expr} {Φ : val → IProp GF} (P : IProp GF) :
    wp_update E P ∗ (P -∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example {s : Stuckness} {E : CoPset} {e : expr} {Φ : val → IProp GF} (P : IProp GF) :
    state_update E E P ∗ (P -∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example {E : CoPset} (P Q : IProp GF) : P ∗ wp_update E Q ⊢ wp_update E iprop(P ∗ Q) := by
  iintro ⟨HP, HQ⟩
  imod HQ
  iframe HP
  imodintro
  iexact HQ

example {E : CoPset} (P Q : IProp GF) :
    P ∗ state_update E E Q ⊢ state_update E E iprop(Q ∗ P) := by
  iintro ⟨HP, HQ⟩
  iframe HP
  iexact HQ

example {E : CoPset} (P : IProp GF) : (|={E}=> P) ⊢ state_update E E P := by
  iintro >HP
  iexact HP

end examples

end Coneris
