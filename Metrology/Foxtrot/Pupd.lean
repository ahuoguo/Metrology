module

public import Metrology.Foxtrot.Weakestpre
public import Iris.Instances.Lib.Invariants

/-!
# The `pupd` (probabilistic update) modality of Foxtrot

Ported from clutch/theories/foxtrot/pupd.v

`pupd E1 E2 P` holds if, for all current LHS state `σ1`, RHS configuration `ρ1` and error
`ε1`, one can (after opening the masks `E1` to `∅`) perform a `spec_coupl` (LHS state steps /
RHS scheduler steps with error-credit accounting) and end, closing the mask to `E2`, with the
new interpretations and `P`. It is the Foxtrot analogue of Coneris's `state_update`
(see `Metrology/Coneris/WpUpdate.lean`, which this file follows).

## Rocq → Lean map
All Rocq names are kept: `pupd_def`, `pupd`, `pupd_unseal`, `pupd_ne`, `pupd_ret`,
`from_modal_pupd_pupd`, `pupd_mono_fupd`, `pupd_mono`, `pupd_mono_fupd'`, `pupd_fupd`,
`pupd_fupd_change`, `elim_modal_bupd_pupd`, `elim_modal_fupd_pupd`, `pupd_mask_intro`,
`pupd_fupd'`, `pupd_bind`, `elim_modal_pupd_pupd`, `elim_modal_pupd_wp`, `elim_modal_pupd_wp'`,
`is_except_0_pupd`, `pupd_frame_l`, `frame_pupd`, `from_pure_bupd_pupd`, `into_wand_pupd`,
`into_wand_bupd_persistent_pupd`, `into_wand_bupd_args_pupd`, `from_sep_bupd_pupd`,
`from_exist_pupd`, `into_forall_pupd`, `from_assumption_pupd`, `wp_pupd`, `pupd_wp`,
`pupd_inv_alloc`, `pupd_inv_acc`, `pupd_inv_acc'`, `pupd_ra_alloc`.

## Design choices / deviations (Rocq → Lean)
* Sealing (`seal`/`unseal`) is mimicked by a pair of `def`s: `pupd_def` and
  `pupd := pupd_def`, with the `rfl` equation `pupd_unseal` (as in `Coneris.WpUpdate`). Being
  `def`s, they are opaque to instance search, as the sealed Rocq definition. Downstream
  (Rocq: `rewrite pupd_unseal/pupd_def`) use `rw [pupd_unseal]; unfold pupd_def` or
  `unfold pupd pupd_def`.
* RHS configurations are `CPState` (local notation for `(con_lang_mdp con_prob_lang).mdpstate`),
  errors are `ℝ≥0∞`.
* `pupd_ne` (Rocq: a `Proper ((=) ==> (=) ==> dist n ==> dist n)` instance) is the
  `NonExpansive (pupd E1 E2)` instance.
* Statement shapes: Rocq's `P -∗ Q` lemmas are stated as `P ⊢ Q` and `X -∗ Y -∗ Z` as
  `X ⊢ Y -∗ Z` (as in `Foxtrot.Weakestpre`); `✓ a → ⊢ ..` is kept.
* Proof-mode instances follow iris-lean's `ProofMode/InstancesUpdates.lean` (as in
  `Coneris.WpUpdate`): `ElimModal` carries the `InOut` parameter, `IntoWand` the `WandMode`
  parameter, `FromPure` the `InOut` parameter, `FromExist` is `FromExists`, and Rocq's
  `KnownRFromAssumption` is iris-lean's `FromAssumption` (with the `InOut` parameter).
  `into_wand_bupd_args_pupd` is restricted to the `.matching s` modes and gets
  `priority := low`, like iris-lean's `intoWand_bupd_args`.
* The instances whose goal is a WP (`elim_modal_pupd_wp`, `elim_modal_pupd_wp'`) are stated for
  an arbitrary stuckness `s` (the Foxtrot WP ignores it, `wp_stuckness_irrel`).
  `elim_modal_pupd_wp'` (no side condition) gets `priority := default + 10`, as it is declared
  later in Rocq (and so tried first there).
* `pupd_ra_alloc` is stated for an iris-lean `ElemG GF F` and `a : F.ap (IProp GF)`
  (Rocq: `inG Σ A`, `a : A`), like iris-lean's `iOwn_alloc`.
* The proofs of `pupd_mono_fupd` and `pupd_fupd_change` do not need Rocq's detour through
  `spec_coupl_mono` (the continuation is passed through unchanged).

## Omitted
* `pupd_aux` (the seal, see above).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

section pupd

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]

/-- Rocq: `pupd_def`. -/
def pupd_def (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞),
    state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E1, ∅}=∗
    spec_coupl σ1 ρ1 ε1 fun σ2 ρ2 ε2 => iprop(
      |={∅, E2}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ P))

/-- Rocq: `pupd`. -/
def pupd (E1 E2 : CoPset) (P : IProp GF) : IProp GF := pupd_def E1 E2 P

/-- Rocq: `pupd_unseal`. -/
theorem pupd_unseal : @pupd GF _ = @pupd_def GF _ := rfl

/-- Rocq: `pupd_ne`. -/
instance pupd_ne (E1 E2 : CoPset) : NonExpansive (pupd (GF := GF) E1 E2) where
  ne {_ _ _} h := by
    unfold pupd pupd_def
    refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
    refine wand_ne.ne .rfl (BIFUpdate.ne.ne ?_)
    refine spec_coupl_ne fun _ _ _ => ?_
    exact BIFUpdate.ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl h

/-- Rocq: `pupd_ret`. -/
theorem pupd_ret (E : CoPset) (P : IProp GF) : P ⊢ pupd E E P := by
  unfold pupd pupd_def
  iintro HP %σ1 %ρ1 %ε1 ⟨Hσ, Hρ, Hε⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_ret
  imod Hclose
  imodintro
  iframe

/-- Rocq: `from_modal_pupd_pupd`. -/
instance from_modal_pupd_pupd {io : InOut} {P : IProp GF} {E : CoPset} :
    FromModal io modality_id True (pupd E E P) (pupd E E P) P where
  from_modal _ := pupd_ret E P

/-- Rocq: `pupd_mono_fupd`. -/
theorem pupd_mono_fupd (E1 E2 E3 : CoPset) (P : IProp GF) (_Hsubseteq : E1 ⊆ E2) :
    (|={E2, E1}=> pupd E1 E3 P) ⊢ pupd E2 E3 P := by
  unfold pupd pupd_def
  iintro Hvs %σ1 %ρ1 %ε1 Hs
  imod Hvs
  imod Hvs $$ %σ1 %ρ1 %ε1 Hs with H
  imodintro
  iexact H

/-- Rocq: `pupd_mono`. -/
theorem pupd_mono (E1 E2 : CoPset) (P Q : IProp GF) :
    (P ={E2}=∗ Q) ⊢ pupd E1 E2 P -∗ pupd E1 E2 Q := by
  unfold pupd pupd_def
  iintro Hvs H %σ1 %ρ1 %ε1 Hs
  imod H $$ %σ1 %ρ1 %ε1 Hs with H
  imodintro
  iapply spec_coupl_mono $$ [Hvs] H
  iintro %σ2 %ρ2 %ε2 >⟨Hσ, Hρ, Hε, HP⟩
  iframe Hσ Hρ Hε
  iapply Hvs $$ HP

/-- Rocq: `pupd_mono_fupd'`. -/
theorem pupd_mono_fupd' (E1 E2 : CoPset) (P : IProp GF) (h : E1 ⊆ E2) :
    pupd E1 E1 P ⊢ pupd E2 E2 P := by
  iintro H
  iapply pupd_mono_fupd E1 E2 E2 P h
  iapply fupd_mask_intro h
  iintro Hclose
  unfold pupd pupd_def
  iintro %σ1 %ρ1 %ε1 Hs
  imod H $$ %σ1 %ρ1 %ε1 Hs with H
  imodintro
  iapply spec_coupl_bind $$ [Hclose] H
  iintro %σ2 %ρ2 %ε2 H
  iapply spec_coupl_ret
  imod H with ⟨Hσ, Hρ, Hε, HP⟩
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_fupd`. -/
theorem pupd_fupd (E1 E2 : CoPset) (P : IProp GF) :
    (|={E1}=> pupd E1 E2 P) ⊢ pupd E1 E2 P := by
  iintro H
  iapply pupd_mono_fupd E1 E1 E2 P LawfulSet.subset_refl
  imod H
  imodintro
  iexact H

/-- Rocq: `pupd_fupd_change`. -/
theorem pupd_fupd_change (E1 E2 E3 : CoPset) (P Q : IProp GF) :
    (|={E1, E2}=> P) ⊢ (P -∗ pupd E2 E3 Q) -∗ pupd E1 E3 Q := by
  unfold pupd pupd_def
  iintro H1 H2 %σ1 %ρ1 %ε1 Hs
  imod H1
  imod H2 $$ H1 %σ1 %ρ1 %ε1 Hs with H2
  imodintro
  iexact H2

/-- Rocq: `elim_modal_bupd_pupd`. -/
instance elim_modal_bupd_pupd {p : Bool} {io : InOut} {E1 E2 : CoPset} {P Q : IProp GF} :
    ElimModal True p io false iprop(|==> P) P (pupd E1 E2 Q) (pupd E1 E2 Q) where
  elim_modal _ := by
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    iintro ⟨H1, H2⟩
    iapply pupd_fupd
    imod H1
    imodintro
    iapply H2 $$ H1

/-- Rocq: `elim_modal_fupd_pupd`. -/
instance elim_modal_fupd_pupd {p : Bool} {io : InOut} {E1 E2 E3 : CoPset} {P Q : IProp GF} :
    ElimModal True p io false iprop(|={E1, E2}=> P) P (pupd E1 E3 Q) (pupd E2 E3 Q) where
  elim_modal _ := by
    refine (sep_mono_left intuitionisticallyIf_elim).trans ?_
    iintro ⟨H1, H2⟩
    iapply pupd_fupd_change $$ H1 H2

/-- Rocq: `pupd_mask_intro`. -/
theorem pupd_mask_intro (E1 E2 : CoPset) (P : IProp GF) (h : E2 ⊆ E1) :
    (pupd E2 E1 emp -∗ P) ⊢ pupd E1 E2 P := by
  iintro H
  iapply pupd_mono_fupd E2 E1 E2 P h
  iapply fupd_mask_intro h
  iintro K
  imodintro
  iapply H
  imod K
  imodintro
  iempintro

/-- Rocq: `pupd_fupd'`. -/
theorem pupd_fupd' (E1 E2 : CoPset) (P : IProp GF) (h : E2 ⊆ E1) :
    pupd E1 E1 P ⊢ pupd E1 E2 iprop(|={E2, E1}=> P) := by
  unfold pupd pupd_def
  iintro H %σ1 %ρ1 %ε1 Hs
  imod H $$ %σ1 %ρ1 %ε1 Hs with H
  imodintro
  iapply spec_coupl_mono $$ [] H
  iintro %σ2 %ρ2 %ε2 >⟨Hσ, Hρ, Hε, HP⟩
  iapply fupd_mask_intro h
  iintro Hclose
  iframe Hσ Hρ Hε
  imod Hclose
  imodintro
  iexact HP

/-- Rocq: `pupd_bind`. -/
theorem pupd_bind (E1 E2 E3 : CoPset) (P Q : IProp GF) :
    pupd E1 E2 P ∗ (P -∗ pupd E2 E3 Q) ⊢ pupd E1 E3 Q := by
  unfold pupd pupd_def
  iintro ⟨H1, H2⟩ %σ1 %ρ1 %ε1 Hs
  imod H1 $$ %σ1 %ρ1 %ε1 Hs with H1
  imodintro
  iapply spec_coupl_bind $$ [H2] H1
  iintro %σ2 %ρ2 %ε2 H1
  iapply fupd_spec_coupl
  imod H1 with ⟨Hσ, Hρ, Hε, HP⟩
  iapply H2 $$ HP %σ2 %ρ2 %ε2 [Hσ Hρ Hε]
  iframe

/-- Rocq: `elim_modal_pupd_pupd`. -/
instance elim_modal_pupd_pupd {p : Bool} {io : InOut} {E1 E2 E3 : CoPset} {P Q : IProp GF} :
    ElimModal True p io false (pupd E1 E2 Q) Q (pupd E1 E3 P) (pupd E2 E3 P) where
  elim_modal _ :=
    (sep_mono_left intuitionisticallyIf_elim).trans (pupd_bind E1 E2 E3 Q P)

/-- Rocq: `elim_modal_pupd_wp`. -/
instance elim_modal_pupd_wp {s : Stuckness} {e : expr} {Φ : val → IProp GF}
    {p : Bool} {io : InOut} {E1 E2 : CoPset} {P : IProp GF} :
    ElimModal (E1 ⊆ E2) p io false (pupd E1 E1 P) P (WP e @ s; E2 {{ Φ }})
      (WP e @ s; E2 {{ Φ }}) where
  elim_modal h := by
    refine (sep_mono_left (intuitionisticallyIf_elim.trans (pupd_mono_fupd' E1 E2 P h))).trans
      ?_
    unfold pupd pupd_def
    iintro ⟨H1, H2⟩
    iapply spec_coupl_wp
    iintro %σ1 %ρ1 %ε1 Hs
    imod H1 $$ %σ1 %ρ1 %ε1 Hs with H1
    imodintro
    iapply spec_coupl_mono $$ [H2] H1
    iintro %σ2 %ρ2 %ε2 >⟨Hσ, Hρ, Hε, HP⟩
    imodintro
    iframe Hσ Hρ Hε
    iapply H2 $$ HP

/-- Rocq: `elim_modal_pupd_wp'`. -/
instance (priority := default + 10) elim_modal_pupd_wp' {s : Stuckness} {e : expr}
    {Φ : val → IProp GF} {p : Bool} {io : InOut} {E : CoPset} {P : IProp GF} :
    ElimModal True p io false (pupd E E P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}) where
  elim_modal _ :=
    (elim_modal_pupd_wp (s := s) (e := e) (Φ := Φ) (p := p) (io := io) (E1 := E) (E2 := E)
      (P := P)).elim_modal LawfulSet.subset_refl

/-- Rocq: `is_except_0_pupd`. -/
instance is_except_0_pupd {E1 E2 : CoPset} {Q : IProp GF} : IsExcept0 (pupd E1 E2 Q) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans (pupd_fupd E1 E2 Q))

/-- Rocq: `pupd_frame_l`. -/
theorem pupd_frame_l (R : IProp GF) (E1 E2 : CoPset) (P : IProp GF) :
    R ∗ pupd E1 E2 P ⊢ pupd E1 E2 iprop(P ∗ R) := by
  iintro ⟨HR, H⟩
  imod H
  imodintro
  iframe

/-- Rocq: `frame_pupd`. -/
instance frame_pupd {p : Bool} {E : CoPset} {R P Q : IProp GF} [HR : Frame p R P Q] :
    Frame p R (pupd E E P) (pupd E E Q) where
  frame := by
    refine (pupd_frame_l _ E E Q).trans ?_
    iintro >⟨HQ, HR'⟩
    imodintro
    iapply HR.frame $$ [HQ HR']
    iframe

/-- Rocq: `from_pure_bupd_pupd`. -/
instance from_pure_bupd_pupd {b : Bool} {io : InOut} {E : CoPset} {P : IProp GF}
    {φ : Prop} [HP : FromPure b P io φ] : FromPure b (pupd E E P) io φ where
  from_pure := HP.from_pure.trans (pupd_ret E P)

/-- Rocq: `into_wand_pupd`. -/
instance into_wand_pupd {p q : Bool} {m : WandMode} {E : CoPset} {R P Q : IProp GF}
    [HR : IntoWand false false R m P Q] :
    IntoWand p q (pupd E E R) m (pupd E E P) (pupd E E Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    refine (sep_mono_right intuitionisticallyIf_elim).trans ?_
    iintro ⟨HR', HP⟩
    imod HR'
    imod HP
    imodintro
    iapply HR.into_wand $$ HR' HP

/-- Rocq: `into_wand_bupd_persistent_pupd`. -/
instance into_wand_bupd_persistent_pupd {p q : Bool} {m : WandMode} {E : CoPset}
    {R P Q : IProp GF} [HR : IntoWand false q R m P Q] :
    IntoWand p q (pupd E E R) m P (pupd E E Q) where
  into_wand := by
    refine intuitionisticallyIf_elim.trans <| wand_intro ?_
    iintro ⟨HR', HP⟩
    imod HR'
    imodintro
    iapply HR.into_wand $$ HR' HP

-- The mask `E` is not determined by the argument and result slots (as for iris-lean's
-- `intoWand_fupd_args`).
set_option synthInstance.checkSynthOrder false in
/-- Rocq: `into_wand_bupd_args_pupd`. -/
instance (priority := low) into_wand_bupd_args_pupd {p q : Bool} {s : WandMode.Side}
    {E : CoPset} {R P Q : IProp GF} [HR : IntoWand p false R (.matching s) P Q] :
    IntoWand p q R (.matching s) (pupd E E P) (pupd E E Q) where
  into_wand := by
    refine wand_intro ?_
    refine (sep_mono HR.into_wand intuitionisticallyIf_elim).trans ?_
    iintro ⟨Hw, HP⟩
    imod HP
    imodintro
    iapply Hw $$ HP

/-- Rocq: `from_sep_bupd_pupd`. -/
instance from_sep_bupd_pupd {E : CoPset} {P Q1 Q2 : IProp GF} [HP : FromSep P Q1 Q2] :
    FromSep (pupd E E P) (pupd E E Q1) (pupd E E Q2) where
  from_sep := by
    iintro ⟨HQ1, HQ2⟩
    imod HQ1
    imod HQ2
    imodintro
    iapply HP.from_sep
    iframe

/-- Rocq: `from_exist_pupd`. -/
instance from_exist_pupd {B : Type _} {P : IProp GF} {E : CoPset} {Φ : B → IProp GF}
    [HP : FromExists P Φ] : FromExists (pupd E E P) (fun b => pupd E E (Φ b)) where
  from_exists := by
    iintro ⟨%x, Hx⟩
    imod Hx
    imodintro
    iapply HP.from_exists
    iexists x
    iexact Hx

/-- Rocq: `into_forall_pupd`. -/
instance into_forall_pupd {B : Type _} {P : IProp GF} {E : CoPset} {Φ : B → IProp GF}
    [HP : IntoForall P Φ] : IntoForall (pupd E E P) (fun b => pupd E E (Φ b)) where
  into_forall := by
    iintro H %b
    imod H
    imodintro
    iapply HP.into_forall $$ H

/-- Rocq: `from_assumption_pupd` (Rocq: a `KnownRFromAssumption` instance). -/
instance from_assumption_pupd {p : Bool} {io : InOut} {E : CoPset} {P Q : IProp GF}
    [HP : FromAssumption p io P Q] : FromAssumption p io P (pupd E E Q) where
  from_assumption := HP.from_assumption.trans (pupd_ret E Q)

/-- Rocq: `wp_pupd`. -/
theorem wp_pupd (Φ : val → IProp GF) (E : CoPset) (e : expr) :
    WP e @ E {{ x, pupd E E (Φ x) }} ⊢ WP e @ E {{ Φ }} := by
  iintro H
  iapply wp_strong_mono LawfulSet.subset_refl $$ H
  unfold pupd pupd_def
  iintro %σ1 %ρ1 %ε1 %v ⟨Hσ, Hρ, Hε, H⟩
  iapply H $$ %σ1 %ρ1 %ε1 [Hσ Hρ Hε]
  iframe

/-- Rocq: `pupd_wp`. -/
theorem pupd_wp (Φ : val → IProp GF) (E : CoPset) (e : expr) :
    pupd E E (WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }} := by
  iintro >H
  iexact H

/-! `pupd` works for allocation of invariants and ghost resources. -/

/-- Rocq: `pupd_inv_alloc`. -/
theorem pupd_inv_alloc (E : CoPset) (P : IProp GF) (N : Namespace) :
    ▷ P ⊢ pupd E E (inv N P) := by
  iintro HP
  imod inv_alloc N E P $$ HP with H
  imodintro
  iexact H

/-- Rocq: `pupd_inv_acc`. -/
theorem pupd_inv_acc (P : IProp GF) (E : CoPset) (I : IProp GF) (N : Namespace)
    (Hsubset : ↑N ⊆ E) :
    inv N I ⊢ (▷ I -∗ pupd (E \ ↑N) (E \ ↑N) iprop(P ∗ ▷ I)) -∗ pupd E E P := by
  iintro #Hinv H
  imod inv_acc Hsubset $$ Hinv with ⟨HI, Hclose⟩
  imod H $$ HI with ⟨HP, HI⟩
  imod Hclose $$ HI with -
  imodintro
  iexact HP

/-- Rocq: `pupd_inv_acc'`. -/
theorem pupd_inv_acc' (E : CoPset) (I : IProp GF) (N : Namespace) (Hsubset : ↑N ⊆ E) :
    inv N I ⊢
      pupd E (E \ ↑N) iprop(▷ I ∗ (▷ I -∗ pupd (E \ ↑N) E iprop(True))) := by
  iintro #Hinv
  imod inv_acc Hsubset $$ Hinv with ⟨HI, Hvs⟩
  imodintro
  iframe HI
  iintro HI
  imod Hvs $$ HI with -
  imodintro
  ipureintro
  trivial

/-- Rocq: `pupd_ra_alloc`. -/
theorem pupd_ra_alloc {F : COFE.OFunctorPre} [RFunctorContractive F] [ElemG GF F]
    (E : CoPset) (a : F.ap (IProp GF)) (H : ✓ a) :
    ⊢ pupd E E iprop(∃ γ, iOwn γ a) := by
  imod iOwn_alloc a H with H
  imodintro
  iexact H

end pupd

/- Sanity checks for the proof-mode instances. -/
section examples

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]

example {s : Stuckness} {E : CoPset} {e : expr} {Φ : val → IProp GF} (P : IProp GF) :
    pupd E E P ∗ (P -∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example {E1 E2 : CoPset} (h : E1 ⊆ E2) {e : expr} {Φ : val → IProp GF} (P : IProp GF) :
    pupd E1 E1 P ∗ (P -∗ WP e @ E2 {{ Φ }}) ⊢ WP e @ E2 {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example {E : CoPset} (P Q : IProp GF) : P ∗ pupd E E Q ⊢ pupd E E iprop(Q ∗ P) := by
  iintro ⟨HP, HQ⟩
  iframe HP
  iexact HQ

example {E : CoPset} (P : IProp GF) : (|={E}=> P) ⊢ pupd E E P := by
  iintro >HP
  iexact HP

end examples

end Foxtrot
