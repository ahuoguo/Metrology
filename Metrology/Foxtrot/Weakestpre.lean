module

public import Metrology.Foxtrot.FullInfo
public import Metrology.ConProbLang.Erasure
public import Metrology.Prob.CouplingsApp
public import Metrology.Iris.Fixpoint
public import Iris.BI.Lib.Fixpoint
public import Iris.BI.WeakestPre
public import Iris.ProofMode
public import Iris.Instances.Lib.FUpd

/-!
# The weakest precondition of Foxtrot

Ported from clutch/theories/foxtrot/weakestpre.v

Foxtrot is a concurrent probabilistic *relational* separation logic with error credits. The WP
of the left-hand-side program is interleaved with couplings against the right-hand-side
configuration (held in `spec_interp`), whose steps are chosen by a full-information oblivious
scheduler (`full_info_oscheduler`, see `Foxtrot.FullInfo`). As in Rocq, everything is
specialised to `con_prob_lang`.

* `foxtrotWpGS Λ GF` bundles the invariant ghost state (`InvGS_gen .hasNoLC GF`, Rocq:
  `invGS_gen HasNoLc Σ`), `state_interp`, `spec_interp` (on `cfg Λ`), `fork_post` and
  `err_interp`.
* `spec_coupl σ ρ ε Z` is the least fixpoint (`bi_least_fixpoint`) of `spec_coupl_pre Z`:
  either the error is `≥ 1`, or `Z σ ρ ε` holds, or the error can be amplified, or a
  scheduler-erasable LHS state distribution `μ` is (approximately) coupled with the limit
  execution of a full-information scheduler on the RHS, with an expected-error continuation.
* `prog_coupl e σ ρ ε Z` couples one LHS program step of `e` with an RHS scheduler execution.
* `wp_pre` is the WP pre-functor (contractive, `wp_pre_contractive`); the WP is its guarded
  fixpoint (`fixpoint`), exposed through iris-lean's `Wp` class (instance `wp'`), so that the
  `WP e @ s; E {{ Φ }}` notations of iris-lean apply.

## Rocq → Lean map
All Rocq names are kept: `foxtrotWpGS` (fields `foxtrotWpGS_invGS`, `state_interp`,
`spec_interp`, `fork_post`, `err_interp`), `spec_coupl_pre`, `spec_coupl_pre_ne`,
`spec_coupl_pre_mono`, `spec_coupl'`, `spec_coupl`, `spec_coupl_unfold`,
`spec_coupl_ret_err_ge_1`, `spec_coupl_ret`, `spec_coupl_amplify`, `spec_coupl_rec`,
`spec_coupl_ind`, `fupd_spec_coupl`, `spec_coupl_mono`, `spec_coupl_mono_err`,
`spec_coupl_bind`, `spec_coupl_step_l_dret_adv`, `spec_coupl_step_r_adv`, `spec_coupl_step_r`,
`prog_coupl`, `prog_coupl_mono_err`, `prog_coupl_strong_mono`, `prog_coupl_mono`,
`prog_coupl_strengthen`, `prog_coupl_ctx_bind`, `prog_coupl_reducible`,
`prog_coupl_step_l_dret_adv`, `prog_coupl_step_l_dret`, `prog_coupl_step_l`, `wp_pre`,
`wp_pre_contractive`, `wp'`, `wp_unfold`, `wp_ne`, `wp_contractive`, `wp_value_fupd'`,
`wp_strong_mono`, `wp_strong_mono'`, `spec_coupl_wp`, `fupd_wp`, `wp_fupd`, `wp_atomic`,
`wp_step_fupd`, `wp_bind`, `wp_mono`, `wp_mask_mono`, `wp_value_fupd`, `wp_value'`,
`wp_value`, `wp_frame_l`, `wp_frame_r`, `wp_frame_step_l`, `wp_frame_step_r`,
`wp_frame_step_l'`, `wp_frame_step_r'`, `wp_wand`, `wp_wand_l`, `wp_wand_r`,
`wp_frame_wand`, `frame_wp`, `is_except_0_wp`, `elim_modal_bupd_wp`, `elim_modal_fupd_wp`,
`elim_modal_fupd_wp_atomic`, `add_modal_fupd_wp`, `elim_acc_wp_atomic`, `elim_acc_wp_nonatomic`.

## Design choices / deviations (Rocq → Lean)
The file follows `Metrology/Coneris/Weakestpre.lean` closely:
* Configurations of the RHS are `CPState` (local notation for
  `(con_lang_mdp con_prob_lang).mdpstate`, reducibly `cfg`), as in `Foxtrot.Oscheduler` /
  `Foxtrot.FullInfo`, so that `osch_lim_exec osch.fi_osch ([], ρ)` and `cfg_to_cfg' ρ`
  typecheck. The `spec_coupl'` argument is `state × CPState × ℝ≥0∞` (Rocq:
  `state * cfg * nonnegreal`) with a discrete COFE (Rocq: `prodO (prodO stateO cfgO) NNRO`).
* Errors are `ℝ≥0∞` (Rocq: `nonnegreal`); nonnegativity/summability (`ex_expval`) side
  conditions vanish. The bounds `∀ x, X2 x ≤ r` with `r : ℝ≥0∞` are kept for fidelity (they are
  trivially satisfiable, e.g. by `⟨⊤, fun _ => le_top⟩`, so the field is vacuous; `X2` may also
  take the value `∞`). This only relaxes a Rocq summability side condition: the rules are no
  weaker for users and adequacy is still proved. Rocq's `(x > 0)%R` is `0 < x`.
* `sch_erasable (λ t _ _ sch, TapeOblivious t sch)` is `sch_erasable tape_oblivious_sch`
  (`tape_oblivious_sch` is a local copy of `Coneris.tape_oblivious_sch`, so that this file does
  not import Coneris).
* Scheduler application uses the explicit coercion: `osch_lim_exec osch.fi_osch ([], ρ)`.
* `<[j := e']> ρ.1` is `ρ.1.set j e'`; `ρ.1 !! j` is `ρ.1[j]?`; `tapes σ'` is `σ'.tapes`;
  Rocq's `λ '(e', σ', efs), ..` pattern lambdas use projections (`p.2.1.tapes`).
* Rocq `encode_nat` / `decode_nat` (stdpp `Countable`) are the local helpers `encode_nat` /
  `decode_nat` built from `Encodable.ofCountable`.
* The schedulers / error functions / coupling proofs that Rocq writes inline in
  `spec_coupl_step_l_dret_adv` and `prog_coupl_step_l_dret_adv` (same construction) are factored
  into `enc_osch`, `enc_X2`, `enc_osch_lim_exec`, `ARcoupl_pgl_dmap`; those of
  `spec_coupl_step_r_adv` into `inj_X2` (Rocq: `decide (∃ ..)` + `epsilon`),
  `ARcoupl_dret_pgl_dmap` and `full_info_one_step_stutter_osch j` (which is by definition
  Rocq's `full_info_cons_osch (λ _, dret j) (λ _, full_info_stutter_osch full_info_inhabitant)`).
* Wp class / stuckness: as in Coneris, the index type is iris-lean's `Stuckness` (ignored by
  the instance; `wp_stuckness_irrel`), instead of Rocq's `()`. Note that `Foxtrot.wp'` and
  `Coneris.pgl_wp'` are both instances of `Wp (IProp GF) expr val Stuckness`; where both ghost
  classes are available (e.g. in `coneris_relate`), select one with `(Wp := ...)`.
* `spec_coupl_pre`, `prog_coupl` and `wp_pre` are `abbrev`s (so the proof mode can destruct
  them); `spec_coupl'`/`spec_coupl` are `def`s (unfold with `spec_coupl_unfold`, an equation);
  the WP is iris-lean's opaque `fixpoint` (unfold with `wp_unfold`, an equation).
* `foxtrotWpGS` takes `Λ` as an `outParam`; `fork_post` needs `(Λ := con_prob_lang)` when its
  argument type is not otherwise determined.
* `wp_strong_mono`, `wp_strong_mono'`, `wp_step_fupd`, `wp_wand`, `wp_frame_wand` are stated as
  `⊢ A -∗ B -∗ C`; the modality lemmas `X -∗ Y -∗ Z` as `X ⊢ Y -∗ Z`; instance arguments
  (`Atomic`, `IntoVal`, `ConLanguageCtx`) are instance-implicit; `TCEq (to_val e) None` is a
  hypothesis `to_val e = none`.
* The proof-mode instances follow iris-lean's `ProgramLogic/WeakestPre.lean` (as in Coneris):
  `Frame` uses `FrameInstantiateExistDisabled`, `ElimModal` carries `InOut`, `elim_acc_wp_atomic`
  has `priority := low` (Rocq `| 100`), `elim_modal_fupd_wp` has `default + 10` and
  `elim_modal_fupd_wp_atomic` the default priority (see `Coneris.Weakestpre` for why).

## Omitted
* `Global Opaque foxtrotWpGS_invGS`, `Global Arguments FoxtrotWpGS`, `Hint Resolve cond_nonneg`,
  `Canonical Structure NNRO` (replaced by the discrete COFE instance).
* Sealing: `wp_def`, `wp_aux`, `wp_unseal` (iris-lean's `fixpoint` is opaque).
* `Proper` plumbing: `wp_proper` (follows from `wp_ne`), `wp_mono'`, `wp_flip_mono'`
  (use `wp_mono`).
* The commented-out Rocq lemmas (`spec_coupl_state_step`, `spec_coupl_iterM_state_adv_comp`,
  `spec_coupl_state_adv_comp`).

## Added helpers (not in Rocq)
`encode_nat`, `decode_nat`, `decode_encode_nat`, `encode_nat_inj`, `ARcoupl_pgl_dmap`,
`ARcoupl_dret_pgl_dmap` (generic `Prob` facts), `full_info_cons_stutter_lim_exec`, `enc_osch`,
`enc_osch_lim_exec`, `enc_X2`, `enc_X2_eq`, `inj_X2`, `inj_X2_eq`, `inj_X2_le`,
`tape_oblivious_sch`, `spec_coupl_ne`, `prog_coupl_ne`, `wp_pre_dist` (the Rocq `f_equiv`
proofs), `wp_stuckness_irrel`, `wp_unfold_none` (`wp_unfold` for a non-value).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-! ## Local helpers (not in the Rocq file) -/

section helpers

variable {A : Type} [Countable A]

/-- Helper (Rocq: `encode_nat`): a (classical) injective encoding into `ℕ`. -/
def encode_nat (a : A) : ℕ := @Encodable.encode A (Encodable.ofCountable A) a

/-- Helper (Rocq: `decode_nat`). -/
def decode_nat (n : ℕ) : Option A := @Encodable.decode A (Encodable.ofCountable A) n

/-- Helper (Rocq: `decode_encode_nat`). -/
@[simp] theorem decode_encode_nat (a : A) : decode_nat (encode_nat a) = some a :=
  @Encodable.encodek A (Encodable.ofCountable A) a

/-- Helper (Rocq: `encode_nat_inj`). -/
theorem encode_nat_inj : Function.Injective (encode_nat (A := A)) :=
  @Encodable.encode_injective A (Encodable.ofCountable A)

end helpers


/-! ### Local helpers for the coupling constructions (not in Rocq) -/

section coupl_helpers

variable {α β : Type*} [Countable α] [Countable β]

/-- Helper: a graded predicate lifting gives an approximate coupling of `μ` with its image
under `h` (Rocq: inline, via `ARcoupl_dbind`, `up_to_bad_lhs`, `ARcoupl_eq`). -/
theorem ARcoupl_pgl_dmap (μ : Distr α) (h : α → β) (R : α → Prop) (ε : ℝ≥0∞)
    (Hpgl : pgl μ R ε) : ARcoupl μ (dmap h μ) (fun a b => R a ∧ b = h a) ε := by
  have H1 : ARcoupl μ μ (fun x y => x = y ∧ R x) (0 + ε) :=
    up_to_bad_lhs μ μ R _ 0 ε
      (ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
        (fun x y hxy hR => ⟨hxy, hR⟩) le_rfl (ARcoupl_eq μ)) Hpgl
  have H2 := ARcoupl_dbind' (0 + ε) 0 ε (fun a => dret a) (fun a => dret (h a)) μ μ
    (fun x y => x = y ∧ R x) (fun a b => R a ∧ b = h a) (by simp)
    (fun a b hab => by
      obtain ⟨rfl, hR⟩ := hab
      exact ARcoupl_dret _ _ _ _ ⟨hR, rfl⟩) H1
  rwa [dret_id_right] at H2

/-- Helper: coupling a Dirac distribution with the image under `h` of a distribution of mass
one (Rocq: inline, via `ARcoupl_dbind`, `up_to_bad_rhs`, `ARcoupl_trivial`). -/
theorem ARcoupl_dret_pgl_dmap (a : α) (μ : Distr β) {γ : Type*} [Countable γ] (h : β → γ)
    (P : β → Prop) (ε : ℝ≥0∞) (Hmass : ∑' b, μ b = 1) (Hpgl : pgl μ P ε) :
    ARcoupl (dret a) (dmap h μ) (fun x y => x = a ∧ ∃ b, P b ∧ y = h b) ε := by
  have H1 : ARcoupl (dret ()) μ (fun _ b => P b) (0 + ε) :=
    up_to_bad_rhs (dret ()) μ P _ 0 ε
      (ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
        (fun _ _ _ hP => hP) le_rfl (ARcoupl_trivial _ _ (dret_mass ()) Hmass)) Hpgl
  have H2 := ARcoupl_dbind' (0 + ε) 0 ε (fun _ => dret a) (fun b => dret (h b)) (dret ()) μ
    (fun _ b => P b) (fun x y => x = a ∧ ∃ b, P b ∧ y = h b) (by simp)
    (fun _ b hb => ARcoupl_dret _ _ _ _ ⟨rfl, b, hb, rfl⟩) H1
  rwa [dret_id_left] at H2

end coupl_helpers

/-- Helper (not in Rocq): the limit execution of a `full_info_cons_osch` that stutters once
and then stops. -/
theorem full_info_cons_stutter_lim_exec (ν : cfg' → Distr ℕ) (ρ : CPState) :
    osch_lim_exec (full_info_cons_osch ν
        (fun _ => full_info_stutter_osch full_info_inhabitant)).fi_osch ([], ρ) =
      ν (cfg_to_cfg' ρ) ≫= fun x => dmap (fun ρ' : CPState =>
        (([(cfg_to_cfg' ρ, x), (cfg_to_cfg' ρ', ρ'.1.length)] : full_info_state), ρ'))
        (step' x ρ) := by
  rw [full_info_cons_osch_lim_exec]
  refine dbind_ext_right _ _ _ fun x => ?_
  rw [dmap]
  refine dbind_ext_right _ _ _ fun ρ' => ?_
  have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, x)]
    (full_info_stutter_osch full_info_inhabitant) [] ρ'
  simp only [List.append_nil] at this
  rw [this, full_info_stutter_osch_lim_exec, full_info_inhabitant_lim_exec, dmap_dret, dmap_dret]
  rfl

section enc_osch

variable {A : Type} [Countable A]

/-- Helper (Rocq: inline in `spec_coupl_step_l_dret_adv` / `prog_coupl_step_l_dret_adv`):
a scheduler that records a sample of `μ` in the history by stuttering with thread id
`n + encode_nat a` (out of bounds when `n` is the number of threads), then stutters once more
and stops. -/
def enc_osch (μ : Distr A) (n : ℕ) : full_info_oscheduler :=
  full_info_cons_osch (fun _ => dmap (fun x => n + encode_nat x) μ)
    (fun _ => full_info_stutter_osch full_info_inhabitant)

/-- Helper: the limit execution of `enc_osch`. -/
theorem enc_osch_lim_exec (μ : Distr A) (ρ : CPState) :
    osch_lim_exec (enc_osch μ ρ.1.length).fi_osch ([], ρ) =
      dmap (fun a => (([(cfg_to_cfg' ρ, ρ.1.length + encode_nat a),
        (cfg_to_cfg' ρ, ρ.1.length)] : full_info_state), ρ)) μ := by
  unfold enc_osch
  rw [full_info_cons_stutter_lim_exec, dmap, dmap, ← dbind_assoc]
  refine dbind_ext_right _ _ _ fun a => ?_
  rw [dret_id_left, out_of_bounds_step' _ _ (Nat.le_add_right _ _), dmap_dret]

/-- Helper (Rocq: inline): the error function reading back the sample recorded by `enc_osch`. -/
def enc_X2 (ε2 : A → ℝ≥0∞) (n : ℕ) (p : full_info_state × CPState) : ℝ≥0∞ :=
  match p.1[0]? with
  | some q =>
    match decode_nat (A := A) (q.2 - n) with
    | some x => ε2 x
    | none => 0
  | none => 0

@[simp] theorem enc_X2_eq (ε2 : A → ℝ≥0∞) (n : ℕ) (c : cfg') (a : A) (l : full_info_state)
    (ρ : CPState) : enc_X2 ε2 n ((c, n + encode_nat a) :: l, ρ) = ε2 a := by
  simp [enc_X2]

end enc_osch


section inj_X2

variable {A : Type*}

open Classical in
/-- Helper (Rocq: inline in `spec_coupl_step_r_adv`, via `decide (∃ ..)` and `epsilon`): the
error function reading back the preimage of the final configuration under `f`. -/
def inj_X2 (f : A → CPState) (ε2 : A → ℝ≥0∞) (q : full_info_state × CPState) : ℝ≥0∞ :=
  if h : ∃ p, q.2 = f p then ε2 (Classical.choose h) else 0

theorem inj_X2_eq {f : A → CPState} (Hf : Function.Injective f) (ε2 : A → ℝ≥0∞)
    (l : full_info_state) (p : A) : inj_X2 f ε2 (l, f p) = ε2 p := by
  have h : ∃ p', (l, f p).2 = f p' := ⟨p, rfl⟩
  unfold inj_X2
  rw [dite_eq_left h]
  exact congrArg ε2 (Hf (Classical.choose_spec h)).symm

theorem inj_X2_le {f : A → CPState} {ε2 : A → ℝ≥0∞} {r : ℝ≥0∞} (Hr : ∀ p, ε2 p ≤ r)
    (q : full_info_state × CPState) : inj_X2 f ε2 q ≤ r := by
  unfold inj_X2
  split
  · exact Hr _
  · exact zero_le

end inj_X2

/-! ## The ghost-state class -/

/-- Rocq: `foxtrotWpGS`. -/
class foxtrotWpGS (Λ : outParam conLanguage) (GF : BundledGFunctors) where
  [foxtrotWpGS_invGS : InvGS_gen .hasNoLC GF]
  state_interp : Λ.state → IProp GF
  spec_interp : ConProbLang.cfg Λ → IProp GF
  fork_post : Λ.val → IProp GF
  err_interp : ℝ≥0∞ → IProp GF

attribute [reducible, instance] foxtrotWpGS.foxtrotWpGS_invGS
export foxtrotWpGS (state_interp spec_interp fork_post err_interp)

/-- The discrete OFE on the arguments of `spec_coupl'` (Rocq: `prodO (prodO stateO cfgO) NNRO`). -/
instance : COFE (state × CPState × ℝ≥0∞) := COFE.ofDiscrete _
instance : OFE.Discrete (state × CPState × ℝ≥0∞) := ⟨id⟩

/-- The class of schedulers the LHS state steps are erasable for
(Rocq: `λ t _ _ sch, TapeOblivious t sch`). -/
abbrev tape_oblivious_sch : ∀ (t : Type) [DecidableEq t] [Countable t],
    scheduler (con_lang_mdp con_prob_lang) t → Prop :=
  fun t _ _ sch => TapeOblivious t sch

section modalities

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]

/-! ### spec_coupl -/

/-- Rocq: `spec_coupl_pre`. -/
abbrev spec_coupl_pre (Z : state → CPState → ℝ≥0∞ → IProp GF)
    (Φ : state × CPState × ℝ≥0∞ → IProp GF) : state × CPState × ℝ≥0∞ → IProp GF := fun x =>
  iprop(
  ⌜1 ≤ x.2.2⌝ ∨ Z x.1 x.2.1 x.2.2 ∨ (∀ ε', ⌜x.2.2 < ε'⌝ -∗ Φ (x.1, x.2.1, ε')) ∨
    ∃ (S : state → full_info_state × CPState → Prop) (μ : Distr state)
      (osch : full_info_oscheduler) (ε1 : ℝ≥0∞) (X2 : full_info_state × CPState → ℝ≥0∞)
      (r : ℝ≥0∞),
      ⌜sch_erasable tape_oblivious_sch μ x.1⌝ ∗
      ⌜∀ y, X2 y ≤ r⌝ ∗
      ⌜ε1 + Expval (osch_lim_exec osch.fi_osch ([], x.2.1)) X2 ≤ x.2.2⌝ ∗
      ⌜ARcoupl μ (osch_lim_exec osch.fi_osch ([], x.2.1)) S ε1⌝ ∗
      ⌜∀ σx σy ρx ρy l, S σx (l, ρx) → S σy (l, ρy) → σx = σy ∧ ρx = ρy⌝ ∗
      ∀ σ2 l ρ', ⌜S σ2 (l, ρ')⌝ ={∅}=∗ Φ (σ2, ρ', X2 (l, ρ')))

/-- Rocq: `spec_coupl_pre_ne`. -/
instance spec_coupl_pre_ne (Z : state → CPState → ℝ≥0∞ → IProp GF)
    (Φ : state × CPState × ℝ≥0∞ → IProp GF) : NonExpansive (spec_coupl_pre Z Φ) :=
  nonExpansive_of_discrete_leibniz _

/-- Rocq: `spec_coupl_pre_mono`. -/
instance spec_coupl_pre_mono (Z : state → CPState → ℝ≥0∞ → IProp GF) :
    BIMonoPred (spec_coupl_pre Z) where
  mono_pred {_ _ _ _} := by
    iintro #Hwand %x H
    icases H with (H | H | H | ⟨%S, %μ, %osch, %ε1, %X2, %r, %H1, %H2, %H3, %H4, %H5, H⟩)
    · ileft
      iexact H
    · iright
      ileft
      iexact H
    · iright
      iright
      ileft
      iintro %ε' %Hε'
      iapply Hwand
      iapply H $$ %ε' %Hε'
    · iright
      iright
      iright
      iexists S, μ, osch, ε1, X2, r
      iframe %
      iintro %σ2 %l %ρ' %HS
      imod H $$ %σ2 %l %ρ' %HS with H
      imodintro
      iapply Hwand $$ H
  mono_pred_ne := nonExpansive_of_discrete_leibniz _

/-- Rocq: `spec_coupl'`. -/
def spec_coupl' (Z : state → CPState → ℝ≥0∞ → IProp GF) : state × CPState × ℝ≥0∞ → IProp GF :=
  bi_least_fixpoint (spec_coupl_pre Z)

/-- Rocq: `spec_coupl`. -/
def spec_coupl (σ : state) (ρ : CPState) (ε : ℝ≥0∞) (Z : state → CPState → ℝ≥0∞ → IProp GF) :
    IProp GF :=
  spec_coupl' Z (σ, ρ, ε)

/-- Rocq: `spec_coupl_unfold`. -/
theorem spec_coupl_unfold (σ1 : state) (ρ : CPState) (ε : ℝ≥0∞)
    (Z : state → CPState → ℝ≥0∞ → IProp GF) :
    spec_coupl σ1 ρ ε Z = iprop(
      ⌜1 ≤ ε⌝ ∨ Z σ1 ρ ε ∨ (∀ ε', ⌜ε < ε'⌝ -∗ spec_coupl σ1 ρ ε' Z) ∨
        ∃ (S : state → full_info_state × CPState → Prop) (μ : Distr state)
          (osch : full_info_oscheduler) (ε1 : ℝ≥0∞) (X2 : full_info_state × CPState → ℝ≥0∞)
          (r : ℝ≥0∞),
          ⌜sch_erasable tape_oblivious_sch μ σ1⌝ ∗
          ⌜∀ y, X2 y ≤ r⌝ ∗
          ⌜ε1 + Expval (osch_lim_exec osch.fi_osch ([], ρ)) X2 ≤ ε⌝ ∗
          ⌜ARcoupl μ (osch_lim_exec osch.fi_osch ([], ρ)) S ε1⌝ ∗
          ⌜∀ σx σy ρx ρy l, S σx (l, ρx) → S σy (l, ρy) → σx = σy ∧ ρx = ρy⌝ ∗
          ∀ σ2 l ρ', ⌜S σ2 (l, ρ')⌝ ={∅}=∗ spec_coupl σ2 ρ' (X2 (l, ρ')) Z) := by
  unfold spec_coupl spec_coupl'
  rw [least_fixpoint_unfold]

/-- Rocq: `spec_coupl_ret_err_ge_1`. -/
theorem spec_coupl_ret_err_ge_1 (σ1 : state) (ρ1 : CPState)
    (Z : state → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) (h : 1 ≤ ε) :
    ⊢ spec_coupl σ1 ρ1 ε Z := by
  rw [spec_coupl_unfold]
  ileft
  ipureintro
  exact h

/-- Rocq: `spec_coupl_ret`. -/
theorem spec_coupl_ret (σ1 : state) (ρ1 : CPState) (Z : state → CPState → ℝ≥0∞ → IProp GF)
    (ε : ℝ≥0∞) : Z σ1 ρ1 ε ⊢ spec_coupl σ1 ρ1 ε Z := by
  rw [spec_coupl_unfold]
  iintro H
  iright
  ileft
  iexact H

/-- Rocq: `spec_coupl_amplify`. -/
theorem spec_coupl_amplify (σ1 : state) (ρ1 : CPState) (Z : state → CPState → ℝ≥0∞ → IProp GF)
    (ε : ℝ≥0∞) :
    (∀ ε', ⌜ε < ε'⌝ -∗ spec_coupl σ1 ρ1 ε' Z) ⊢ spec_coupl σ1 ρ1 ε Z := by
  rw [spec_coupl_unfold σ1 ρ1 ε]
  iintro H
  iright
  iright
  ileft
  iexact H

/-- Rocq: `spec_coupl_rec`. -/
theorem spec_coupl_rec (σ1 : state) (ρ1 : CPState) (ε : ℝ≥0∞)
    (Z : state → CPState → ℝ≥0∞ → IProp GF) :
    (∃ (S : state → full_info_state × CPState → Prop) (μ : Distr state)
        (osch : full_info_oscheduler) (ε1 : ℝ≥0∞) (X2 : full_info_state × CPState → ℝ≥0∞)
        (r : ℝ≥0∞),
        ⌜sch_erasable tape_oblivious_sch μ σ1⌝ ∗
        ⌜∀ y, X2 y ≤ r⌝ ∗
        ⌜ε1 + Expval (osch_lim_exec osch.fi_osch ([], ρ1)) X2 ≤ ε⌝ ∗
        ⌜ARcoupl μ (osch_lim_exec osch.fi_osch ([], ρ1)) S ε1⌝ ∗
        ⌜∀ σx σy ρx ρy l, S σx (l, ρx) → S σy (l, ρy) → σx = σy ∧ ρx = ρy⌝ ∗
        ∀ σ2 l ρ', ⌜S σ2 (l, ρ')⌝ ={∅}=∗ spec_coupl σ2 ρ' (X2 (l, ρ')) Z) ⊢
      spec_coupl σ1 ρ1 ε Z := by
  rw [spec_coupl_unfold σ1 ρ1 ε]
  iintro H
  iright
  iright
  iright
  iexact H

/-- Rocq: `spec_coupl_ind`. -/
theorem spec_coupl_ind (Ψ Z : state → CPState → ℝ≥0∞ → IProp GF) :
    ⊢ □ (∀ σ ρ ε, spec_coupl_pre Z
          (fun x => iprop(Ψ x.1 x.2.1 x.2.2 ∧ spec_coupl x.1 x.2.1 x.2.2 Z)) (σ, ρ, ε) -∗
          Ψ σ ρ ε) -∗
      ∀ σ ρ ε, spec_coupl σ ρ ε Z -∗ Ψ σ ρ ε := by
  have h : (fun x : state × CPState × ℝ≥0∞ =>
      iprop(Ψ x.1 x.2.1 x.2.2 ∧ spec_coupl x.1 x.2.1 x.2.2 Z)) =
      fun x => iprop(Ψ x.1 x.2.1 x.2.2 ∧ bi_least_fixpoint (spec_coupl_pre Z) x) := rfl
  rw [h]
  unfold spec_coupl spec_coupl'
  iintro #IH %σ %ρ %ε H
  iapply least_fixpoint_ind (spec_coupl_pre Z) (fun x => Ψ x.1 x.2.1 x.2.2)
    (IN := nonExpansive_of_discrete_leibniz _) $$ [] %(σ, ρ, ε) H
  iintro !> %⟨σ', ρ', ε'⟩ Hx
  iapply IH $$ %σ' %ρ' %ε' Hx

/-- Rocq: `fupd_spec_coupl`. -/
theorem fupd_spec_coupl (σ1 : state) (ρ1 : CPState) (Z : state → CPState → ℝ≥0∞ → IProp GF)
    (ε : ℝ≥0∞) : (|={∅}=> spec_coupl σ1 ρ1 ε Z) ⊢ spec_coupl σ1 ρ1 ε Z := by
  iintro H
  iapply spec_coupl_rec
  iexists (fun x y => x = σ1 ∧ y = ([], ρ1)), dret σ1, full_info_inhabitant, 0,
    (fun _ => ε), ε
  isplitr
  · ipureintro
    exact dret_sch_erasable (Λ := con_prob_lang) σ1 _
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [full_info_inhabitant_lim_exec, Expval_dret, zero_add]
  isplitr
  · ipureintro
    rw [full_info_inhabitant_lim_exec]
    exact ARcoupl_dret _ _ _ _ ⟨rfl, rfl⟩
  isplitr
  · ipureintro
    rintro _ _ _ _ _ ⟨rfl, h1⟩ ⟨rfl, h2⟩
    exact ⟨rfl, (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm⟩
  iintro %σ2 %l %ρ' %HS
  obtain ⟨rfl, h⟩ := HS
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  iexact H

/-- Rocq: `spec_coupl_mono`. -/
theorem spec_coupl_mono (σ1 : state) (ρ1 : CPState) (Z1 Z2 : state → CPState → ℝ≥0∞ → IProp GF)
    (ε : ℝ≥0∞) :
    (∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ Z2 σ2 ρ2 ε') ⊢
      spec_coupl σ1 ρ1 ε Z1 -∗ spec_coupl σ1 ρ1 ε Z2 := by
  iintro HZ Hs
  iapply spec_coupl_ind
    (fun σ ρ ε => iprop((∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ Z2 σ2 ρ2 ε') -∗ spec_coupl σ ρ ε Z2)) Z1
    $$ [] %σ1 %ρ1 %ε Hs HZ
  iintro !> %σ %ρ %ε' H Hw
  icases H with (%H | H | H | ⟨%S, %μ, %osch, %ε1, %X2, %r, %H1, %H2, %H3, %H4, %H5, H⟩)
  · iapply spec_coupl_ret_err_ge_1 _ _ _ _ H
  · iapply spec_coupl_ret
    iapply Hw $$ H
  · iapply spec_coupl_amplify
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨IH, -⟩
    iapply IH $$ Hw
  · iapply spec_coupl_rec
    iexists S, μ, osch, ε1, X2, r
    iframe %
    iintro %σ2 %l %ρ' %HS
    imod H $$ %σ2 %l %ρ' %HS with ⟨IH, -⟩
    imodintro
    iapply IH $$ Hw

/-- Rocq: `spec_coupl_mono_err`. -/
theorem spec_coupl_mono_err (ε1 ε2 : ℝ≥0∞) (σ1 : state) (ρ1 : CPState)
    (Z : state → CPState → ℝ≥0∞ → IProp GF) (Heps : ε1 ≤ ε2) :
    spec_coupl σ1 ρ1 ε1 Z ⊢ spec_coupl σ1 ρ1 ε2 Z := by
  iintro Hs
  iapply spec_coupl_rec
  iexists (fun x y => x = σ1 ∧ y = ([], ρ1)), dret σ1, full_info_inhabitant, 0,
    (fun _ => ε1), ε1
  isplitr
  · ipureintro
    exact dret_sch_erasable (Λ := con_prob_lang) σ1 _
  isplitr
  · ipureintro
    exact fun _ => le_rfl
  isplitr
  · ipureintro
    rw [full_info_inhabitant_lim_exec, Expval_dret, zero_add]
    exact Heps
  isplitr
  · ipureintro
    rw [full_info_inhabitant_lim_exec]
    exact ARcoupl_dret _ _ _ _ ⟨rfl, rfl⟩
  isplitr
  · ipureintro
    rintro _ _ _ _ _ ⟨rfl, h1⟩ ⟨rfl, h2⟩
    exact ⟨rfl, (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm⟩
  iintro %σ2 %l %ρ' %HS
  obtain ⟨rfl, h⟩ := HS
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  imodintro
  iexact Hs

/-- Rocq: `spec_coupl_bind`. -/
theorem spec_coupl_bind (σ1 : state) (ρ1 : CPState) (Z1 Z2 : state → CPState → ℝ≥0∞ → IProp GF)
    (ε : ℝ≥0∞) :
    (∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ spec_coupl σ2 ρ2 ε' Z2) ⊢
      spec_coupl σ1 ρ1 ε Z1 -∗ spec_coupl σ1 ρ1 ε Z2 := by
  iintro HZ Hs
  iapply spec_coupl_ind
    (fun σ ρ ε => iprop((∀ σ2 ρ2 ε', Z1 σ2 ρ2 ε' -∗ spec_coupl σ2 ρ2 ε' Z2) -∗
      spec_coupl σ ρ ε Z2)) Z1
    $$ [] %σ1 %ρ1 %ε Hs HZ
  iintro !> %σ %ρ %ε' H HZ
  icases H with (%H | H | H | ⟨%S, %μ, %osch, %ε1, %X2, %r, %H1, %H2, %H3, %H4, %H5, H⟩)
  · iapply spec_coupl_ret_err_ge_1 _ _ _ _ H
  · iapply HZ $$ H
  · iapply spec_coupl_amplify
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨IH, -⟩
    iapply IH $$ HZ
  · iapply spec_coupl_rec
    iexists S, μ, osch, ε1, X2, r
    iframe %
    iintro %σ2 %l %ρ' %HS
    imod H $$ %σ2 %l %ρ' %HS with ⟨IH, -⟩
    imodintro
    iapply IH $$ HZ

/-- Rocq: `spec_coupl_step_l_dret_adv`. -/
theorem spec_coupl_step_l_dret_adv (R : state → Prop) (μ : Distr state) (ε1 : ℝ≥0∞)
    (ε2 : state → ℝ≥0∞) (ρ1 : CPState) (σ1 : state) (Z : state → CPState → ℝ≥0∞ → IProp GF)
    (ε : ℝ≥0∞) (Herasable : sch_erasable tape_oblivious_sch μ σ1)
    (Hbound : ∃ r, ∀ ρ, ε2 ρ ≤ r) (Hineq : ε1 + Expval μ ε2 ≤ ε) (Hpgl : pgl μ R ε1) :
    (∀ σ2, ⌜R σ2⌝ ={∅}=∗ spec_coupl σ2 ρ1 (ε2 σ2) Z) ⊢ spec_coupl σ1 ρ1 ε Z := by
  obtain ⟨r, Hr⟩ := Hbound
  -- `n` is the number of threads, so thread ids `n + encode_nat σ'` stutter.
  have Hlim := enc_osch_lim_exec μ ρ1
  iintro H
  iapply spec_coupl_rec
  iexists (fun σ' p => R σ' ∧ p.2 = ρ1 ∧
      p.1 = [(cfg_to_cfg' ρ1, ρ1.1.length + encode_nat σ'), (cfg_to_cfg' ρ1, ρ1.1.length)]),
    μ, enc_osch μ ρ1.1.length, ε1, enc_X2 ε2 ρ1.1.length, r
  isplitr
  · ipureintro
    exact Herasable
  isplitr
  · ipureintro
    intro y
    unfold enc_X2
    split
    · split
      · exact Hr _
      · exact zero_le
    · exact zero_le
  isplitr
  · ipureintro
    rw [Hlim, Expval_dmap]
    refine le_trans (le_of_eq ?_) Hineq
    congr 2
    funext a
    exact enc_X2_eq _ _ _ _ _ _
  isplitr
  · ipureintro
    rw [Hlim]
    refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
      (ARcoupl_pgl_dmap μ _ R ε1 Hpgl)
    rintro a b ⟨hR, rfl⟩
    exact ⟨hR, rfl, rfl⟩
  isplitr
  · ipureintro
    rintro x1 x2 ρx ρy l ⟨-, h1, h2⟩ ⟨-, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    subst h1 h3
    rw [h2] at h4
    refine ⟨encode_nat_inj ?_, rfl⟩
    have := congrArg (fun l : full_info_state => (l.head?.map Prod.snd)) h4
    simpa using this
  iintro %σ2 %l %ρ' %HS
  obtain ⟨hR, h1, h2⟩ := HS
  dsimp only at h1 h2
  subst h1 h2
  rw [enc_X2_eq]
  iapply H $$ %σ2 %hR

/-- Rocq: `spec_coupl_step_r_adv`. -/
theorem spec_coupl_step_r_adv (R : expr × state × List expr → Prop) (ε1 : ℝ≥0∞)
    (m : Std.ExtTreeMap Loc tape) (ε2 : expr × state × List expr → ℝ≥0∞) (ρ1 : CPState)
    (σ1 : state) (Z : state → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) (j : ℕ) (e : expr)
    (Hreducible : reducible (Λ := con_prob_lang) e ρ1.2) (Hsome : ρ1.1[j]? = some e)
    (Hbound : ∃ r, ∀ ρ, ε2 ρ ≤ r)
    (Hineq : ε1 + Expval (prim_step (Λ := con_prob_lang) e ρ1.2) ε2 ≤ ε)
    (Hpgl : pgl (prim_step (Λ := con_prob_lang) e ρ1.2) (fun p => R p ∧ p.2.1.tapes = m) ε1) :
    (∀ e' σ' efs, ⌜R (e', σ', efs) ∧ σ'.tapes = m⌝ ={∅}=∗
      spec_coupl σ1 ((ρ1.1.set j e' ++ efs, σ') : CPState) (ε2 (e', σ', efs)) Z) ⊢
      spec_coupl σ1 ρ1 ε Z := by
  obtain ⟨r, Hr⟩ := Hbound
  have Hval : ConProbLang.to_val (Λ := con_prob_lang) e = none := by
    obtain ⟨ρ, hρ⟩ := Hreducible
    exact val_stuck _ _ _ hρ
  have Hj : j < ρ1.1.length := (List.getElem?_eq_some_iff.1 Hsome).1
  obtain ⟨f, hf⟩ : ∃ f : expr × state × List expr → CPState,
      f = fun p => ((ρ1.1.set j p.1 ++ p.2.2, p.2.1) : CPState) := ⟨_, rfl⟩
  have Hf : Function.Injective f := by
    rintro ⟨e1, s1, l1⟩ ⟨e2, s2, l2⟩ h
    subst hf
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp)
    have h5 := congrArg (fun l : List expr => l[j]?) h3
    simp only [List.getElem?_set_self Hj] at h5
    dsimp only at h2 h4
    subst h2 h4
    cases h5
    rfl
  have Hstep : step' j ρ1 = dmap f (prim_step (Λ := con_prob_lang) e ρ1.2) := by
    subst hf
    simp only [step', Hsome, Hval]
  obtain ⟨k, hk⟩ : ∃ k : CPState → full_info_state × CPState,
      k = fun ρ' => (([(cfg_to_cfg' ρ1, j), (cfg_to_cfg' ρ', ρ'.1.length)] : full_info_state), ρ') :=
    ⟨_, rfl⟩
  have Hlim : osch_lim_exec (full_info_one_step_stutter_osch j).fi_osch ([], ρ1) =
      dmap (k ∘ f) (prim_step (Λ := con_prob_lang) e ρ1.2) := by
    rw [full_info_one_step_stutter_osch_lim_exec, Hstep, dmap_comp, hk]
  iintro H
  iapply spec_coupl_rec
  -- Rocq: `full_info_cons_osch (λ _, dret j) (λ _, full_info_stutter_osch full_info_inhabitant)`,
  -- which is `full_info_one_step_stutter_osch j` by definition.
  iexists (fun σ' q => σ' = σ1 ∧ ∃ e' σ'' efs, R (e', σ'', efs) ∧ σ''.tapes = m ∧
      q.2 = f (e', σ'', efs) ∧ q.1 = [(cfg_to_cfg' ρ1, j), (cfg_to_cfg' q.2, q.2.1.length)]),
    dret σ1, full_info_one_step_stutter_osch j, ε1, inj_X2 f ε2, r
  isplitr
  · ipureintro
    exact dret_sch_erasable (Λ := con_prob_lang) σ1 _
  isplitr
  · ipureintro
    exact inj_X2_le Hr
  isplitr
  · ipureintro
    rw [Hlim, Expval_dmap]
    refine le_trans (le_of_eq ?_) Hineq
    congr 2
    funext p
    rw [Function.comp_apply, hk]
    exact inj_X2_eq Hf ε2 _ p
  isplitr
  · ipureintro
    rw [Hlim]
    refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
      (ARcoupl_dret_pgl_dmap σ1 _ (k ∘ f) _ ε1 (prim_step_mass _ _ Hreducible) Hpgl)
    rintro a b ⟨rfl, ⟨e', σ'', efs⟩, ⟨hR, ht⟩, rfl⟩
    subst hk
    exact ⟨rfl, e', σ'', efs, hR, ht, rfl, rfl⟩
  isplitr
  · ipureintro
    rintro σx σy ρx ρy l ⟨hx, ex, sx, fx, -, htx, hx2, hx1⟩ ⟨hy, ey, sy, fy, -, hty, hy2, hy1⟩
    refine ⟨hx.trans hy.symm, ?_⟩
    dsimp only at hx1 hx2 hy1 hy2
    rw [hx1] at hy1
    have hc : cfg_to_cfg' ρx = cfg_to_cfg' ρy := by
      have := congrArg (fun l : full_info_state => (l[1]?).map Prod.fst) hy1
      simpa using this
    simp only [cfg_to_cfg', Prod.mk.injEq] at hc
    refine Prod.ext hc.1 (state.ext' hc.2 ?_)
    rw [hx2, hy2, hf]
    exact htx.trans hty.symm
  iintro %σ2 %l %ρ' %HS
  obtain ⟨rfl, e', σ'', efs, hR, ht, h2, h1⟩ := HS
  dsimp only at h1 h2
  subst h1 h2
  rw [inj_X2_eq Hf]
  subst hf
  iapply H $$ %e' %σ'' %efs %⟨hR, ht⟩

/-- Rocq: `spec_coupl_step_r`. -/
theorem spec_coupl_step_r (R : expr × state × List expr → Prop) (ε1 : ℝ≥0∞)
    (m : Std.ExtTreeMap Loc tape) (ε2 : ℝ≥0∞) (ρ1 : CPState)
    (σ1 : state) (Z : state → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) (j : ℕ) (e : expr)
    (Hreducible : reducible (Λ := con_prob_lang) e ρ1.2) (Hsome : ρ1.1[j]? = some e)
    (Hineq : ε1 + ε2 ≤ ε)
    (Hpgl : pgl (prim_step (Λ := con_prob_lang) e ρ1.2) (fun p => R p ∧ p.2.1.tapes = m) ε1) :
    (∀ e' σ' efs, ⌜R (e', σ', efs) ∧ σ'.tapes = m⌝ ={∅}=∗
      spec_coupl σ1 ((ρ1.1.set j e' ++ efs, σ') : CPState) ε2 Z) ⊢
      spec_coupl σ1 ρ1 ε Z := by
  refine spec_coupl_step_r_adv R ε1 m (fun _ => ε2) ρ1 σ1 Z ε j e Hreducible Hsome
    ⟨ε2, fun _ => le_rfl⟩ ?_ Hpgl
  rw [Expval_const, prim_step_mass _ _ Hreducible, mul_one]
  exact Hineq


/-! ### One step prog coupl -/

/-- Rocq: `prog_coupl`. -/
abbrev prog_coupl (e1 : expr) (σ1 : state) (ρ1 : CPState) (ε : ℝ≥0∞)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) : IProp GF := iprop(
  ∃ (S : expr × state × List expr → full_info_state × CPState → Prop)
    (osch : full_info_oscheduler) (ε1 : ℝ≥0∞) (X2 : full_info_state × CPState → ℝ≥0∞)
    (r : ℝ≥0∞),
    ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
    ⌜∀ x, X2 x ≤ r⌝ ∗
    ⌜ε1 + Expval (osch_lim_exec osch.fi_osch ([], ρ1)) X2 ≤ ε⌝ ∗
    ⌜ARcoupl (prim_step (Λ := con_prob_lang) e1 σ1) (osch_lim_exec osch.fi_osch ([], ρ1)) S ε1⌝ ∗
    ⌜∀ x1 x2 l y1 y2, S x1 (l, y1) → S x2 (l, y2) → x1 = x2 ∧ y1 = y2⌝ ∗
    ∀ e2 σ2 efs l ρ2, ⌜S (e2, σ2, efs) (l, ρ2)⌝ ={∅}=∗ Z e2 σ2 efs ρ2 (X2 (l, ρ2)))

/-- Rocq: `prog_coupl_mono_err`. -/
theorem prog_coupl_mono_err (e : expr) (σ : state) (ρ : CPState)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (ε ε' : ℝ≥0∞) (h : ε ≤ ε') :
    prog_coupl e σ ρ ε Z ⊢ prog_coupl e σ ρ ε' Z := by
  iintro ⟨%S, %osch, %ε1, %X2, %r, %Hred, %Hr, %Hineq, %Hcoupl, %Hinj, H⟩
  iexists S, osch, ε1, X2, r
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact Hr
  isplitr
  · ipureintro
    exact Hineq.trans h
  iframe %
  iexact H

/-- Rocq: `prog_coupl_strong_mono`. -/
theorem prog_coupl_strong_mono (e1 : expr) (σ1 : state) (ρ1 : CPState)
    (Z1 Z2 : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (∀ e2 σ2 ρ2 ε' efs, ⌜∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ (e2, σ2, efs)⌝ ∗
        Z1 e2 σ2 efs ρ2 ε' -∗ Z2 e2 σ2 efs ρ2 ε') ⊢
      prog_coupl e1 σ1 ρ1 ε Z1 -∗ prog_coupl e1 σ1 ρ1 ε Z2 := by
  iintro Hm ⟨%S, %osch, %ε1, %X2, %r, %Hred, %Hr, %Hineq, %Hcoupl, %Hinj, H⟩
  iexists (fun a b => S a b ∧ 0 < prim_step (Λ := con_prob_lang) e1 σ1 a ∧
      0 < osch_lim_exec osch.fi_osch ([], ρ1) b), osch, ε1, X2, r
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact Hr
  isplitr
  · ipureintro
    exact Hineq
  isplitr
  · ipureintro
    exact ARcoupl_pos_R _ _ S ε1 Hcoupl
  isplitr
  · ipureintro
    rintro x1 x2 l y1 y2 ⟨h1, -⟩ ⟨h2, -⟩
    exact Hinj x1 x2 l y1 y2 h1 h2
  iintro %e2 %σ2 %efs %l %ρ2 %⟨HS, Hpos, -⟩
  imod H $$ %e2 %σ2 %efs %l %ρ2 %HS with H
  imodintro
  iapply Hm
  iframe H
  ipureintro
  exact ⟨σ1, Hpos⟩

/-- Rocq: `prog_coupl_mono`. -/
theorem prog_coupl_mono (e1 : expr) (σ1 : state) (ρ1 : CPState)
    (Z1 Z2 : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (∀ e2 σ2 efs ρ2 ε', Z1 e2 σ2 efs ρ2 ε' -∗ Z2 e2 σ2 efs ρ2 ε') ⊢
      prog_coupl e1 σ1 ρ1 ε Z1 -∗ prog_coupl e1 σ1 ρ1 ε Z2 := by
  iintro Hm ⟨%S, %osch, %ε1, %X2, %r, %Hred, %Hr, %Hineq, %Hcoupl, %Hinj, H⟩
  iexists S, osch, ε1, X2, r
  iframe %
  iintro %e2 %σ2 %efs %l %ρ2 %HS
  imod H $$ %e2 %σ2 %efs %l %ρ2 %HS with H
  imodintro
  iapply Hm $$ H

/-- Rocq: `prog_coupl_strengthen`. -/
theorem prog_coupl_strengthen (e1 : expr) (σ1 : state) (ρ1 : CPState)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    prog_coupl e1 σ1 ρ1 ε Z ⊢
      prog_coupl e1 σ1 ρ1 ε (fun e2 σ2 efs ρ2 ε' => iprop(
        ⌜∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ (e2, σ2, efs)⌝ ∧ Z e2 σ2 efs ρ2 ε')) := by
  iintro ⟨%S, %osch, %ε1, %X2, %r, %Hred, %Hr, %Hineq, %Hcoupl, %Hinj, H⟩
  iexists (fun a b => S a b ∧ 0 < prim_step (Λ := con_prob_lang) e1 σ1 a ∧
      0 < osch_lim_exec osch.fi_osch ([], ρ1) b), osch, ε1, X2, r
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact Hr
  isplitr
  · ipureintro
    exact Hineq
  isplitr
  · ipureintro
    exact ARcoupl_pos_R _ _ S ε1 Hcoupl
  isplitr
  · ipureintro
    rintro x1 x2 l y1 y2 ⟨h1, -⟩ ⟨h2, -⟩
    exact Hinj x1 x2 l y1 y2 h1 h2
  iintro %e2 %σ2 %efs %l %ρ2 %⟨HS, Hpos, -⟩
  imod H $$ %e2 %σ2 %efs %l %ρ2 %HS with H
  imodintro
  isplit
  · ipureintro
    exact ⟨σ1, Hpos⟩
  · iexact H

/-- Rocq: `prog_coupl_ctx_bind`. -/
theorem prog_coupl_ctx_bind (K : expr → expr) [ConLanguageCtx (Λ := con_prob_lang) K]
    (e1 : expr) (σ1 : state) (ρ1 : CPState)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞)
    (Hv : ConProbLang.to_val (Λ := con_prob_lang) e1 = none) :
    prog_coupl e1 σ1 ρ1 ε (fun e2 σ2 efs ρ2 ε' => Z (K e2) σ2 efs ρ2 ε') ⊢
      prog_coupl (K e1) σ1 ρ1 ε Z := by
  iintro ⟨%S, %osch, %ε1, %X2, %r, %Hred, %Hr, %Hineq, %Hcoupl, %Hinj, H⟩
  iexists (fun p ρ2 => ∃ e2', p.1 = K e2' ∧ S (e2', p.2.1, p.2.2) ρ2), osch, ε1, X2, r
  isplitr
  · ipureintro
    exact reducible_fill (Λ := con_prob_lang) (K := K) e1 σ1 Hred
  isplitr
  · ipureintro
    exact Hr
  isplitr
  · ipureintro
    exact Hineq
  isplitr
  · ipureintro
    rw [fill_dmap (Λ := con_prob_lang) (K := K) e1 σ1 Hv, dmap,
      ← dret_id_right (osch_lim_exec osch.fi_osch ([], ρ1))]
    refine ARcoupl_dbind' ε1 0 ε1 _ _ _ _ S _ (add_zero _).symm (fun a b hab => ?_) Hcoupl
    exact ARcoupl_dret _ _ _ _ ⟨a.1, rfl, hab⟩
  isplitr
  · ipureintro
    rintro ⟨x1, s1, f1⟩ ⟨x2, s2, f2⟩ l y1 y2 ⟨e1', h1, H1⟩ ⟨e2', h2, H2⟩
    obtain ⟨h3, h4⟩ := Hinj _ _ _ _ _ H1 H2
    obtain ⟨rfl, rfl, rfl⟩ : e1' = e2' ∧ s1 = s2 ∧ f1 = f2 := by simpa using h3
    dsimp only at h1 h2
    subst h1 h2
    exact ⟨rfl, h4⟩
  iintro %e2 %σ2 %efs %l %ρ2 %⟨e2', h, HS⟩
  dsimp only at h
  subst h
  iapply H $$ %e2' %σ2 %efs %l %ρ2 %HS

/-- Rocq: `prog_coupl_reducible`. -/
theorem prog_coupl_reducible (e : expr) (σ : state) (ρ : CPState)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    prog_coupl e σ ρ ε Z ⊢ ⌜reducible (Λ := con_prob_lang) e σ⌝ := by
  iintro ⟨%S, %osch, %ε1, %X2, %r, %Hred, -⟩
  ipureintro
  exact Hred

/-- Rocq: `prog_coupl_step_l_dret_adv`. -/
theorem prog_coupl_step_l_dret_adv (ε ε1 : ℝ≥0∞) (X2 : expr × state × List expr → ℝ≥0∞)
    (R : expr × state × List expr → Prop) (e1 : expr) (σ1 : state) (ρ1 : CPState)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF)
    (Hineq : ε1 + Expval (prim_step (Λ := con_prob_lang) e1 σ1) X2 ≤ ε)
    (Hred : reducible (Λ := con_prob_lang) e1 σ1) (Hbound : ∃ r, ∀ ρ, X2 ρ ≤ r)
    (Hpgl : pgl (prim_step (Λ := con_prob_lang) e1 σ1) R ε1) :
    (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs ρ1 (X2 (e2, σ2, efs))) ⊢
      prog_coupl e1 σ1 ρ1 ε Z := by
  obtain ⟨r, Hr⟩ := Hbound
  have Hlim := enc_osch_lim_exec (prim_step (Λ := con_prob_lang) e1 σ1) ρ1
  iintro H
  iexists (fun p q => R p ∧ q.2 = ρ1 ∧
      q.1 = [(cfg_to_cfg' ρ1, ρ1.1.length + encode_nat p), (cfg_to_cfg' ρ1, ρ1.1.length)]),
    enc_osch (prim_step (Λ := con_prob_lang) e1 σ1) ρ1.1.length, ε1,
    enc_X2 X2 ρ1.1.length, r
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    intro y
    unfold enc_X2
    split
    · split
      · exact Hr _
      · exact zero_le
    · exact zero_le
  isplitr
  · ipureintro
    rw [Hlim, Expval_dmap]
    refine le_trans (le_of_eq ?_) Hineq
    congr 2
    funext a
    exact enc_X2_eq _ _ _ _ _ _
  isplitr
  · ipureintro
    rw [Hlim]
    refine ARcoupl_mono _ _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ?_ le_rfl
      (ARcoupl_pgl_dmap _ _ R ε1 Hpgl)
    rintro a b ⟨hR, rfl⟩
    exact ⟨hR, rfl, rfl⟩
  isplitr
  · ipureintro
    rintro x1 x2 l y1 y2 ⟨-, h1, h2⟩ ⟨-, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    subst h1 h3
    rw [h2] at h4
    refine ⟨encode_nat_inj ?_, rfl⟩
    have := congrArg (fun l : full_info_state => (l.head?.map Prod.snd)) h4
    simpa using this
  iintro %e2 %σ2 %efs %l %ρ2 %HS
  obtain ⟨hR, h1, h2⟩ := HS
  dsimp only at h1 h2
  subst h1 h2
  rw [enc_X2_eq]
  iapply H $$ %e2 %σ2 %efs %hR

/-- Rocq: `prog_coupl_step_l_dret`. -/
theorem prog_coupl_step_l_dret (ε1 ε2 ε : ℝ≥0∞) (R : expr × state × List expr → Prop)
    (e1 : expr) (σ1 : state) (ρ1 : CPState)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (Heq : ε = ε1 + ε2)
    (Hred : reducible (Λ := con_prob_lang) e1 σ1)
    (Hpgl : pgl (prim_step (Λ := con_prob_lang) e1 σ1) R ε1) :
    (∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs ρ1 ε2) ⊢ prog_coupl e1 σ1 ρ1 ε Z := by
  refine prog_coupl_step_l_dret_adv ε ε1 (fun _ => ε2) R e1 σ1 ρ1 Z ?_ Hred
    ⟨ε2, fun _ => le_rfl⟩ Hpgl
  rw [Expval_const, prim_step_mass _ _ Hred, mul_one, Heq]

/-- Rocq: `prog_coupl_step_l`. -/
theorem prog_coupl_step_l (e1 : expr) (σ1 : state) (ρ1 : CPState) (ε : ℝ≥0∞)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF)
    (Hred : reducible (Λ := con_prob_lang) e1 σ1) :
    (∀ e2 σ2 efs, ⌜0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)⌝ ={∅}=∗
      Z e2 σ2 efs ρ1 ε) ⊢ prog_coupl e1 σ1 ρ1 ε Z := by
  iintro H
  iapply prog_coupl_step_l_dret 0 ε ε _ e1 σ1 ρ1 Z (zero_add ε).symm Hred
    (pgl_pos_R _ _ _ (pgl_trivial _ 0))
  iintro %e2 %σ2 %efs %⟨-, Hpos⟩
  iapply H $$ %e2 %σ2 %efs %Hpos

/-! ### Non-expansiveness (the Rocq proofs use `f_equiv` inline) -/

/-- Helper: `spec_coupl` is non-expansive in its continuation. -/
theorem spec_coupl_ne {n : ℕ} {σ : state} {ρ : CPState} {ε : ℝ≥0∞}
    {Z1 Z2 : state → CPState → ℝ≥0∞ → IProp GF}
    (HZ : ∀ σ ρ ε, Z1 σ ρ ε ≡{n}≡ Z2 σ ρ ε) :
    spec_coupl σ ρ ε Z1 ≡{n}≡ spec_coupl σ ρ ε Z2 := by
  unfold spec_coupl spec_coupl'
  refine least_fixpoint_ne_outer (fun _ x => ?_) .rfl
  exact or_ne.ne .rfl (or_ne.ne (HZ x.1 x.2.1 x.2.2) .rfl)

/-- Helper: `prog_coupl` is non-expansive in its continuation. -/
theorem prog_coupl_ne {n : ℕ} {e1 : expr} {σ1 : state} {ρ1 : CPState} {ε : ℝ≥0∞}
    {Z1 Z2 : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF}
    (HZ : ∀ e2 σ2 efs ρ2 ε', Z1 e2 σ2 efs ρ2 ε' ≡{n}≡ Z2 e2 σ2 efs ρ2 ε') :
    prog_coupl e1 σ1 ρ1 ε Z1 ≡{n}≡ prog_coupl e1 σ1 ρ1 ε Z2 := by
  refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => exists_ne fun _ =>
    exists_ne fun _ => ?_
  refine sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl <|
    sep_ne.ne .rfl ?_
  exact forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ =>
    forall_ne fun _ => wand_ne.ne .rfl (BIFUpdate.ne.ne (HZ _ _ _ _ _))

end modalities

/-! ## The weakest precondition -/

section wp_def

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]

/-- Rocq: `wp_pre`. -/
abbrev wp_pre (wp : CoPset → expr → (val → IProp GF) → IProp GF) :
    CoPset → expr → (val → IProp GF) → IProp GF := fun E e1 Φ => iprop(
  ∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞),
    state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
    spec_coupl σ1 ρ1 ε1 fun σ2 ρ2 ε2 =>
      match to_val e1 with
      | some v => iprop(|={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ Φ v)
      | none => prog_coupl e1 σ2 ρ2 ε2 fun e3 σ3 efs ρ3 ε3 => iprop(
          ▷ spec_coupl σ3 ρ3 ε3 fun σ4 ρ4 ε4 => iprop(
            |={∅, E}=> state_interp σ4 ∗ spec_interp ρ4 ∗ err_interp ε4 ∗ wp E e3 Φ ∗
              [∗list] ef ∈ efs, wp ⊤ ef (fork_post (Λ := con_prob_lang)))))

/-- Helper: the common core of `wp_pre_contractive`, `wp_ne` and `wp_contractive`. -/
theorem wp_pre_dist {n : ℕ} {wp wp' : CoPset → expr → (val → IProp GF) → IProp GF}
    {E : CoPset} {e : expr} {Φ Ψ : val → IProp GF}
    (HΦ : ∀ v, to_val e = some v → Φ v ≡{n}≡ Ψ v)
    (Hwp : ∀ m, m < n → ∀ e3, wp E e3 Φ ≡{m}≡ wp' E e3 Ψ)
    (Hfork : ∀ m, m < n → ∀ ef, wp ⊤ ef (fork_post (Λ := con_prob_lang)) ≡{m}≡
      wp' ⊤ ef (fork_post (Λ := con_prob_lang))) :
    wp_pre wp E e Φ ≡{n}≡ wp_pre wp' E e Ψ := by
  refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
  refine wand_ne.ne .rfl (BIFUpdate.ne.ne ?_)
  refine spec_coupl_ne fun _ _ _ => ?_
  cases htv : to_val e with
  | some v =>
    exact BIFUpdate.ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl (HΦ v htv)
  | none =>
    refine prog_coupl_ne fun e3 _ _ _ _ => ?_
    refine Contractive.distLater_dist fun m Hm => ?_
    refine spec_coupl_ne fun _ _ _ => ?_
    exact BIFUpdate.ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl <|
      sep_ne.ne (Hwp m Hm e3) (BI.BigSepL.bigSepL_dist fun _ => Hfork m Hm _)

/-- Rocq: `wp_pre_contractive`. -/
instance wp_pre_contractive : Contractive (wp_pre (GF := GF)) where
  distLater_dist Hwp E _ Φ :=
    wp_pre_dist (fun _ _ => .rfl) (fun m Hm e3 => Hwp m Hm E e3 Φ)
      (fun m Hm ef => Hwp m Hm ⊤ ef _)

/-- Rocq: `wp'` (the `Wp` instance of Foxtrot). As in Rocq, the stuckness parameter is
ignored; we use iris-lean's `Stuckness` (rather than Rocq's `()`) so that the `WP` notation of
iris-lean, which fills in `Stuckness.NotStuck`, can be used. -/
instance wp' : Wp (IProp GF) expr val Stuckness where
  wp _ := fixpoint wp_pre

end wp_def

section wp

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]
variable {s : Stuckness} {E : CoPset} {e : expr} {v : val} {Φ Ψ : val → IProp GF}

/-- Rocq: `wp_unfold`. -/
theorem wp_unfold (s : Stuckness) (E : CoPset) (e : expr) (Φ : val → IProp GF) :
    WP e @ s; E {{ Φ }} = wp_pre (Wp.wp (PROP := IProp GF) s) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold (wp_pre (GF := GF)).toContractiveHom) E) e) Φ

/-- Helper (not in Rocq): the Foxtrot WP ignores its stuckness parameter. -/
theorem wp_stuckness_irrel (s : Stuckness) (E : CoPset) (e : expr) (Φ : val → IProp GF) :
    WP e @ s; E {{ Φ }} = WP e @ E {{ Φ }} := rfl

/-- Helper (not in Rocq): `wp_unfold` specialised to a non-value (Rocq:
`rewrite wp_unfold /wp_pre /= Heq`). -/
theorem wp_unfold_none {s : Stuckness} {E : CoPset} {e : expr} {Φ : val → IProp GF}
    (h : to_val e = none) :
    WP e @ s; E {{ Φ }} ⊢ ∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞),
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 fun σ2 ρ2 ε2 =>
        prog_coupl e σ2 ρ2 ε2 fun e3 σ3 efs ρ3 ε3 => iprop(
          ▷ spec_coupl σ3 ρ3 ε3 fun σ4 ρ4 ε4 => iprop(
            |={∅, E}=> state_interp σ4 ∗ spec_interp ρ4 ∗ err_interp ε4 ∗
              WP e3 @ s; E {{ Φ }} ∗
              [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})) := by
  rw [wp_unfold]
  simp only [wp_pre, h]
  exact .rfl

/-- Rocq: `wp_ne`. -/
instance wp_ne : NonExpansive (Wp.wp (PROP := IProp GF) (Expr := expr) s E e) where
  ne {n} := by
    induction n using Nat.strongRecOn generalizing E e with | ind n IH =>
    intro Φ Ψ HΦ
    rw [wp_unfold s E e Φ, wp_unfold s E e Ψ]
    exact wp_pre_dist (fun v _ => HΦ v) (fun m Hm e3 => IH m Hm (OFE.dist_lt HΦ Hm))
      (fun _ _ _ => .rfl)

/-- Rocq: `wp_contractive`. -/
theorem wp_contractive (h : to_val e = none) :
    Contractive (Wp.wp (PROP := IProp GF) (Expr := expr) s E e) where
  distLater_dist {_ Φ Ψ} HΦ := by
    rw [wp_unfold s E e Φ, wp_unfold s E e Ψ]
    exact wp_pre_dist (fun v hv => by simp [h] at hv)
      (fun m Hm _ => NonExpansive.ne (HΦ m Hm)) (fun _ _ _ => .rfl)

/-- Rocq: `wp_value_fupd'`. -/
theorem wp_value_fupd' : (|={E}=> Φ v) ⊢ WP (Val v) @ s; E {{ Φ }} := by
  rw [wp_unfold]
  simp only [wp_pre, to_val_Val]
  iintro H %σ1 %ρ1 %ε1 ⟨Hσ, Hρ, Hε⟩
  imod H
  imod fupd_mask_subseteq (E1 := E) LawfulSet.empty_subset with Hclose
  imodintro
  iapply spec_coupl_ret
  imod Hclose
  imodintro
  iframe

/-- Rocq: `wp_strong_mono`. -/
theorem wp_strong_mono {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    ⊢ WP e @ s; E1 {{ Φ }} -∗
      (∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞) (v : val),
        state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ∗ Φ v ={E2, ∅}=∗
        spec_coupl σ1 ρ1 ε1 fun σ2 ρ2 ε2 => iprop(
          |={∅, E2}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ Ψ v)) -∗
      WP e @ s; E2 {{ Ψ }} := by
  -- `iloeb` would otherwise try to generalize the (auxiliary) recursive declaration.
  clear wp_strong_mono
  iloeb as IH generalizing %e %E1 %E2 %HE %Φ %Ψ
  rw [wp_unfold s E1 e Φ, wp_unfold s E2 e Ψ]
  iintro H HΦ %σ1 %ρ1 %ε Hσε
  ispecialize H $$ %σ1 %ρ1 %ε Hσε
  imod fupd_mask_subseteq HE with Hclose
  imod H
  imodintro
  iapply spec_coupl_bind $$ [-H] H
  iintro %σ2 %ρ2 %ε2 H
  cases hv : to_val e with
  | some v =>
    iapply fupd_spec_coupl
    imod H with ⟨Hσ, Hρ, Hε, HΦv⟩
    imod Hclose
    imod HΦ $$ %σ2 %ρ2 %ε2 %v [Hσ Hρ Hε HΦv] with H
    · iframe
    imodintro
    iexact H
  | none =>
    iapply spec_coupl_ret
    iapply prog_coupl_mono $$ [-H] H
    iintro %e3 %σ3 %efs %ρ3 %ε3 H !>
    iapply spec_coupl_mono $$ [-H] H
    iintro %σ4 %ρ4 %ε4 H
    imod H with ⟨Hσ, Hρ, Hε, Hwp, Hefs⟩
    imod Hclose
    imodintro
    iframe Hσ Hρ Hε Hefs
    iapply IH $$ %e3 %E1 %E2 %HE %Φ %Ψ Hwp HΦ

/-- Rocq: `wp_strong_mono'`. -/
theorem wp_strong_mono' {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    ⊢ WP e @ s; E1 {{ Φ }} -∗
      (∀ (σ : state) (ρ : CPState) (v : val) (ε : ℝ≥0∞),
        state_interp σ ∗ spec_interp ρ ∗ err_interp ε ∗ Φ v ={E2}=∗
        state_interp σ ∗ spec_interp ρ ∗ err_interp ε ∗ Ψ v) -∗
      WP e @ s; E2 {{ Ψ }} := by
  iintro Hwp Hw
  iapply wp_strong_mono HE $$ Hwp
  iintro %σ1 %ρ1 %ε1 %v H
  iapply spec_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >Hclose
  iapply Hw $$ H

/-- Rocq: `spec_coupl_wp`. -/
theorem spec_coupl_wp :
    (∀ (σ1 : state) (ρ1 : CPState) (ε1 : ℝ≥0∞),
      state_interp σ1 ∗ spec_interp ρ1 ∗ err_interp ε1 ={E, ∅}=∗
      spec_coupl σ1 ρ1 ε1 fun σ2 ρ2 ε2 => iprop(
        |={∅, E}=> state_interp σ2 ∗ spec_interp ρ2 ∗ err_interp ε2 ∗ WP e @ s; E {{ Φ }})) ⊢
    WP e @ s; E {{ Φ }} := by
  rw [wp_unfold s E e Φ]
  iintro H %σ1 %ρ1 %ε1 Hσε
  imod H $$ %σ1 %ρ1 %ε1 Hσε with H
  imodintro
  iapply spec_coupl_bind $$ [] H
  iintro %σ2 %ρ2 %ε2 H
  iapply fupd_spec_coupl
  imod H with ⟨Hσ, Hρ, Hε, H⟩
  iapply H $$ %σ2 %ρ2 %ε2
  iframe

/-- Rocq: `fupd_wp`. -/
theorem fupd_wp : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  rw [wp_unfold s E e Φ]
  iintro H %σ1 %ρ1 %ε1 Hσε
  imod H
  iapply H $$ %σ1 %ρ1 %ε1 Hσε

/-- Rocq: `wp_fupd`. -/
theorem wp_fupd : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }} := by
  iintro H
  iapply wp_strong_mono LawfulSet.subset_refl $$ H
  iintro %σ1 %ρ1 %ε1 %v ⟨Hσ, Hρ, Hε, HΦ⟩
  iapply spec_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imod HΦ
  imodintro
  iframe

/-- Rocq: `wp_atomic`. -/
theorem wp_atomic {E1 E2 : CoPset} [Atomic (Λ := con_prob_lang) StronglyAtomic e] :
    (|={E1, E2}=> WP e @ s; E2 {{ v, |={E2, E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }} := by
  rw [wp_unfold s E1 e Φ, wp_unfold s E2 e]
  iintro H %σ1 %ρ1 %ε1 Hσε
  imod H
  imod H $$ %σ1 %ρ1 %ε1 Hσε with H
  imodintro
  iapply spec_coupl_mono $$ [] H
  iintro %σ2 %ρ2 %ε2
  cases hv : to_val e with
  | some v =>
    iintro >⟨Hσ, Hρ, Hε, >HΦ⟩
    imodintro
    iframe
  | none =>
    iintro H
    ihave H := prog_coupl_strengthen _ _ _ _ _ $$ H
    iapply prog_coupl_mono $$ [] H
    iintro %e3 %σ3 %efs %ρ3 %ε3 ⟨%Hstep, H⟩ !>
    obtain ⟨σ', Hstep⟩ := Hstep
    iapply spec_coupl_bind $$ [] H
    iintro %σ4 %ρ4 %ε4 H
    iapply fupd_spec_coupl
    imod H with ⟨Hσ, Hρ, Hε, Hwp, Hefs⟩
    rw [wp_unfold s E2 e3]
    imod Hwp $$ %σ4 %ρ4 %ε4 [Hσ Hρ Hε] with Hwp
    · iframe
    imodintro
    iapply spec_coupl_mono $$ [Hefs] Hwp
    iintro %σ5 %ρ5 %ε5
    cases hv3 : to_val e3 with
    | some v =>
      obtain rfl : e3 = Val v := (ConProbLang.of_to_val (Λ := con_prob_lang) e3 v hv3).symm
      iintro >⟨Hσ, Hρ, Hε, >HΦ⟩
      imodintro
      iframe Hσ Hρ Hε Hefs
      iapply wp_value_fupd'
      imodintro
      iexact HΦ
    | none =>
      iintro H
      ihave %Hr := prog_coupl_reducible _ _ _ _ _ $$ H
      obtain ⟨ρ, Hr⟩ := Hr
      obtain ⟨v, hv⟩ := Atomic.atomic (Λ := con_prob_lang) (a := .StronglyAtomic) σ' e3 σ3 efs
        Hstep
      exact absurd (hv3.symm.trans hv) (Option.some_ne_none v).symm

/-- Rocq: `wp_step_fupd`. -/
theorem wp_step_fupd {E1 E2 : CoPset} {P : IProp GF} (h : to_val e = none) (HE : E2 ⊆ E1) :
    ⊢ (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }} := by
  rw [wp_unfold s E1 e Φ, wp_unfold s E2 e]
  simp only [wp_pre, h]
  iintro HR H %σ1 %ρ1 %ε1 Hσε
  imod HR
  imod H $$ %σ1 %ρ1 %ε1 Hσε with H
  imodintro
  iapply spec_coupl_mono $$ [HR] H
  iintro %σ2 %ρ2 %ε2 H
  iapply prog_coupl_mono $$ [HR] H
  iintro %e3 %σ3 %efs %ρ3 %ε3 H !>
  iapply spec_coupl_mono $$ [HR] H
  iintro %σ4 %ρ4 %ε4 >⟨Hσ, Hρ, Hε, Hwp, Hefs⟩
  imod HR
  imodintro
  iframe Hσ Hρ Hε Hefs
  iapply wp_strong_mono HE $$ Hwp
  iintro %σ %ρ %ε %v ⟨Hσ, Hρ, Hε, HK⟩
  iapply spec_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imod HK $$ HR
  imodintro
  iframe

/-- Rocq: `wp_bind`. -/
theorem wp_bind (K : expr → expr) [ConLanguageCtx (Λ := con_prob_lang) K] :
    WP e @ s; E {{ v, WP (K (Val v)) @ s; E {{ Φ }} }} ⊢ WP (K e) @ s; E {{ Φ }} := by
  iintro H
  -- `iloeb` would otherwise try to generalize the (auxiliary) recursive declaration.
  clear wp_bind
  iloeb as IH generalizing %E %e %Φ
  rw [wp_unfold s E e, wp_unfold s E (K e) Φ]
  iintro %σ1 %ρ1 %ε1 Hσε
  imod H $$ %σ1 %ρ1 %ε1 Hσε with H
  imodintro
  iapply spec_coupl_bind $$ [] H
  iintro %σ2 %ρ2 %ε2 H
  cases hv : to_val e with
  | some v =>
    obtain rfl : e = Val v := (ConProbLang.of_to_val (Λ := con_prob_lang) e v hv).symm
    iapply fupd_spec_coupl
    imod H with ⟨Hσ, Hρ, Hε, H⟩
    beta_reduce
    rw [wp_unfold s E (K (Val v)) Φ]
    iapply H $$ %σ2 %ρ2 %ε2
    iframe
  | none =>
    have hK : to_val (K e) = none := fill_not_val (Λ := con_prob_lang) e hv
    iapply spec_coupl_ret
    rw [hK]
    iapply prog_coupl_ctx_bind K e σ2 ρ2 _ ε2 hv
    iapply prog_coupl_mono $$ [] H
    iintro %e3 %σ3 %efs %ρ3 %ε3 H !>
    iapply spec_coupl_mono $$ [] H
    iintro %σ4 %ρ4 %ε4 >⟨Hσ, Hρ, Hε, H, Hefs⟩
    imodintro
    iframe Hσ Hρ Hε Hefs
    iapply IH $$ %E %e3 %Φ H

/-! ### Derived rules -/

/-- Rocq: `wp_mono`. -/
theorem wp_mono (HΦ : ∀ v, Φ v ⊢ Ψ v) : WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }} := by
  iintro H
  iapply wp_strong_mono' LawfulSet.subset_refl $$ H
  iintro %σ1 %ρ1 %v %ε1 ⟨Hσ, Hρ, Hε, HΦv⟩
  imodintro
  iframe Hσ Hρ Hε
  iapply HΦ v $$ HΦv

/-- Rocq: `wp_mask_mono`. -/
theorem wp_mask_mono {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }} := by
  iintro H
  iapply wp_strong_mono' HE $$ H
  iintro %σ1 %ρ1 %v %ε1 H
  imodintro
  iexact H

/-- Rocq: `wp_value_fupd`. -/
theorem wp_value_fupd [IntoVal (Λ := con_prob_lang) e v] :
    (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }} := by
  obtain rfl : Val v = e := IntoVal.into_val (Λ := con_prob_lang)
  exact wp_value_fupd'

/-- Rocq: `wp_value'`. -/
theorem wp_value' : Φ v ⊢ WP (Val v) @ s; E {{ Φ }} :=
  fupd_intro.trans wp_value_fupd'

/-- Rocq: `wp_value`. -/
theorem wp_value [IntoVal (Λ := con_prob_lang) e v] : Φ v ⊢ WP e @ s; E {{ Φ }} :=
  fupd_intro.trans wp_value_fupd

/-- Rocq: `wp_frame_l`. -/
theorem wp_frame_l {R : IProp GF} : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, H⟩
  iapply wp_strong_mono LawfulSet.subset_refl $$ H
  iintro %σ1 %ρ1 %ε1 %v ⟨Hσ, Hρ, Hε, HΦ⟩
  iapply spec_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imodintro
  iframe

/-- Rocq: `wp_frame_r`. -/
theorem wp_frame_r {R : IProp GF} : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }} := by
  iintro ⟨H, HR⟩
  iapply wp_strong_mono' LawfulSet.subset_refl $$ H
  iintro %σ1 %ρ1 %v %ε1 ⟨Hσ, Hρ, Hε, HΦ⟩
  imodintro
  iframe

/-- Rocq: `wp_frame_step_l`. -/
theorem wp_frame_step_l {E1 E2 : CoPset} {R : IProp GF} (h : to_val e = none)
    (HE : E2 ⊆ E1) :
    (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }} := by
  iintro ⟨Hu, Hwp⟩
  iapply wp_step_fupd h HE $$ Hu
  iapply wp_mono (fun _ => by iintro HΦ HR !>; iframe) $$ Hwp

/-- Rocq: `wp_frame_step_r`. -/
theorem wp_frame_step_r {E1 E2 : CoPset} {R : IProp GF} (h : to_val e = none)
    (HE : E2 ⊆ E1) :
    WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }} :=
  sep_comm.1.trans <| (wp_frame_step_l h HE).trans <| wp_mono fun _ => sep_comm.1

/-- Rocq: `wp_frame_step_l'`. -/
theorem wp_frame_step_l' {R : IProp GF} (h : to_val e = none) :
    ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, Hwp⟩
  iapply wp_frame_step_l h LawfulSet.subset_refl
  iframe Hwp
  iintro !> !> !>
  iexact HR

/-- Rocq: `wp_frame_step_r'`. -/
theorem wp_frame_step_r' {R : IProp GF} (h : to_val e = none) :
    WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }} :=
  sep_comm.1.trans <| (wp_frame_step_l' h).trans <| wp_mono fun _ => sep_comm.1

/-- Rocq: `wp_wand`. -/
theorem wp_wand :
    ⊢ WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }} := by
  iintro Hwp H
  iapply wp_strong_mono' LawfulSet.subset_refl $$ Hwp
  iintro %σ1 %ρ1 %v %ε1 ⟨Hσ, Hρ, Hε, HΦ⟩
  imodintro
  iframe Hσ Hρ Hε
  iapply H $$ HΦ

/-- Rocq: `wp_wand_l`. -/
theorem wp_wand_l : (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }} := by
  iintro ⟨H, Hwp⟩
  iapply wp_wand $$ Hwp H

/-- Rocq: `wp_wand_r`. -/
theorem wp_wand_r : WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }} := by
  iintro ⟨Hwp, H⟩
  iapply wp_wand $$ Hwp H

/-- Rocq: `wp_frame_wand`. -/
theorem wp_frame_wand {R : IProp GF} :
    ⊢ R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }} := by
  iintro HR Hwp
  iapply wp_wand $$ Hwp
  iintro %v HΦ
  iapply HΦ $$ HR

end wp

/-! ## Proofmode class instances -/

section proofmode_classes

variable {GF : BundledGFunctors} [foxtrotWpGS con_prob_lang GF]
variable {s : Stuckness} {E : CoPset} {e : expr} {Φ Ψ : val → IProp GF} {P R : IProp GF}

/-- Rocq: `frame_wp`. -/
instance frame_wp {p : Bool} [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) where
  frame := wp_frame_l.trans <|
    wp_mono fun v => (H v).frame_instantiatiate_exist_disabled.frame

/-- Rocq: `is_except_0_wp`. -/
instance is_except_0_wp : IsExcept0 (WP e @ s; E {{ Φ }}) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_wp)

/-- Rocq: `elim_modal_fupd_wp`. (Higher priority than `elim_modal_fupd_wp_atomic`.) -/
instance (priority := default + 10) elim_modal_fupd_wp {p : Bool} {io : InOut} :
    ElimModal True p io false iprop(|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases intuitionisticallyIf_elim $$ H with H
    iapply fupd_wp
    imod H
    imodintro
    iapply G $$ H

/-- Rocq: `elim_modal_bupd_wp`. -/
instance elim_modal_bupd_wp {p : Bool} {io : InOut} :
    ElimModal True p io false iprop(|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}) where
  elim_modal := by
    rintro ⟨⟩
    refine sep_mono (intuitionisticallyIf_mono (BIUpdateFUpdate.fupd_of_bupd (E := E))) .rfl
      |>.trans ?_
    exact (elim_modal_fupd_wp (io := io)).elim_modal ⟨⟩

/-- Rocq: `elim_modal_fupd_wp_atomic`. -/
instance elim_modal_fupd_wp_atomic {p : Bool} {io : InOut} {E1 E2 : CoPset} :
    ElimModal (Atomic (Λ := con_prob_lang) StronglyAtomic e) p io false iprop(|={E1, E2}=> P) P
      (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2, E1}=> Φ v }}) where
  elim_modal := by
    rintro _
    iintro ⟨H, G⟩
    icases intuitionisticallyIf_elim $$ H with H
    iapply wp_atomic
    imod H
    imodintro
    iapply G $$ H

/-- Rocq: `add_modal_fupd_wp`. -/
instance add_modal_fupd_wp : AddModal iprop(|={E}=> P) P (WP e @ s; E {{ Φ }}) where
  add_modal := by
    iintro ⟨H1, H2⟩
    imod H1
    iapply H2 $$ H1

/-- Rocq: `elim_acc_wp_atomic`. -/
instance (priority := low) elim_acc_wp_atomic {X : Type} {E1 E2 : CoPset}
    {α β : X → IProp GF} {γ : X → Option (IProp GF)} :
    ElimAcc (Atomic (Λ := con_prob_lang) StronglyAtomic e) (fupd E1 E2) (fupd E2 E1) α β γ
      (WP e @ s; E1 {{ Φ }})
      (fun x => WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %atomic Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

/-- Rocq: `elim_acc_wp_nonatomic`. -/
instance elim_acc_wp_nonatomic {X : Type} {α β : X → IProp GF}
    {γ : X → Option (IProp GF)} :
    ElimAcc True (fupd E E) (fupd E E) α β γ (WP e @ s; E {{ Φ }})
      (fun x => WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_fupd
    iapply wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

/- Sanity checks for the proof-mode instances. -/
example (P : IProp GF) : (|={E}=> P) ∗ (P -∗ WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example (P : IProp GF) : (|==> P) ∗ (P -∗ WP e {{ Φ }}) ⊢ WP e {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example [Atomic (Λ := con_prob_lang) StronglyAtomic e] {E1 E2 : CoPset} (P : IProp GF) :
    (|={E1, E2}=> P) ∗ (P -∗ WP e @ E2 {{ v, |={E2, E1}=> Φ v }}) ⊢ WP e @ E1 {{ Φ }} := by
  iintro ⟨HP, H⟩
  imod HP
  iapply H $$ HP

example (P : IProp GF) : P ∗ WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, P ∗ Φ v }} := by
  iintro ⟨HP, H⟩
  iframe HP
  iexact H

end proofmode_classes

end Foxtrot
