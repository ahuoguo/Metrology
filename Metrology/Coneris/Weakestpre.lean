module

public import Metrology.ConProbLang.Erasure
public import Metrology.Prob.GradedPredicateLifting
public import Metrology.Iris.Fixpoint
public import Iris.BI.Lib.Fixpoint
public import Iris.BI.WeakestPre
public import Iris.ProofMode
public import Iris.Instances.Lib.FUpd

/-!
# The weakest precondition of Coneris

Ported from clutch/theories/coneris/weakestpre.v

Coneris is a concurrent probabilistic separation logic with error credits. As in Rocq, the WP
is specialised to `con_prob_lang`, since it allows big "state steps" that are scheduler-erasable
for tape-oblivious schedulers (a class of schedulers specific to the language).

* `conerisWpGS Λ GF` bundles the invariant ghost state (`InvGS_gen .hasNoLC GF`, i.e. no later
  credits, Rocq: `invGS_gen HasNoLc Σ`), the state interpretation `state_interp`, the
  postcondition of forked threads `fork_post` and the error interpretation `err_interp`.
* `state_step_coupl σ ε Z` is the least fixpoint (`bi_least_fixpoint`) of
  `state_step_coupl_pre Z`: either the error is `≥ 1`, or `Z σ ε` holds, or the error can be
  amplified, or a scheduler-erasable state distribution is coupled with an expected-error
  continuation.
* `prog_coupl e σ ε Z` performs one program step of `e` with an expected-error continuation.
* `pgl_wp_pre` is the WP pre-functor; it is contractive (`wp_pre_contractive`) and the WP is its
  guarded fixpoint (`fixpoint`), exposed through iris-lean's `Wp` class (`pgl_wp'`), so that the
  `WP e @ s; E {{ Φ }}` / `WP e @ E {{ v, Q }}` / `WP e {{ Φ }}` notations of iris-lean apply.

## Design choices (Rocq → Lean)

* **Wp class / stuckness** (`clutch/theories/bi/weakestpre.v`): we reuse iris-lean's
  `Iris.Wp` class and `WP` notation rather than porting clutch's notation file (which only
  declares the `Wp`/`Twp` classes and the `WP`/Texan-triple notations). Rocq instantiates
  `Wp (iProp Σ) expr val ()` to avoid stuckness; here the index type is iris-lean's `Stuckness`
  (so that iris-lean's notation, which fills in `Stuckness.NotStuck`, typechecks), and the
  stuckness argument is ignored by the instance. All lemmas are stated for an arbitrary
  `s : Stuckness`, like the Rocq lemmas are for an arbitrary `s : ()`.
* Errors are `ℝ≥0∞` (Rocq: `nonnegreal`); summability and nonnegativity side conditions
  vanish. The boundedness conditions `⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝` are kept for fidelity with the Rocq
  statements (and Foxtrot), but with `r : ℝ≥0∞` they are trivially satisfiable (`r = ⊤`); the
  proofs that in Rocq pick `Rmax r 1` pick `⊤` here.
* `bool_decide P` in continuations is a (classical) `if P then .. else ..`; `SeriesC (λ ρ, μ ρ * f ρ)`
  is `Expval μ f` (which is its definition).
* `sch_erasable` is universe polymorphic in the scheduler state; the WP fixes it to `Type`
  (`tape_oblivious_sch`, the Rocq `λ t _ _ sch, TapeOblivious t sch`).
* Rocq `α ∈ get_active σ1` uses the concrete `get_active` of `con_prob_lang` (`σ.tapes.keys`).
* The `state × ℝ≥0∞` argument of `state_step_coupl'` carries the discrete COFE
  (Rocq: `prodO stateO NNRO`, with the canonical `NNRO := leibnizO nonnegreal`).
* `state_step_coupl_pre`, `prog_coupl` and `pgl_wp_pre` are `abbrev`s so that the proof mode
  can destruct them; `state_step_coupl'`/`state_step_coupl` are `def`s (unfold with
  `state_step_coupl_unfold`), and the WP itself is (iris-lean's opaque) `fixpoint`
  (unfold with `pgl_wp_unfold`, an equation).
* `Class conerisWpGS` takes `Λ` as an `outParam`, so that `state_interp σ`/`err_interp ε`
  elaborate without mentioning `Λ`; `fork_post` needs `(Λ := con_prob_lang)` when its
  argument type is not otherwise determined.
* `pgl_wp_strong_mono`, `pgl_wp_step_fupd`, `pgl_wp_wand`, `pgl_wp_strong_mono'`,
  `pgl_wp_frame_wand` are stated as `⊢ A -∗ B -∗ C` (as the Rocq `A -∗ B -∗ C`); the others as
  entailments. Instance arguments (`Atomic`, `IntoVal`, `ConLanguageCtx`) are instance-implicit.
* `ElimModal`/`AddModal`/`ElimAcc`/`Frame`/`IsExcept0` instances follow iris-lean's
  `ProgramLogic/WeakestPre.lean` (e.g. `Frame` uses `FrameInstantiateExistDisabled`, the
  `ElimModal` instances carry the `InOut` parameter, Rocq's cost `| 100` is `priority := low`).
  Exception: `elim_modal_fupd_pgl_wp_atomic` has default priority (as iris-lean's
  `elimModalFupdWpAtomic`; `elim_modal_fupd_pgl_wp` has `default + 10` and is still tried first),
  since at low priority a generic `IntoExcept0`-based instance is tried first and aborts when
  the eliminated proposition is a bound variable (e.g. `imod` on an atomic update under a WP).

## Omitted
* `Global Opaque conerisWpGS_invGS`, `Global Arguments`, `Hint Resolve cond_nonneg`,
  `Canonical Structure NNRO` (replaced by the discrete COFE instance on `state × ℝ≥0∞`).
* Sealing: `pgl_wp_def`, `pgl_wp_aux`, `pgl_wp_unseal` (iris-lean's `fixpoint` is opaque).
* `Proper` plumbing: `pgl_wp_proper` (follows from `pgl_wp_ne`), `pgl_wp_mono'`,
  `pgl_wp_flip_mono'` (use `pgl_wp_mono`).
* Nothing from `clutch/theories/bi/weakestpre.v` is ported (see above); in particular its
  Texan-triple notations are iris-lean's.

## Added helpers (not in Rocq)
`Expval_ite_of_support`, `Expval_ite_pgl` (generic `Distr` facts; belong in `Prob`),
`partial_inv_fun` (Rocq `prelude/classical.v`, as a function) with `partial_inv_fun_some`,
`partial_inv_fun_inj`, `tape_oblivious_sch`, `state_step_coupl_ne`, `prog_coupl_ne`,
`pgl_wp_pre_dist` (the Rocq `f_equiv` proofs of contractivity/non-expansiveness),
`pgl_wp_stuckness_irrel` (the WP ignores its stuckness), `pgl_wp_unfold_none` (`pgl_wp_unfold`
for a non-value, used by `Adequacy`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

/-! ## Local helpers (not in the Rocq file) -/

section helpers

variable {α : Type*} [Countable α]

/-- Helper: modifying the integrand outside the support does not change the expectation. -/
theorem Expval_ite_of_support (μ : Distr α) (P : α → Prop) [DecidablePred P] (f : α → ℝ≥0∞)
    (c : ℝ≥0∞) (hP : ∀ a, 0 < μ a → P a) :
    Expval μ (fun a => if P a then f a else c) = Expval μ f := by
  unfold Expval
  congr 1
  funext a
  dsimp only
  split_ifs with h
  · rfl
  · have : μ a = 0 := by
      by_contra hne
      exact h (hP a (pos_iff_ne_zero.2 hne))
    simp [this]

/-- Helper: replacing the integrand by `1` outside of `R` costs at most the `pgl` error. -/
theorem Expval_ite_pgl (μ : Distr α) (R : α → Prop) [DecidablePred R] (f : α → ℝ≥0∞)
    (ε1 : ℝ≥0∞) (h : pgl μ R ε1) :
    Expval μ (fun a => if R a then f a else 1) ≤ ε1 + Expval μ f := by
  rw [pgl_unfold] at h
  calc Expval μ (fun a => if R a then f a else 1)
      ≤ Expval μ (fun a => (if R a then 0 else 1) + f a) :=
        Expval_le _ _ _ fun a => by split_ifs <;> simp
    _ = Expval μ (fun a => if R a then 0 else 1) + Expval μ f := Expval_plus _ _ _
    _ ≤ ε1 + Expval μ f := by
        refine add_le_add (le_trans (le_of_eq ?_) h) le_rfl
        unfold Expval prob
        congr 1
        funext a
        by_cases hR : R a <;> simp [hR]

open Classical in
/-- Rocq (`prelude/classical.v`): `partial_inv_fun`, a classical partial inverse. -/
def partial_inv_fun {A B : Type*} (f : A → B) (b : B) : Option A :=
  if h : ∃ a, f a = b then some h.choose else none

theorem partial_inv_fun_some {A B : Type*} {f : A → B} {b : B} {a : A}
    (h : partial_inv_fun f b = some a) : f a = b := by
  unfold partial_inv_fun at h
  split_ifs at h with hb
  cases h
  exact hb.choose_spec

theorem partial_inv_fun_inj {A B : Type*} {f : A → B} (hf : Function.Injective f) (a : A) :
    partial_inv_fun f (f a) = some a := by
  unfold partial_inv_fun
  split_ifs with hb
  · rw [hf hb.choose_spec]
  · exact absurd ⟨a, rfl⟩ hb

end helpers

/-! ## The ghost-state class -/

/-- Rocq: `conerisWpGS`. -/
class conerisWpGS (Λ : outParam conLanguage) (GF : BundledGFunctors) where
  [conerisWpGS_invGS : InvGS_gen .hasNoLC GF]
  state_interp : Λ.state → IProp GF
  fork_post : Λ.val → IProp GF
  err_interp : ℝ≥0∞ → IProp GF

attribute [reducible, instance] conerisWpGS.conerisWpGS_invGS
export conerisWpGS (state_interp fork_post err_interp)

/-- The discrete OFE on the arguments of `state_step_coupl'` (Rocq: `prodO stateO NNRO`). -/
instance : COFE (state × ℝ≥0∞) := COFE.ofDiscrete _
instance : OFE.Discrete (state × ℝ≥0∞) := ⟨id⟩

/-- The class of schedulers the state steps are erasable for. -/
abbrev tape_oblivious_sch : ∀ (t : Type) [DecidableEq t] [Countable t],
    scheduler (con_lang_mdp con_prob_lang) t → Prop :=
  fun t _ _ sch => TapeOblivious t sch

section modalities

variable {GF : BundledGFunctors} [conerisWpGS con_prob_lang GF]

/-- Rocq: `state_step_coupl_pre`. -/
abbrev state_step_coupl_pre (Z : state → ℝ≥0∞ → IProp GF) (Φ : state × ℝ≥0∞ → IProp GF) :
    state × ℝ≥0∞ → IProp GF := fun x => iprop(
  ⌜1 ≤ x.2⌝ ∨ Z x.1 x.2 ∨ (∀ ε', ⌜x.2 < ε'⌝ -∗ Φ (x.1, ε')) ∨
    ∃ (μ : Distr state) (ε2 : state → ℝ≥0∞),
      ⌜sch_erasable tape_oblivious_sch μ x.1⌝ ∗
      ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
      ⌜Expval μ ε2 ≤ x.2⌝ ∗
      ∀ σ2, |={∅}=> Φ (σ2, ε2 σ2))

/-- Rocq: `state_step_coupl_pre_ne`. -/
instance state_step_coupl_pre_ne (Z : state → ℝ≥0∞ → IProp GF) (Φ : state × ℝ≥0∞ → IProp GF) :
    NonExpansive (state_step_coupl_pre Z Φ) :=
  nonExpansive_of_discrete_leibniz _

/-- Rocq: `state_step_coupl_pre_mono`. -/
instance state_step_coupl_pre_mono (Z : state → ℝ≥0∞ → IProp GF) :
    BIMonoPred (state_step_coupl_pre Z) where
  mono_pred {_ _ _ _} := by
    iintro #Hwand %x H
    icases H with (H | H | H | ⟨%μ, %ε2, %Hμ, %Hr, %Hε, H⟩)
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
      iexists μ, ε2
      isplitr
      · ipureintro
        exact Hμ
      isplitr
      · ipureintro
        exact Hr
      isplitr
      · ipureintro
        exact Hε
      iintro %σ2
      imod H $$ %σ2 with H
      imodintro
      iapply Hwand $$ H
  mono_pred_ne := nonExpansive_of_discrete_leibniz _

/-- Rocq: `state_step_coupl'`. -/
def state_step_coupl' (Z : state → ℝ≥0∞ → IProp GF) : state × ℝ≥0∞ → IProp GF :=
  bi_least_fixpoint (state_step_coupl_pre Z)

/-- Rocq: `state_step_coupl`. -/
def state_step_coupl (σ : state) (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) : IProp GF :=
  state_step_coupl' Z (σ, ε)

/-- Rocq: `state_step_coupl_unfold`. -/
theorem state_step_coupl_unfold (σ1 : state) (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) :
    state_step_coupl σ1 ε Z = iprop(
      ⌜1 ≤ ε⌝ ∨ Z σ1 ε ∨ (∀ ε', ⌜ε < ε'⌝ -∗ state_step_coupl σ1 ε' Z) ∨
        ∃ (μ : Distr state) (ε2 : state → ℝ≥0∞),
          ⌜sch_erasable tape_oblivious_sch μ σ1⌝ ∗
          ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
          ⌜Expval μ ε2 ≤ ε⌝ ∗
          ∀ σ2, |={∅}=> state_step_coupl σ2 (ε2 σ2) Z) := by
  unfold state_step_coupl state_step_coupl'
  rw [least_fixpoint_unfold]

/-- Rocq: `state_step_coupl_ret_err_ge_1`. -/
theorem state_step_coupl_ret_err_ge_1 (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞)
    (h : 1 ≤ ε) : ⊢ state_step_coupl σ1 ε Z := by
  rw [state_step_coupl_unfold]
  ileft
  ipureintro
  exact h

/-- Rocq: `state_step_coupl_ret`. -/
theorem state_step_coupl_ret (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    Z σ1 ε ⊢ state_step_coupl σ1 ε Z := by
  rw [state_step_coupl_unfold]
  iintro H
  iright
  ileft
  iexact H

/-- Rocq: `state_step_coupl_ampl`. -/
theorem state_step_coupl_ampl (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (∀ ε', ⌜ε < ε'⌝ -∗ state_step_coupl σ1 ε' Z) ⊢ state_step_coupl σ1 ε Z := by
  rw [state_step_coupl_unfold σ1 ε]
  iintro H
  iright
  iright
  ileft
  iexact H

/-- Rocq: `state_step_coupl_ampl'`. -/
theorem state_step_coupl_ampl' (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (∀ ε', ⌜ε < ε' ∧ ε' < 1⌝ -∗ state_step_coupl σ1 ε' Z) ⊢ state_step_coupl σ1 ε Z := by
  iintro H
  iapply state_step_coupl_ampl
  iintro %ε' %Hε'
  by_cases h : ε' < 1
  · iapply H
    ipureintro
    exact ⟨Hε', h⟩
  · iapply state_step_coupl_ret_err_ge_1 _ _ _ (not_lt.1 h)

/-- Rocq: `state_step_coupl_rec`. -/
theorem state_step_coupl_rec (σ1 : state) (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) :
    (∃ (μ : Distr state) (ε2 : state → ℝ≥0∞),
      ⌜sch_erasable tape_oblivious_sch μ σ1⌝ ∗
      ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
      ⌜Expval μ ε2 ≤ ε⌝ ∗
      ∀ σ2, |={∅}=> state_step_coupl σ2 (ε2 σ2) Z) ⊢ state_step_coupl σ1 ε Z := by
  rw [state_step_coupl_unfold σ1 ε]
  iintro H
  iright
  iright
  iright
  iexact H

open Classical in
/-- Rocq: `state_step_coupl_rec_equiv`. -/
theorem state_step_coupl_rec_equiv (σ1 : state) (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) :
    (∃ (μ : Distr state) (ε2 : state → ℝ≥0∞),
      ⌜sch_erasable tape_oblivious_sch μ σ1⌝ ∗
      ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
      ⌜Expval μ ε2 ≤ ε⌝ ∗
      ∀ σ2, |={∅}=> state_step_coupl σ2 (ε2 σ2) Z) ⊣⊢
    (∃ (R : state → Prop) (μ : Distr state) (ε1 : ℝ≥0∞) (ε2 : state → ℝ≥0∞),
      ⌜sch_erasable tape_oblivious_sch μ σ1⌝ ∗
      ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
      ⌜ε1 + Expval μ ε2 ≤ ε⌝ ∗
      ⌜pgl μ R ε1⌝ ∗
      ∀ σ2, ⌜R σ2⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) := by
  constructor
  · iintro ⟨%μ, %ε2, %Hμ, %Hr, %Hineq, H⟩
    iexists (fun _ => True), μ, 0, (fun σ => if 0 < μ σ then ε2 σ else 1)
    isplitr
    · ipureintro
      exact Hμ
    isplitr
    · ipureintro
      exact ⟨⊤, fun _ => le_top⟩
    isplitr
    · ipureintro
      rw [zero_add, Expval_ite_of_support μ _ ε2 1 fun _ h => h]
      exact Hineq
    isplitr
    · ipureintro
      exact pgl_trivial μ 0
    iintro %σ2 -
    by_cases h : 0 < μ σ2
    · simp only [ite_eq_left h]
      iapply H $$ %σ2
    · simp only [ite_eq_right h]
      iclear H
      imodintro
      iapply state_step_coupl_ret_err_ge_1 _ _ _ le_rfl
  · iintro ⟨%R, %μ, %ε1, %ε2, %Hμ, %Hr, %Hineq, %Hpgl, H⟩
    iexists μ, (fun σ => if R σ then ε2 σ else 1)
    isplitr
    · ipureintro
      exact Hμ
    isplitr
    · ipureintro
      exact ⟨⊤, fun _ => le_top⟩
    isplitr
    · ipureintro
      exact (Expval_ite_pgl μ R ε2 ε1 Hpgl).trans Hineq
    iintro %σ2
    by_cases h : R σ2
    · simp only [ite_eq_left h]
      iapply H $$ %σ2 %h
    · simp only [ite_eq_right h]
      iclear H
      imodintro
      iapply state_step_coupl_ret_err_ge_1 _ _ _ le_rfl

/-- Rocq: `state_step_coupl_rec'`. -/
theorem state_step_coupl_rec' (σ1 : state) (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) :
    (∃ (R : state → Prop) (μ : Distr state) (ε1 : ℝ≥0∞) (ε2 : state → ℝ≥0∞),
      ⌜sch_erasable tape_oblivious_sch μ σ1⌝ ∗
      ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
      ⌜ε1 + Expval μ ε2 ≤ ε⌝ ∗
      ⌜pgl μ R ε1⌝ ∗
      ∀ σ2, ⌜R σ2⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) ⊢ state_step_coupl σ1 ε Z :=
  (state_step_coupl_rec_equiv σ1 ε Z).2.trans (state_step_coupl_rec σ1 ε Z)

/-- Rocq: `state_step_coupl_ind`. -/
theorem state_step_coupl_ind (Ψ Z : state → ℝ≥0∞ → IProp GF) :
    ⊢ □ (∀ σ ε, state_step_coupl_pre Z
          (fun x => iprop(Ψ x.1 x.2 ∧ state_step_coupl x.1 x.2 Z)) (σ, ε) -∗ Ψ σ ε) -∗
      ∀ σ ε, state_step_coupl σ ε Z -∗ Ψ σ ε := by
  have h : (fun x : state × ℝ≥0∞ => iprop(Ψ x.1 x.2 ∧ state_step_coupl x.1 x.2 Z)) =
      fun x => iprop(Ψ x.1 x.2 ∧ bi_least_fixpoint (state_step_coupl_pre Z) x) := rfl
  rw [h]
  unfold state_step_coupl state_step_coupl'
  iintro #IH %σ %ε H
  iapply least_fixpoint_ind (state_step_coupl_pre Z) (fun x => Ψ x.1 x.2)
    (IN := nonExpansive_of_discrete_leibniz _) $$ [] %(σ, ε) H
  iintro !> %⟨σ', ε'⟩ Hx
  iapply IH $$ %σ' %ε' Hx

/-- Rocq: `fupd_state_step_coupl`. -/
theorem fupd_state_step_coupl (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (|={∅}=> state_step_coupl σ1 ε Z) ⊢ state_step_coupl σ1 ε Z := by
  iintro H
  iapply state_step_coupl_rec'
  iexists (fun x => x = σ1), dret σ1, 0, (fun _ => ε)
  isplitr
  · ipureintro
    exact dret_sch_erasable (Λ := con_prob_lang) σ1 _
  isplitr
  · ipureintro
    exact ⟨ε, fun _ => le_rfl⟩
  isplitr
  · ipureintro
    simp
  isplitr
  · ipureintro
    exact pgl_dret σ1 _ rfl
  iintro %σ2 %Hσ2
  subst Hσ2
  iexact H

/-- Rocq: `state_step_coupl_mono`. -/
theorem state_step_coupl_mono (σ1 : state) (Z1 Z2 : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (∀ σ2 ε', Z1 σ2 ε' -∗ Z2 σ2 ε') ⊢ state_step_coupl σ1 ε Z1 -∗ state_step_coupl σ1 ε Z2 := by
  iintro HZ Hs
  iapply state_step_coupl_ind
    (fun σ ε => iprop((∀ σ2 ε', Z1 σ2 ε' -∗ Z2 σ2 ε') -∗ state_step_coupl σ ε Z2)) Z1
    $$ [] %σ1 %ε Hs HZ
  iintro !> %σ %ε' H Hw
  icases H with (%H | H | H | ⟨%μ, %ε2, %Hμ, %Hr, %Hε, H⟩)
  · iapply state_step_coupl_ret_err_ge_1 _ _ _ H
  · iapply state_step_coupl_ret
    iapply Hw $$ H
  · iapply state_step_coupl_ampl
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨IH, -⟩
    iapply IH $$ Hw
  · iapply state_step_coupl_rec
    iexists μ, ε2
    iframe %
    iintro %σ2
    imod H $$ %σ2 with ⟨IH, -⟩
    imodintro
    iapply IH $$ Hw

/-- Rocq: `state_step_coupl_mono_err`. -/
theorem state_step_coupl_mono_err (ε1 ε2 : ℝ≥0∞) (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF)
    (Heps : ε1 ≤ ε2) : state_step_coupl σ1 ε1 Z ⊢ state_step_coupl σ1 ε2 Z := by
  iintro Hs
  iapply state_step_coupl_rec'
  iexists (fun x => x = σ1), dret σ1, 0, (fun _ => ε1)
  isplitr
  · ipureintro
    exact dret_sch_erasable (Λ := con_prob_lang) σ1 _
  isplitr
  · ipureintro
    exact ⟨ε1, fun _ => le_rfl⟩
  isplitr
  · ipureintro
    simpa using Heps
  isplitr
  · ipureintro
    exact pgl_dret σ1 _ rfl
  iintro %σ2 %Hσ2
  subst Hσ2
  imodintro
  iexact Hs

/-- Rocq: `state_step_coupl_bind`. -/
theorem state_step_coupl_bind (σ1 : state) (Z1 Z2 : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (∀ σ2 ε', Z1 σ2 ε' -∗ state_step_coupl σ2 ε' Z2) ⊢
      state_step_coupl σ1 ε Z1 -∗ state_step_coupl σ1 ε Z2 := by
  iintro HZ Hs
  iapply state_step_coupl_ind
    (fun σ ε => iprop((∀ σ2 ε', Z1 σ2 ε' -∗ state_step_coupl σ2 ε' Z2) -∗
      state_step_coupl σ ε Z2)) Z1
    $$ [] %σ1 %ε Hs HZ
  iintro !> %σ %ε' H HZ
  icases H with (%H | H | H | ⟨%μ, %ε2, %Hμ, %Hr, %Hε, H⟩)
  · iapply state_step_coupl_ret_err_ge_1 _ _ _ H
  · iapply HZ $$ H
  · iapply state_step_coupl_ampl
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨IH, -⟩
    iapply IH $$ HZ
  · iapply state_step_coupl_rec
    iexists μ, ε2
    iframe %
    iintro %σ2
    imod H $$ %σ2 with ⟨IH, -⟩
    imodintro
    iapply IH $$ HZ

/-- Rocq: `state_step_coupl_state_step`. -/
theorem state_step_coupl_state_step (α : Loc) (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF)
    (ε ε' : ℝ≥0∞) (Hin : α ∈ get_active σ1) :
    (∃ (R : state → Prop), ⌜pgl (con_prob_lang.state_step σ1 α) R ε⌝ ∗
      ∀ σ2, ⌜R σ2⌝ ={∅}=∗ state_step_coupl σ2 ε' Z) ⊢ state_step_coupl σ1 (ε + ε') Z := by
  have Hin' : α ∈ σ1.tapes := Std.ExtTreeMap.mem_keys.1 Hin
  iintro ⟨%R, %HR, H⟩
  iapply state_step_coupl_rec'
  iexists R, con_prob_lang.state_step σ1 α, ε, (fun _ => ε')
  isplitr
  · ipureintro
    exact state_step_sch_erasable σ1 α _ (Std.ExtTreeMap.getElem?_eq_some_getElem Hin')
  isplitr
  · ipureintro
    exact ⟨ε', fun _ => le_rfl⟩
  isplitr
  · ipureintro
    rw [Expval_const, state_step_mass σ1 α Hin', mul_one]
  isplitr
  · ipureintro
    exact HR
  iexact H

/-- Rocq: `state_step_coupl_iterM_state_adv_comp`. -/
theorem state_step_coupl_iterM_state_adv_comp (N : ℕ) (α : Loc) (σ1 : state)
    (Z : state → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) (Hin : α ∈ get_active σ1) :
    (∃ (R : state → Prop) (ε1 : ℝ≥0∞) (ε2 : state → ℝ≥0∞),
      ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
      ⌜ε1 + Expval (iterM N (fun σ => con_prob_lang.state_step σ α) σ1) ε2 ≤ ε⌝ ∗
      ⌜pgl (iterM N (fun σ => con_prob_lang.state_step σ α) σ1) R ε1⌝ ∗
      ∀ σ2, ⌜R σ2⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) ⊢ state_step_coupl σ1 ε Z := by
  have Hin' : α ∈ σ1.tapes := Std.ExtTreeMap.mem_keys.1 Hin
  iintro ⟨%R, %ε1, %ε2, %Hr, %Hε, %HR, H⟩
  iapply state_step_coupl_rec'
  iexists R, iterM N (fun σ => con_prob_lang.state_step σ α) σ1, ε1, ε2
  isplitr
  · ipureintro
    exact iterM_state_step_sch_erasable σ1 α _ N (Std.ExtTreeMap.getElem?_eq_some_getElem Hin')
  iframe %
  iexact H

/-- Rocq: `state_step_coupl_state_adv_comp`. -/
theorem state_step_coupl_state_adv_comp (α : Loc) (σ1 : state) (Z : state → ℝ≥0∞ → IProp GF)
    (ε : ℝ≥0∞) (Hin : α ∈ get_active σ1) :
    (∃ (R : state → Prop) (ε1 : ℝ≥0∞) (ε2 : state → ℝ≥0∞),
      ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
      ⌜ε1 + Expval (con_prob_lang.state_step σ1 α) ε2 ≤ ε⌝ ∗
      ⌜pgl (con_prob_lang.state_step σ1 α) R ε1⌝ ∗
      ∀ σ2, ⌜R σ2⌝ ={∅}=∗ state_step_coupl σ2 (ε2 σ2) Z) ⊢ state_step_coupl σ1 ε Z := by
  have h1 : iterM 1 (fun σ => con_prob_lang.state_step σ α) σ1 = con_prob_lang.state_step σ1 α := by
    rw [iterM_Sn]
    exact dret_id_right _
  rw [← h1]
  exact state_step_coupl_iterM_state_adv_comp 1 α σ1 Z ε Hin

/-! ### One step prog coupl -/

/-- Rocq: `prog_coupl`. -/
abbrev prog_coupl (e1 : expr) (σ1 : state) (ε : ℝ≥0∞)
    (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) : IProp GF := iprop(
  ∃ (ε2 : expr × state × List expr → ℝ≥0∞),
    ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
    ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
    ⌜Expval (prim_step (Λ := con_prob_lang) e1 σ1) ε2 ≤ ε⌝ ∗
    ∀ e2 σ2 efs, |={∅}=> Z e2 σ2 efs (ε2 (e2, σ2, efs)))

open Classical in
/-- Rocq: `prog_coupl_equiv1`. -/
theorem prog_coupl_equiv1 (e1 : expr) (σ1 : state) (ε : ℝ≥0∞)
    (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) :
    (∀ e2 σ2 efs, Z e2 σ2 efs 1) ⊢ prog_coupl e1 σ1 ε Z -∗
      ∃ (R : expr × state × List expr → Prop) (ε1 : ℝ≥0∞)
        (ε2 : expr × state × List expr → ℝ≥0∞),
        ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
        ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
        ⌜ε1 + Expval (prim_step (Λ := con_prob_lang) e1 σ1) ε2 ≤ ε⌝ ∗
        ⌜pgl (prim_step (Λ := con_prob_lang) e1 σ1) R ε1⌝ ∗
        ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs (ε2 (e2, σ2, efs)) := by
  iintro H1 ⟨%ε2, %Hred, %Hr, %Hineq, H⟩
  iexists (fun _ => True), 0,
    (fun x => if 0 < prim_step (Λ := con_prob_lang) e1 σ1 x then ε2 x else 1)
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    rw [zero_add, Expval_ite_of_support _ _ ε2 1 fun _ h => h]
    exact Hineq
  isplitr
  · ipureintro
    exact pgl_trivial _ 0
  iintro %e2 %σ2 %efs -
  by_cases h : 0 < prim_step (Λ := con_prob_lang) e1 σ1 (e2, σ2, efs)
  · simp only [ite_eq_left h]
    iapply H $$ %e2 %σ2 %efs
  · simp only [ite_eq_right h]
    imodintro
    iapply H1 $$ %e2 %σ2 %efs

open Classical in
/-- Rocq: `prog_coupl_equiv2`. -/
theorem prog_coupl_equiv2 (e1 : expr) (σ1 : state) (ε : ℝ≥0∞)
    (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) :
    (∀ e2 σ2 efs, Z e2 σ2 efs 1) ⊢
      (∃ (R : expr × state × List expr → Prop) (ε1 : ℝ≥0∞)
        (ε2 : expr × state × List expr → ℝ≥0∞),
        ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
        ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
        ⌜ε1 + Expval (prim_step (Λ := con_prob_lang) e1 σ1) ε2 ≤ ε⌝ ∗
        ⌜pgl (prim_step (Λ := con_prob_lang) e1 σ1) R ε1⌝ ∗
        ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs (ε2 (e2, σ2, efs))) -∗
      prog_coupl e1 σ1 ε Z := by
  iintro H1 ⟨%R, %ε1, %ε2, %Hred, %Hr, %Hineq, %Hpgl, H⟩
  iexists (fun x => if R x then ε2 x else 1)
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    exact (Expval_ite_pgl _ R ε2 ε1 Hpgl).trans Hineq
  iintro %e2 %σ2 %efs
  by_cases h : R (e2, σ2, efs)
  · simp only [ite_eq_left h]
    iapply H $$ %e2 %σ2 %efs %h
  · simp only [ite_eq_right h]
    imodintro
    iapply H1 $$ %e2 %σ2 %efs

/-- Rocq: `prog_coupl_mono_err`. -/
theorem prog_coupl_mono_err (e : expr) (σ : state) (Z : expr → state → List expr → ℝ≥0∞ → IProp GF)
    (ε ε' : ℝ≥0∞) (h : ε ≤ ε') : prog_coupl e σ ε Z ⊢ prog_coupl e σ ε' Z := by
  iintro ⟨%ε2, %Hred, %Hr, %Hineq, H⟩
  iexists ε2
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact Hr
  isplitr
  · ipureintro
    exact Hineq.trans h
  iexact H

open Classical in
/-- Rocq: `prog_coupl_strong_mono`. -/
theorem prog_coupl_strong_mono (e1 : expr) (σ1 : state)
    (Z1 Z2 : expr → state → List expr → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    □ (∀ e2 σ2 efs, Z2 e2 σ2 efs 1) ⊢
      (∀ e2 σ2 ε' efs, ⌜∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ (e2, σ2, efs)⌝ ∗
        Z1 e2 σ2 efs ε' -∗ Z2 e2 σ2 efs ε') -∗
      prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2 := by
  iintro #H1 Hm ⟨%ε2, %Hred, %Hr, %Hineq, Hcnt⟩
  iexists (fun x => if ∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ x then ε2 x else 1)
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    rw [Expval_ite_of_support _ _ ε2 1 fun _ h => ⟨σ1, h⟩]
    exact Hineq
  iintro %e2 %σ2 %efs
  by_cases h : ∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ (e2, σ2, efs)
  · simp only [ite_eq_left h]
    imod Hcnt $$ %e2 %σ2 %efs with Hcnt
    imodintro
    iapply Hm
    iframe Hcnt
    ipureintro
    exact h
  · simp only [ite_eq_right h]
    imodintro
    iapply H1 $$ %e2 %σ2 %efs

/-- Rocq: `prog_coupl_mono`. -/
theorem prog_coupl_mono (e1 : expr) (σ1 : state)
    (Z1 Z2 : expr → state → List expr → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    (∀ e2 σ2 efs ε', Z1 e2 σ2 efs ε' -∗ Z2 e2 σ2 efs ε') ⊢
      prog_coupl e1 σ1 ε Z1 -∗ prog_coupl e1 σ1 ε Z2 := by
  iintro Hm ⟨%ε2, %Hred, %Hr, %Hineq, H⟩
  iexists ε2
  iframe %
  iintro %e2 %σ2 %efs
  imod H $$ %e2 %σ2 %efs with H
  imodintro
  iapply Hm $$ H

open Classical in
/-- Rocq: `prog_coupl_strengthen`. -/
theorem prog_coupl_strengthen (e1 : expr) (σ1 : state)
    (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    □ (∀ e2 σ2 efs, Z e2 σ2 efs 1) ⊢ prog_coupl e1 σ1 ε Z -∗
      prog_coupl e1 σ1 ε (fun e2 σ2 efs ε' => iprop(
        ⌜(∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ (e2, σ2, efs)) ∨ 1 ≤ ε'⌝ ∧
          Z e2 σ2 efs ε')) := by
  iintro #Hmono ⟨%ε2, %Hred, %Hr, %Hineq, Hcnt⟩
  iexists (fun x => if ∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ x then ε2 x else 1)
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    rw [Expval_ite_of_support _ _ ε2 1 fun _ h => ⟨σ1, h⟩]
    exact Hineq
  iintro %e2 %σ2 %efs
  by_cases h : ∃ σ, 0 < prim_step (Λ := con_prob_lang) e1 σ (e2, σ2, efs)
  · simp only [ite_eq_left h]
    imod Hcnt $$ %e2 %σ2 %efs with Hcnt
    imodintro
    isplit
    · ipureintro
      exact Or.inl h
    · iexact Hcnt
  · simp only [ite_eq_right h]
    imodintro
    isplit
    · ipureintro
      exact Or.inr le_rfl
    · iapply Hmono $$ %e2 %σ2 %efs

/-- Rocq: `prog_coupl_ctx_bind`. -/
theorem prog_coupl_ctx_bind (K : expr → expr) [ConLanguageCtx (Λ := con_prob_lang) K]
    (e1 : expr) (σ1 : state) (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞)
    (Hv : to_val e1 = none) :
    □ (∀ e2 σ2 efs, Z e2 σ2 efs 1) ⊢
      prog_coupl e1 σ1 ε (fun e2 σ2 efs ε' => Z (K e2) σ2 efs ε') -∗
      prog_coupl (K e1) σ1 ε Z := by
  iintro #H' ⟨%ε2, %Hred, %Hr, %Hineq, H⟩
  -- The (classical) inverse of the context `K`.
  iexists (fun ρ : expr × state × List expr =>
    Option.elim (partial_inv_fun K ρ.1) 1 fun e' => ε2 (e', ρ.2))
  isplitr
  · ipureintro
    exact reducible_fill (Λ := con_prob_lang) (K := K) e1 σ1 Hred
  isplitr
  · ipureintro
    exact ⟨⊤, fun _ => le_top⟩
  isplitr
  · ipureintro
    rw [fill_dmap (Λ := con_prob_lang) (K := K) e1 σ1 Hv, Expval_dmap]
    refine le_of_eq_of_le (congrArg _ (funext fun ρ => ?_)) Hineq
    simp [fill_lift', partial_inv_fun_inj (fill_inj (Λ := con_prob_lang) (K := K))]
  iintro %e2 %σ2 %efs
  cases h : partial_inv_fun K e2 with
  | none =>
    simp only [h, Option.elim_none]
    imodintro
    iapply H' $$ %e2 %σ2 %efs
  | some e' =>
    obtain rfl := partial_inv_fun_some h
    simp only [h, Option.elim_some]
    iapply H $$ %e' %σ2 %efs

/-- Rocq: `prog_coupl_reducible`. -/
theorem prog_coupl_reducible (e : expr) (σ : state)
    (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    prog_coupl e σ ε Z ⊢ ⌜reducible (Λ := con_prob_lang) e σ⌝ := by
  iintro ⟨%ε2, %Hred, -, -, -⟩
  ipureintro
  exact Hred

/-- Rocq: `prog_coupl_adv_comp`. -/
theorem prog_coupl_adv_comp (e1 : expr) (σ1 : state)
    (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    □ (∀ e2 σ2 efs, Z e2 σ2 efs 1) ⊢
      (∃ (R : expr × state × List expr → Prop) (ε1 : ℝ≥0∞)
        (ε2 : expr × state × List expr → ℝ≥0∞),
        ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
        ⌜∃ r, ∀ ρ, ε2 ρ ≤ r⌝ ∗
        ⌜ε1 + Expval (prim_step (Λ := con_prob_lang) e1 σ1) ε2 ≤ ε⌝ ∗
        ⌜pgl (prim_step (Λ := con_prob_lang) e1 σ1) R ε1⌝ ∗
        ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs (ε2 (e2, σ2, efs))) -∗
      prog_coupl e1 σ1 ε Z := by
  iintro #H' H
  iapply prog_coupl_equiv2 $$ H' H

/-- Rocq: `prog_coupl_prim_step`. -/
theorem prog_coupl_prim_step (e1 : expr) (σ1 : state)
    (Z : expr → state → List expr → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    □ (∀ e2 σ2 efs, Z e2 σ2 efs 1) ⊢
      (∃ (R : expr × state × List expr → Prop) (ε1 ε2 : ℝ≥0∞),
        ⌜reducible (Λ := con_prob_lang) e1 σ1⌝ ∗
        ⌜ε1 + ε2 ≤ ε⌝ ∗
        ⌜pgl (prim_step (Λ := con_prob_lang) e1 σ1) R ε1⌝ ∗
        ∀ e2 σ2 efs, ⌜R (e2, σ2, efs)⌝ ={∅}=∗ Z e2 σ2 efs ε2) -∗
      prog_coupl e1 σ1 ε Z := by
  iintro #H' ⟨%R, %ε1, %ε2, %Hred, %Hε, %Hpgl, H⟩
  iapply prog_coupl_adv_comp $$ H'
  iexists R, ε1, (fun _ => ε2)
  isplitr
  · ipureintro
    exact Hred
  isplitr
  · ipureintro
    exact ⟨ε2, fun _ => le_rfl⟩
  isplitr
  · ipureintro
    rw [Expval_const, prim_step_mass _ _ Hred, mul_one]
    exact Hε
  isplitr
  · ipureintro
    exact Hpgl
  iexact H

/-! ### Non-expansiveness (the Rocq proofs use `f_equiv` inline) -/

/-- Helper: `state_step_coupl` is non-expansive in its continuation. -/
theorem state_step_coupl_ne {n : ℕ} {σ : state} {ε : ℝ≥0∞} {Z1 Z2 : state → ℝ≥0∞ → IProp GF}
    (HZ : ∀ σ ε, Z1 σ ε ≡{n}≡ Z2 σ ε) : state_step_coupl σ ε Z1 ≡{n}≡ state_step_coupl σ ε Z2 := by
  unfold state_step_coupl state_step_coupl'
  refine least_fixpoint_ne_outer (fun _ x => ?_) .rfl
  exact or_ne.ne .rfl (or_ne.ne (HZ x.1 x.2) .rfl)

/-- Helper: `prog_coupl` is non-expansive in its continuation. -/
theorem prog_coupl_ne {n : ℕ} {e1 : expr} {σ1 : state} {ε : ℝ≥0∞}
    {Z1 Z2 : expr → state → List expr → ℝ≥0∞ → IProp GF}
    (HZ : ∀ e2 σ2 efs ε', Z1 e2 σ2 efs ε' ≡{n}≡ Z2 e2 σ2 efs ε') :
    prog_coupl e1 σ1 ε Z1 ≡{n}≡ prog_coupl e1 σ1 ε Z2 := by
  refine exists_ne fun _ => ?_
  refine sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl ?_
  exact forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => BIFUpdate.ne.ne (HZ _ _ _ _)

end modalities

/-! ## The weakest precondition -/

section pgl_wp_def

variable {GF : BundledGFunctors} [conerisWpGS con_prob_lang GF]

/-- Rocq: `pgl_wp_pre`. -/
abbrev pgl_wp_pre (wp : CoPset → expr → (val → IProp GF) → IProp GF) :
    CoPset → expr → (val → IProp GF) → IProp GF := fun E e1 Φ => iprop(
  ∀ (σ1 : state) (ε1 : ℝ≥0∞), state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
    state_step_coupl σ1 ε1 fun σ2 ε2 =>
      match to_val e1 with
      | some v => iprop(|={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ Φ v)
      | none => prog_coupl e1 σ2 ε2 fun e3 σ3 efs ε3 => iprop(
          ▷ state_step_coupl σ3 ε3 fun σ4 ε4 => iprop(
            |={∅, E}=> state_interp σ4 ∗ err_interp ε4 ∗ wp E e3 Φ ∗
              [∗list] ef ∈ efs, wp ⊤ ef (fork_post (Λ := con_prob_lang)))))

/-- Helper: the common core of `wp_pre_contractive`, `pgl_wp_ne` and `pgl_wp_contractive`. -/
theorem pgl_wp_pre_dist {n : ℕ} {wp wp' : CoPset → expr → (val → IProp GF) → IProp GF}
    {E : CoPset} {e : expr} {Φ Ψ : val → IProp GF}
    (HΦ : ∀ v, to_val e = some v → Φ v ≡{n}≡ Ψ v)
    (Hwp : ∀ m, m < n → ∀ e3, wp E e3 Φ ≡{m}≡ wp' E e3 Ψ)
    (Hfork : ∀ m, m < n → ∀ ef, wp ⊤ ef (fork_post (Λ := con_prob_lang)) ≡{m}≡ wp' ⊤ ef (fork_post (Λ := con_prob_lang))) :
    pgl_wp_pre wp E e Φ ≡{n}≡ pgl_wp_pre wp' E e Ψ := by
  refine forall_ne fun _ => forall_ne fun _ => ?_
  refine wand_ne.ne .rfl (BIFUpdate.ne.ne ?_)
  refine state_step_coupl_ne fun _ _ => ?_
  cases htv : to_val e with
  | some v =>
    exact BIFUpdate.ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl (HΦ v htv)
  | none =>
    refine prog_coupl_ne fun e3 _ _ _ => ?_
    refine Contractive.distLater_dist fun m Hm => ?_
    refine state_step_coupl_ne fun _ _ => ?_
    exact BIFUpdate.ne.ne <| sep_ne.ne .rfl <| sep_ne.ne .rfl <|
      sep_ne.ne (Hwp m Hm e3) (BI.BigSepL.bigSepL_dist fun _ => Hfork m Hm _)

/-- Rocq: `wp_pre_contractive`. -/
instance wp_pre_contractive : Contractive (pgl_wp_pre (GF := GF)) where
  distLater_dist Hwp E _ Φ :=
    pgl_wp_pre_dist (fun _ _ => .rfl) (fun m Hm e3 => Hwp m Hm E e3 Φ)
      (fun m Hm ef => Hwp m Hm ⊤ ef _)

/-- Rocq: `pgl_wp'` (the `Wp` instance of Coneris). As in Rocq, the stuckness parameter is
ignored; we use iris-lean's `Stuckness` (rather than Rocq's `()`) so that the `WP` notation of
iris-lean, which fills in `Stuckness.NotStuck`, can be used. -/
instance pgl_wp' : Wp (IProp GF) expr val Stuckness where
  wp _ := fixpoint pgl_wp_pre

end pgl_wp_def

section pgl_wp

variable {GF : BundledGFunctors} [conerisWpGS con_prob_lang GF]
variable {s : Stuckness} {E : CoPset} {e : expr} {v : val} {Φ Ψ : val → IProp GF}

/-- Rocq: `pgl_wp_unfold`. -/
theorem pgl_wp_unfold (s : Stuckness) (E : CoPset) (e : expr) (Φ : val → IProp GF) :
    WP e @ s; E {{ Φ }} = pgl_wp_pre (Wp.wp (PROP := IProp GF) s) E e Φ :=
  congrFun (congrFun (congrFun (fixpoint_unfold (pgl_wp_pre (GF := GF)).toContractiveHom) E) e) Φ

/-- Helper (not in Rocq): the Coneris WP ignores its stuckness parameter. -/
theorem pgl_wp_stuckness_irrel (s : Stuckness) (E : CoPset) (e : expr) (Φ : val → IProp GF) :
    WP e @ s; E {{ Φ }} = WP e @ E {{ Φ }} := rfl

/-- Helper (not in Rocq): `pgl_wp_unfold` specialised to a non-value (Rocq:
`rewrite pgl_wp_unfold /pgl_wp_pre /= Heq`). -/
theorem pgl_wp_unfold_none {s : Stuckness} {E : CoPset} {e : expr} {Φ : val → IProp GF}
    (h : to_val e = none) :
    WP e @ s; E {{ Φ }} ⊢ ∀ (σ1 : state) (ε1 : ℝ≥0∞), state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
      state_step_coupl σ1 ε1 fun σ2 ε2 =>
        prog_coupl e σ2 ε2 fun e3 σ3 efs ε3 => iprop(
          ▷ state_step_coupl σ3 ε3 fun σ4 ε4 => iprop(
            |={∅, E}=> state_interp σ4 ∗ err_interp ε4 ∗ WP e3 @ s; E {{ Φ }} ∗
              [∗list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post (Λ := con_prob_lang) }})) := by
  rw [pgl_wp_unfold]
  simp only [pgl_wp_pre, h]
  exact .rfl

/-- Rocq: `pgl_wp_ne`. -/
instance pgl_wp_ne : NonExpansive (Wp.wp (PROP := IProp GF) (Expr := expr) s E e) where
  ne {n} := by
    induction n using Nat.strongRecOn generalizing E e with | ind n IH =>
    intro Φ Ψ HΦ
    rw [pgl_wp_unfold s E e Φ, pgl_wp_unfold s E e Ψ]
    exact pgl_wp_pre_dist (fun v _ => HΦ v) (fun m Hm e3 => IH m Hm (OFE.dist_lt HΦ Hm))
      (fun _ _ _ => .rfl)

/-- Rocq: `pgl_wp_contractive`. -/
theorem pgl_wp_contractive (h : to_val e = none) :
    Contractive (Wp.wp (PROP := IProp GF) (Expr := expr) s E e) where
  distLater_dist {_ Φ Ψ} HΦ := by
    rw [pgl_wp_unfold s E e Φ, pgl_wp_unfold s E e Ψ]
    exact pgl_wp_pre_dist (fun v hv => by simp [h] at hv)
      (fun m Hm _ => NonExpansive.ne (HΦ m Hm)) (fun _ _ _ => .rfl)

/-- Rocq: `pgl_wp_value_fupd'`. -/
theorem pgl_wp_value_fupd' : (|={E}=> Φ v) ⊢ WP (Val v) @ s; E {{ Φ }} := by
  rw [pgl_wp_unfold]
  simp only [pgl_wp_pre, to_val_Val]
  iintro H %σ1 %ε1 ⟨Hσ, Hε⟩
  imod H
  imod fupd_mask_subseteq (E1 := E) LawfulSet.empty_subset with Hclose
  imodintro
  iapply state_step_coupl_ret
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pgl_wp_strong_mono`. -/
theorem pgl_wp_strong_mono {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    ⊢ WP e @ s; E1 {{ Φ }} -∗
      (∀ (σ1 : state) (ε1 : ℝ≥0∞) (v : val), state_interp σ1 ∗ err_interp ε1 ∗ Φ v ={E2, ∅}=∗
        state_step_coupl σ1 ε1 fun σ2 ε2 => iprop(
          |={∅, E2}=> state_interp σ2 ∗ err_interp ε2 ∗ Ψ v)) -∗
      WP e @ s; E2 {{ Ψ }} := by
  -- `iloeb` would otherwise try to generalize the (auxiliary) recursive declaration.
  clear pgl_wp_strong_mono
  iloeb as IH generalizing %e %E1 %E2 %HE %Φ %Ψ
  rw [pgl_wp_unfold s E1 e Φ, pgl_wp_unfold s E2 e Ψ]
  iintro H HΦ %σ1 %ε Hσε
  ispecialize H $$ %σ1 %ε Hσε
  imod fupd_mask_subseteq HE with Hclose
  imod H
  imodintro
  iapply state_step_coupl_bind $$ [-H] H
  iintro %σ2 %ε2 H
  cases hv : to_val e with
  | some v =>
    iapply fupd_state_step_coupl
    imod H with ⟨Hσ, Hε, HΦv⟩
    imod Hclose
    imod HΦ $$ %σ2 %ε2 %v [Hσ Hε HΦv] with H
    · iframe
    imodintro
    iexact H
  | none =>
    iapply state_step_coupl_ret
    iapply prog_coupl_mono $$ [-H] H
    iintro %e3 %σ3 %efs %ε3 H !>
    iapply state_step_coupl_mono $$ [-H] H
    iintro %σ4 %ε4 H
    imod H with ⟨Hσ, Hε, Hwp, Hefs⟩
    imod Hclose
    imodintro
    iframe Hσ Hε Hefs
    iapply IH $$ %e3 %E1 %E2 %HE %Φ %Ψ Hwp HΦ
/-- Rocq: `pgl_wp_strong_mono'`. -/
theorem pgl_wp_strong_mono' {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    ⊢ WP e @ s; E1 {{ Φ }} -∗
      (∀ (σ1 : state) (ε1 : ℝ≥0∞) (v : val), state_interp σ1 ∗ err_interp ε1 ∗ Φ v ={E2}=∗
        state_interp σ1 ∗ err_interp ε1 ∗ Ψ v) -∗
      WP e @ s; E2 {{ Ψ }} := by
  iintro Hwp Hw
  iapply pgl_wp_strong_mono HE $$ Hwp
  iintro %σ1 %ε1 %v H
  iapply state_step_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >Hclose
  iapply Hw $$ H

/-- Rocq: `state_step_coupl_pgl_wp`. -/
theorem state_step_coupl_pgl_wp :
    (∀ (σ1 : state) (ε1 : ℝ≥0∞), state_interp σ1 ∗ err_interp ε1 ={E, ∅}=∗
      state_step_coupl σ1 ε1 fun σ2 ε2 => iprop(
        |={∅, E}=> state_interp σ2 ∗ err_interp ε2 ∗ WP e @ s; E {{ Φ }})) ⊢
    WP e @ s; E {{ Φ }} := by
  rw [pgl_wp_unfold s E e Φ]
  iintro H %σ1 %ε1 Hσε
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_bind $$ [] H
  iintro %σ2 %ε2 H
  iapply fupd_state_step_coupl
  imod H with ⟨Hσ, Hε, H⟩
  iapply H $$ %σ2 %ε2
  iframe

/-- Rocq: `fupd_pgl_wp`. -/
theorem fupd_pgl_wp : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  rw [pgl_wp_unfold s E e Φ]
  iintro H %σ1 %ε1 Hσε
  imod H
  iapply H $$ %σ1 %ε1 Hσε

/-- Rocq: `pgl_wp_fupd`. -/
theorem pgl_wp_fupd : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }} := by
  iintro H
  iapply pgl_wp_strong_mono LawfulSet.subset_refl $$ H
  iintro %σ1 %ε1 %v ⟨Hσ, Hε, HΦ⟩
  iapply state_step_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imod HΦ
  imodintro
  iframe

/-- Rocq: `pgl_wp_atomic`. -/
theorem pgl_wp_atomic {E1 E2 : CoPset} [Atomic (Λ := con_prob_lang) StronglyAtomic e] :
    (|={E1, E2}=> WP e @ s; E2 {{ v, |={E2, E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }} := by
  rw [pgl_wp_unfold s E1 e Φ, pgl_wp_unfold s E2 e]
  iintro H %σ1 %ε1 Hσε
  imod H
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_mono $$ [] H
  iintro %σ2 %ε2
  cases hv : to_val e with
  | some v =>
    iintro >⟨Hσ, Hε, >HΦ⟩
    imodintro
    iframe
  | none =>
    iintro H
    ihave H := prog_coupl_strengthen _ _ _ _ $$ [] H
    · iintro !> %e2 %σ3 %efs !>
      iapply state_step_coupl_ret_err_ge_1 _ _ _ le_rfl
    iapply prog_coupl_mono $$ [] H
    iintro %e3 %σ3 %efs %ε3 ⟨%Hcase, H⟩ !>
    rcases Hcase with ⟨σ', Hstep⟩ | Hge
    · iapply state_step_coupl_bind $$ [] H
      iintro %σ4 %ε4 H
      iapply fupd_state_step_coupl
      imod H with ⟨Hσ, Hε, Hwp, Hefs⟩
      rw [pgl_wp_unfold s E2 e3]
      imod Hwp $$ %σ4 %ε4 [Hσ Hε] with Hwp
      · iframe
      imodintro
      iapply state_step_coupl_mono $$ [Hefs] Hwp
      iintro %σ5 %ε5
      cases hv3 : to_val e3 with
      | some v =>
        obtain rfl : e3 = Val v := (ConProbLang.of_to_val (Λ := con_prob_lang) e3 v hv3).symm
        iintro >⟨Hσ, Hε, >HΦ⟩
        imodintro
        iframe Hσ Hε Hefs
        iapply pgl_wp_value_fupd'
        imodintro
        iexact HΦ
      | none =>
        obtain ⟨v, hv⟩ := Atomic.atomic (Λ := con_prob_lang) (a := .StronglyAtomic) σ' e3 σ3 efs Hstep
        exact absurd (hv3.symm.trans hv) (Option.some_ne_none v).symm
    · iclear H
      iapply state_step_coupl_ret_err_ge_1 _ _ _ Hge

/-- Rocq: `pgl_wp_step_fupd`. -/
theorem pgl_wp_step_fupd {E1 E2 : CoPset} {P : IProp GF} (h : to_val e = none) (HE : E2 ⊆ E1) :
    ⊢ (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }} := by
  rw [pgl_wp_unfold s E1 e Φ, pgl_wp_unfold s E2 e]
  simp only [pgl_wp_pre, h]
  iintro HR H %σ1 %ε1 Hσε
  imod HR
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_mono $$ [HR] H
  iintro %σ2 %ε2 H
  iapply prog_coupl_mono $$ [HR] H
  iintro %e3 %σ3 %efs %ε3 H !>
  iapply state_step_coupl_mono $$ [HR] H
  iintro %σ4 %ε4 >⟨Hσ, Hε, Hwp, Hefs⟩
  imod HR
  imodintro
  iframe Hσ Hε Hefs
  iapply pgl_wp_strong_mono HE $$ Hwp
  iintro %σ %ε %v ⟨Hσ, Hε, HK⟩
  iapply state_step_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imod HK $$ HR
  imodintro
  iframe

/-- Rocq: `pgl_wp_bind`. -/
theorem pgl_wp_bind (K : expr → expr) [ConLanguageCtx (Λ := con_prob_lang) K] :
    WP e @ s; E {{ v, WP (K (Val v)) @ s; E {{ Φ }} }} ⊢ WP (K e) @ s; E {{ Φ }} := by
  iintro H
  -- `iloeb` would otherwise try to generalize the (auxiliary) recursive declaration.
  clear pgl_wp_bind
  iloeb as IH generalizing %E %e %Φ
  rw [pgl_wp_unfold s E e, pgl_wp_unfold s E (K e) Φ]
  iintro %σ1 %ε1 Hσε
  imod H $$ %σ1 %ε1 Hσε with H
  imodintro
  iapply state_step_coupl_bind $$ [] H
  iintro %σ2 %ε2 H
  cases hv : to_val e with
  | some v =>
    obtain rfl : e = Val v := (ConProbLang.of_to_val (Λ := con_prob_lang) e v hv).symm
    iapply fupd_state_step_coupl
    imod H with ⟨Hσ, Hε, H⟩
    beta_reduce
    rw [pgl_wp_unfold s E (K (Val v)) Φ]
    iapply H $$ %σ2 %ε2
    iframe
  | none =>
    have hK : to_val (K e) = none := fill_not_val (Λ := con_prob_lang) e hv
    iapply state_step_coupl_ret
    rw [hK]
    iapply prog_coupl_ctx_bind K e σ2 _ ε2 hv $$ []
    · iintro !> %e2 %σ3 %efs !>
      iapply state_step_coupl_ret_err_ge_1 _ _ _ le_rfl
    iapply prog_coupl_mono $$ [] H
    iintro %e3 %σ3 %efs %ε3 H !>
    iapply state_step_coupl_mono $$ [] H
    iintro %σ4 %ε4 >⟨Hσ, Hε, H, Hefs⟩
    imodintro
    iframe Hσ Hε Hefs
    iapply IH $$ %E %e3 %Φ H

/-! ### Derived rules -/

/-- Rocq: `pgl_wp_mono`. -/
theorem pgl_wp_mono (HΦ : ∀ v, Φ v ⊢ Ψ v) : WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }} := by
  iintro H
  iapply pgl_wp_strong_mono' LawfulSet.subset_refl $$ H
  iintro %σ1 %ε1 %v ⟨Hσ, Hε, HΦv⟩
  imodintro
  iframe Hσ Hε
  iapply HΦ v $$ HΦv

/-- Rocq: `pgl_wp_mask_mono`. -/
theorem pgl_wp_mask_mono {E1 E2 : CoPset} (HE : E1 ⊆ E2) :
    WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }} := by
  iintro H
  iapply pgl_wp_strong_mono' HE $$ H
  iintro %σ1 %ε1 %v H
  imodintro
  iexact H

/-- Rocq: `pgl_wp_value_fupd`. -/
theorem pgl_wp_value_fupd [IntoVal (Λ := con_prob_lang) e v] :
    (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }} := by
  obtain rfl : Val v = e := IntoVal.into_val (Λ := con_prob_lang)
  exact pgl_wp_value_fupd'

/-- Rocq: `pgl_wp_value'`. -/
theorem pgl_wp_value' : Φ v ⊢ WP (Val v) @ s; E {{ Φ }} :=
  fupd_intro.trans pgl_wp_value_fupd'

/-- Rocq: `pgl_wp_value`. -/
theorem pgl_wp_value [IntoVal (Λ := con_prob_lang) e v] : Φ v ⊢ WP e @ s; E {{ Φ }} :=
  fupd_intro.trans pgl_wp_value_fupd

/-- Rocq: `pgl_wp_frame_l`. -/
theorem pgl_wp_frame_l {R : IProp GF} : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, H⟩
  iapply pgl_wp_strong_mono LawfulSet.subset_refl $$ H
  iintro %σ1 %ε1 %v ⟨Hσ, Hε, HΦ⟩
  iapply state_step_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imodintro
  iframe

/-- Rocq: `pgl_wp_frame_r`. -/
theorem pgl_wp_frame_r {R : IProp GF} : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }} := by
  iintro ⟨H, HR⟩
  iapply pgl_wp_strong_mono LawfulSet.subset_refl $$ H
  iintro %σ1 %ε1 %v ⟨Hσ, Hε, HΦ⟩
  iapply state_step_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imodintro
  iframe

/-- Rocq: `pgl_wp_frame_step_l`. -/
theorem pgl_wp_frame_step_l {E1 E2 : CoPset} {R : IProp GF} (h : to_val e = none)
    (HE : E2 ⊆ E1) :
    (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }} := by
  iintro ⟨Hu, Hwp⟩
  iapply pgl_wp_step_fupd h HE $$ Hu
  iapply pgl_wp_mono (fun _ => by iintro HΦ HR !>; iframe) $$ Hwp

/-- Rocq: `pgl_wp_frame_step_r`. -/
theorem pgl_wp_frame_step_r {E1 E2 : CoPset} {R : IProp GF} (h : to_val e = none)
    (HE : E2 ⊆ E1) :
    WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }} :=
  sep_comm.1.trans <| (pgl_wp_frame_step_l h HE).trans <| pgl_wp_mono fun _ => sep_comm.1

/-- Rocq: `pgl_wp_frame_step_l'`. -/
theorem pgl_wp_frame_step_l' {R : IProp GF} (h : to_val e = none) :
    ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, Hwp⟩
  iapply pgl_wp_frame_step_l h LawfulSet.subset_refl
  iframe Hwp
  iintro !> !> !>
  iexact HR

/-- Rocq: `pgl_wp_frame_step_r'`. -/
theorem pgl_wp_frame_step_r' {R : IProp GF} (h : to_val e = none) :
    WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }} :=
  sep_comm.1.trans <| (pgl_wp_frame_step_l' h).trans <| pgl_wp_mono fun _ => sep_comm.1

/-- Rocq: `pgl_wp_wand`. -/
theorem pgl_wp_wand :
    ⊢ WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }} := by
  iintro Hwp H
  iapply pgl_wp_strong_mono LawfulSet.subset_refl $$ Hwp
  iintro %σ1 %ε1 %v ⟨Hσ, Hε, HΦ⟩
  iapply state_step_coupl_ret
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro >-
  imodintro
  iframe Hσ Hε
  iapply H $$ HΦ

/-- Rocq: `pgl_wp_wand_l`. -/
theorem pgl_wp_wand_l : (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }} := by
  iintro ⟨H, Hwp⟩
  iapply pgl_wp_wand $$ Hwp H

/-- Rocq: `wp_wand_r` (sic: not `pgl_wp_wand_r`). -/
theorem wp_wand_r : WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }} := by
  iintro ⟨Hwp, H⟩
  iapply pgl_wp_wand $$ Hwp H

/-- Rocq: `pgl_wp_frame_wand`. -/
theorem pgl_wp_frame_wand {R : IProp GF} :
    ⊢ R -∗ WP e @ s; E {{ v, R -∗ Φ v }} -∗ WP e @ s; E {{ Φ }} := by
  iintro HR Hwp
  iapply pgl_wp_wand $$ Hwp
  iintro %v HΦ
  iapply HΦ $$ HR

end pgl_wp

/-! ## Proofmode class instances -/

section proofmode_classes

variable {GF : BundledGFunctors} [conerisWpGS con_prob_lang GF]
variable {s : Stuckness} {E : CoPset} {e : expr} {Φ Ψ : val → IProp GF} {P R : IProp GF}

/-- Rocq: `frame_pgl_wp`. -/
instance frame_pgl_wp {p : Bool} [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) where
  frame := pgl_wp_frame_l.trans <|
    pgl_wp_mono fun v => (H v).frame_instantiatiate_exist_disabled.frame

/-- Rocq: `is_except_0_pgl_wp`. -/
instance is_except_0_pgl_wp : IsExcept0 (WP e @ s; E {{ Φ }}) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_pgl_wp)

/-- Rocq: `elim_modal_fupd_pgl_wp`. (Higher priority than `elim_modal_fupd_pgl_wp_atomic`.) -/
instance (priority := default + 10) elim_modal_fupd_pgl_wp {p : Bool} {io : InOut} :
    ElimModal True p io false iprop(|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases intuitionisticallyIf_elim $$ H with H
    iapply fupd_pgl_wp
    imod H
    imodintro
    iapply G $$ H

/-- Rocq: `elim_modal_bupd_pgl_wp`. -/
instance elim_modal_bupd_pgl_wp {p : Bool} {io : InOut} :
    ElimModal True p io false iprop(|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}) where
  elim_modal := by
    rintro ⟨⟩
    refine sep_mono (intuitionisticallyIf_mono (BIUpdateFUpdate.fupd_of_bupd (E := E))) .rfl
      |>.trans ?_
    exact (elim_modal_fupd_pgl_wp (io := io)).elim_modal ⟨⟩

/-- Rocq: `elim_modal_fupd_pgl_wp_atomic`. -/
instance elim_modal_fupd_pgl_wp_atomic {p : Bool} {io : InOut}
    {E1 E2 : CoPset} :
    ElimModal (Atomic (Λ := con_prob_lang) StronglyAtomic e) p io false iprop(|={E1, E2}=> P) P
      (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2, E1}=> Φ v }}) where
  elim_modal := by
    rintro _
    iintro ⟨H, G⟩
    icases intuitionisticallyIf_elim $$ H with H
    iapply pgl_wp_atomic
    imod H
    imodintro
    iapply G $$ H

/-- Rocq: `add_modal_fupd_pgl_wp`. -/
instance add_modal_fupd_pgl_wp : AddModal iprop(|={E}=> P) P (WP e @ s; E {{ Φ }}) where
  add_modal := by
    iintro ⟨H1, H2⟩
    imod H1
    iapply H2 $$ H1

/-- Rocq: `elim_acc_pgl_wp_atomic`. -/
instance (priority := low) elim_acc_pgl_wp_atomic {X : Type} {E1 E2 : CoPset}
    {α β : X → IProp GF} {γ : X → Option (IProp GF)} :
    ElimAcc (Atomic (Λ := con_prob_lang) StronglyAtomic e) (fupd E1 E2) (fupd E2 E1) α β γ
      (WP e @ s; E1 {{ Φ }})
      (fun x => WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %atomic Hinner >⟨%x, Hα, Hclose⟩
    iapply pgl_wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

/-- Rocq: `elim_acc_pgl_wp_nonatomic`. -/
instance elim_acc_pgl_wp_nonatomic {X : Type} {α β : X → IProp GF}
    {γ : X → Option (IProp GF)} :
    ElimAcc True (fupd E E) (fupd E E) α β γ (WP e @ s; E {{ Φ }})
      (fun x => WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    iapply pgl_wp_fupd
    iapply pgl_wp_wand $$ [Hinner Hα]
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

end Coneris
