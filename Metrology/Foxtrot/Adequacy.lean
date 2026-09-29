module

public import Metrology.Foxtrot.PrimitiveLaws
public import Metrology.ConProbLang.LubTermination

/-!
# Adequacy of Foxtrot

Ported from clutch/theories/foxtrot/adequacy.v

A Foxtrot WP `WP e {{ v, ∃ v', 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }}` proved with `↯ ε` and `0 ⤇ e'`
yields, for every tape-oblivious scheduler `sch` of the left-hand side and every `n`, an
approximate coupling (`ARcoupl`) between the `n`-step execution of `e` under `sch` and the limit
execution of `e'` under some full-information oblivious scheduler (`foxtrot_adequacy_full_info_*`),
hence under some tape-oblivious scheduler (`foxtrot_adequacy_intermediate`). Consequently the
least upper bound of the termination probabilities of `e` is at most that of `e'` plus `ε`
(`foxtrot_adequacy`).

## Rocq → Lean map
All Rocq names are kept: `step_fupd_fupdN_S`, `fupdN_S`, `fupd_later_mono`,
`wp_adequacy_val_fupd`, `spec_coupl_erasure`, `spec_coupl_erasure'`, `prog_coupl_erasure`,
`wp_adequacy_step_fupdN`, `foxtrot_adequacy_full_info_intermediate_multi`,
`foxtrot_adequacy_full_info_intermediate`, `foxtrot_adequacy_intermediate`, `ARcoupl_lub`,
`foxtrot_adequacy`.

## Design choices / deviations (Rocq → Lean)
* Errors are `ℝ≥0∞` (Rocq: `R` / `nonnegreal`): the hypotheses `0 <= ε` are dropped;
  `ε' > 0` is `0 < ε'`. Rocq's `Rbar_le a (Rbar_plus b ε)` (on `lub_termination_prob`) is
  `a ≤ b + ε` in `ℝ≥0∞`.
* The postcondition relation `λ v '(l, ρ), ∃ v', ρ.1 !! 0 = Some (Val v') ∧ ϕ v v'` is the
  helper `adequacy_rel ϕ` (it only inspects the RHS thread pool, via `p.2.1`).
* RHS configurations are `CPState` (local notation for `(con_lang_mdp con_prob_lang).mdpstate`);
  Rocq's `(es', σ')` is `((es', σ') : CPState)`.
* `λ '(e3, σ3, efs), ..` is written with projections `t.1`, `t.2.1`, `t.2.2`, and
  `<[num:=e3]> es` is `es.set num e3`, as in `Metrology.ConProbLang.Erasure` / `Coneris.Adequacy`.
* `|={∅}▷=>^n P` is iris-lean's `|={∅}[∅]▷=>^[n] P`.
* The Rocq statements `∀ ε', ε' > 0 -> P -∗ Q` take `(ε' : ℝ≥0∞) (Hε' : 0 < ε')` before `⊢`.
* The Rocq proofs of the four "erasure" lemmas repeat the same argument: collect, for every
  pair `(a, (l, ρ'))` in the support of the coupling `S`, a full-information scheduler for the
  continuation (`iris_choice` over a `sigT` of the support, then `decide`/`epsilon` to turn it
  into a function of the history), and append them at the frontier of the first scheduler with
  `full_info_append_osch`. Here the choice is done at the level of pure propositions (the Iris
  part only commutes the universal quantifier with the (step-)fancy updates, via
  `fupd_step_fupdN_pure_forall_imp`), and the probabilistic argument is factored into the pure
  helper `ARcoupl_append_osch`. Likewise the scheduler `full_info_cons_osch (λ _, dmap (λ ac,
  length es' + encode_nat ac) (sch ..)) (λ x, f (decode_nat (x - length es')))` of
  `wp_adequacy_step_fupdN` is the pure helper `ARcoupl_cons_osch`.
* The Rocq proofs move pure conclusions under `|={∅}=> |={∅}▷=>^n` through universal
  quantifiers using clutch's `iris_ext` `FromForall` instances; here this is done by the helpers
  `fupd_step_fupdN_pure_forall` / `fupd_step_fupdN_pure_forall_imp` (local copies of the
  `Coneris.Adequacy` helpers, so that this file does not import Coneris).
* The amplification case (`ε_new := ε + ε'/2`) first discharges the trivial case `1 ≤ ε + ε'`
  (so that `ε` and `ε'` are finite in `ℝ≥0∞`).
* The thread-pool bookkeeping of `wp_adequacy_step_fupdN` uses `BigSepL.bigSepL_insert_acc`
  instead of Rocq's `list_elem_of_split_length` split (as in `Coneris.Adequacy`).
* `foxtrot_adequacy_full_info_intermediate_multi` and its corollaries take
  `Hwp : ∀ [foxtrotGS GF], ⊢@{IProp GF} ↯ ε -∗ ..` (Rocq: `∀ `{foxtrotGS Σ}, ..`); the thread
  pool `[∗ map] n↦e ∈ to_tpool es', n ⤇ e` is `bigSepM (M := tpoolF) (fun n e => n ⤇ e)
  (to_tpool es')` (as in `spec_ra_init`), and the soundness of the step-indexed fancy update is
  `step_fupdN_soundness` with `hlc := .hasNoLC` (Rocq: `step_fupdN_soundness_no_lc`).
  The ghost state is allocated with the instances `foxtrotGpreS_heap` / `foxtrotGpreS_tapes`
  (named explicitly, since `foxtrotGpreS_spec` provides instances of the same types).
* The adequacy theorems take the ghost-functor bundle `GF` explicitly (Rocq: `Σ`).
* Scheduler states are in `Type` with `[DecidableEq] [Countable]` (Rocq: `Countable`, which
  bundles `EqDecision`). The existential `∃ `(Countable sch_int_σ') sch' ζ' `(!TapeOblivious ..)`
  of `foxtrot_adequacy_intermediate` / `ARcoupl_lub` is
  `∃ (sch_int_σ' : Type) (_ : DecidableEq sch_int_σ') (_ : Countable sch_int_σ') sch' ζ'
  (_ : TapeOblivious sch_int_σ' sch'), ..`.

## Omitted
None.

## Added helpers (not in Rocq)
* Generic step-fupd facts (copies of the `Coneris.Adequacy` helpers):
  `fupd_laterN_to_step_fupdN`, `step_fupdN_except_0`, `fupd_step_fupdN_plain_forall`,
  `fupd_step_fupdN_pure_forall`, `fupd_step_fupdN_pure_forall_imp`, `fupd_pure_forall_imp`;
  and `fupd_step_fupdN_forall_pure_wand` (Rocq: `iIntros (ε'' Hε'')` through
  `|={∅}=> |={∅}▷=>^n`), `forall_pure_wand_elim`.
* `spec_interp_prog_agree` (`spec_auth_prog_agree` stated for `spec_interp ρ`).
* Facts about the MDP of `con_prob_lang` (copies of the `Coneris.Adequacy` helpers):
  `dmap_dbind_dret_dbind`, `con_prob_lang_mdp_step_stutter`, `con_prob_lang_mdp_step_prim`.
* `adequacy_rel`, `ARcoupl_dmap_lift_r`, `ARcoupl_append_osch`, `ARcoupl_cons_osch`,
  `ARcoupl_amplify`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate
set_option quotPrecheck false in
/-- The action type of `con_lang_mdp con_prob_lang` (reducibly `ℕ`). -/
local notation "CPAct" => (con_lang_mdp con_prob_lang).mdpaction

/-! ## Local helpers -/

section helpers

variable {GF : BundledGFunctors} [InvGS_gen .hasNoLC GF]

/-- Helper: a fancy update of `n + 1` laters is an `(n + 1)`-step fancy update. -/
theorem fupd_laterN_to_step_fupdN (E : CoPset) (n : ℕ) {Q : IProp GF} :
    (|={E}=> ▷^[n+1] Q) ⊢ |={E}[E]▷=>^[n+1] Q :=
  (BIFUpdate.mono (step_fupdN_intro LawfulSet.subset_refl)).trans BIFUpdate.trans

/-- Helper: an except-0 under `n + 1` step fancy updates can be dropped. -/
theorem step_fupdN_except_0 (E1 E2 : CoPset) {P : IProp GF} (n : ℕ) :
    (|={E1}[E2]▷=>^[n+1] ◇ P) ⊢ |={E1}[E2]▷=>^[n+1] P :=
  calc
    _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> ◇ P := (step_fupdN_add (n := n) (m := 1)).mp
    _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> P := step_fupdN_mono (BIFUpdate.mono (later_mono fupd_except0))
    _ ⊢ |={E1}[E2]▷=>^[n+1] P := (step_fupdN_add (n := n) (m := 1)).mpr

/-- Helper (clutch `iris_ext`): commuting a plain universal quantifier with
`|={∅}=> |={∅}▷=>^n`. -/
theorem fupd_step_fupdN_plain_forall {A : Type _} (Φ : A → IProp GF) [∀ x, Plain (Φ x)] (n : ℕ) :
    (∀ x, |={∅}=> |={∅}[∅]▷=>^[n] Φ x) ⊢ |={∅}=> |={∅}[∅]▷=>^[n] ∀ x, Φ x := by
  cases n with
  | zero =>
    simp only [Nat.repeat]
    exact (fupd_plain_forall LawfulSet.subset_refl).mpr
  | succ n =>
    calc
      _ ⊢ ∀ x, |={∅}=> ▷^[n+1] ◇ Φ x :=
          forall_mono fun _ => (BIFUpdate.mono step_fupdN_plain).trans BIFUpdate.trans
      _ ⊢ |={∅}=> ∀ x, ▷^[n+1] ◇ Φ x := (fupd_plain_forall LawfulSet.subset_refl).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ∀ x, ◇ Φ x := BIFUpdate.mono (laterN_forall (n+1)).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ◇ ∀ x, Φ x := BIFUpdate.mono (laterN_mono (n+1) except0_forall.mpr)
      _ ⊢ |={∅}[∅]▷=>^[n+1] ◇ ∀ x, Φ x := fupd_laterN_to_step_fupdN ∅ n
      _ ⊢ |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := step_fupdN_except_0 ∅ ∅ n
      _ ⊢ |={∅}=> |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := fupd_intro

/-- Helper: a pure consequence of pure conclusions under `|={∅}=> |={∅}▷=>^n`, for all `x`. -/
theorem fupd_step_fupdN_pure_forall {A : Type _} {q : A → Prop} {r : Prop} (n : ℕ)
    (h : (∀ x, q x) → r) :
    (∀ x, |={∅}=> |={∅}[∅]▷=>^[n] ⌜q x⌝) ⊢@{IProp GF} |={∅}=> |={∅}[∅]▷=>^[n] ⌜r⌝ :=
  (fupd_step_fupdN_plain_forall (fun x => iprop(⌜q x⌝)) n).trans
    (BIFUpdate.mono (step_fupdN_mono (pure_forall.2.trans (pure_mono h))))

/-- Helper: as `fupd_step_fupdN_pure_forall`, with a pure premise for each `x`. -/
theorem fupd_step_fupdN_pure_forall_imp {A : Type _} {p q : A → Prop} {r : Prop} (n : ℕ)
    (h : (∀ x, p x → q x) → r) :
    (∀ x, ⌜p x⌝ -∗ |={∅}=> |={∅}[∅]▷=>^[n] ⌜q x⌝) ⊢@{IProp GF} |={∅}=> |={∅}[∅]▷=>^[n] ⌜r⌝ := by
  iintro H
  iapply fupd_step_fupdN_pure_forall (q := fun x => p x → q x) n h
  iintro %x
  by_cases hx : p x
  · imod H $$ %x %hx with H
    imodintro
    iapply step_fupdN_mono (pure_mono fun hq _ => hq) $$ H
  · iclear H
    imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    exact fun hx' => absurd hx' hx

/-- Helper: `fupd_step_fupdN_pure_forall_imp` without steps. -/
theorem fupd_pure_forall_imp {A : Type _} {p q : A → Prop} {r : Prop} (h : (∀ x, p x → q x) → r) :
    (∀ x, ⌜p x⌝ -∗ |={∅}=> ⌜q x⌝) ⊢@{IProp GF} |={∅}=> ⌜r⌝ :=
  fupd_step_fupdN_pure_forall_imp 0 h

end helpers

/-- Helper: a `dmap` of a deterministic continuation, followed by a bind. -/
theorem dmap_dbind_dret_dbind {α β γ δ : Type _} [Countable α] [Countable β] [Countable γ]
    [Countable δ] (F : β → γ) (G : α → β) (μ : Distr α) (g : γ → Distr δ) :
    (dmap F (μ ≫= fun a => dret (G a)) ≫= g) = μ ≫= fun a => g (F (G a)) := by
  rw [dmap, ← dbind_assoc, ← dbind_assoc]
  refine dbind_ext_right _ _ _ fun a => ?_
  rw [dret_id_left, dret_id_left]

section sch_step_helpers

variable {sch_int_state X : Type} [Countable sch_int_state] [Countable X]

/-- Helper: stepping a thread that is out of bounds, or a value, stutters. -/
theorem con_prob_lang_mdp_step_stutter (e : expr) (es : List expr) (σ : state)
    (sch_σ : sch_int_state) (k : ℕ) (g : sch_int_state × CPState → Distr X)
    (Hv : to_val e = none)
    (Hk : (e :: es)[k]? = none ∨ ∃ e' v, (e :: es)[k]? = some e' ∧ to_val e' = some v) :
    (dmap (fun c => (sch_σ, c)) ((con_lang_mdp con_prob_lang).step k (e :: es, σ)) ≫= g) =
      g (sch_σ, (e :: es, σ)) := by
  have Hv : ConProbLang.to_val (Λ := con_prob_lang) e = none := Hv
  rcases Hk with Hk | ⟨e', v, Hk, Hv'⟩
  · simp only [con_lang_mdp_step_eq, con_lang_mdp_step, List.getElem?_cons_zero,
      Option.bind_eq_bind, Option.bind_some, Hv, Hk]
    exact (congrArg (· ≫= g) (dmap_dret _ _)).trans (dret_id_left _ _)
  · have Hv' : ConProbLang.to_val (Λ := con_prob_lang) e' = some v := Hv'
    simp only [con_lang_mdp_step_eq, con_lang_mdp_step, List.getElem?_cons_zero,
      Option.bind_eq_bind, Option.bind_some, Hv, Hk, Hv']
    exact (congrArg (· ≫= g) (dmap_dret _ _)).trans (dret_id_left _ _)

/-- Helper: stepping a thread that is not a value takes a `prim_step` of it. -/
theorem con_prob_lang_mdp_step_prim (e : expr) (es : List expr) (e' : expr) (σ : state)
    (sch_σ : sch_int_state) (k : ℕ) (g : sch_int_state × CPState → Distr X)
    (Hv : to_val e = none) (Hk : (e :: es)[k]? = some e') (Hv' : to_val e' = none) :
    (dmap (fun c => (sch_σ, c)) ((con_lang_mdp con_prob_lang).step k (e :: es, σ)) ≫= g) =
      prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
        g (sch_σ, ((e :: es).set k t.1 ++ t.2.2, t.2.1)) := by
  have Hv : ConProbLang.to_val (Λ := con_prob_lang) e = none := Hv
  have Hv' : ConProbLang.to_val (Λ := con_prob_lang) e' = none := Hv'
  simp only [con_lang_mdp_step_eq, con_lang_mdp_step, List.getElem?_cons_zero,
    Option.bind_eq_bind, Option.bind_some, Hv, Hk, Hv']
  exact dmap_dbind_dret_dbind _ _ _ _

end sch_step_helpers

/-! ## Pure coupling helpers -/

/-- Helper: the postcondition relation of the adequacy theorems (Rocq: the inline
`λ v '(l, ρ), ∃ v', ρ.1 !! 0%nat = Some (Val v') /\ ϕ v v'`). -/
abbrev adequacy_rel (ϕ : val → val → Prop) (v : val) (p : full_info_state × CPState) : Prop :=
  ∃ v', p.2.1[0]? = some (Val v') ∧ ϕ v v'

/-- Helper: `adequacy_rel` ignores the history, so it is preserved by relabelling it. -/
theorem ARcoupl_dmap_lift_r (μ : Distr val) (ν : Distr (full_info_state × CPState))
    (g : full_info_state → full_info_state) (ϕ : val → val → Prop) (ε : ℝ≥0∞)
    (H : ARcoupl μ ν (adequacy_rel ϕ) ε) :
    ARcoupl μ (dmap (fun p : full_info_state × CPState => (g p.1, p.2)) ν) (adequacy_rel ϕ) ε := by
  rw [← dmap_id μ]
  exact ARcoupl_map (fun x => x) _ μ ν (adequacy_rel ϕ) ε H

/-- Helper: the amplification step of the erasure lemmas. If a coupling with error `ε + ε'`
follows from any error `ε2 > ε` and any `ε'' > 0`, it holds. -/
theorem ARcoupl_amplify {P : ℝ≥0∞ → Prop} (ε ε' : ℝ≥0∞) (Hε' : 0 < ε')
    (Htriv : ∀ e, 1 ≤ e → P e)
    (H : ∀ ε2, ε < ε2 → ∀ ε'', 0 < ε'' → P (ε2 + ε'')) : P (ε + ε') := by
  by_cases h1 : 1 ≤ ε + ε'
  · exact Htriv _ h1
  have hε : ε ≠ ∞ := fun h => h1 (by simp [h])
  have hε' : ε' ≠ ∞ := fun h => h1 (by simp [h])
  have h2 : 0 < ε' / 2 := ENNReal.half_pos Hε'.ne'
  have := H (ε + ε' / 2) (ENNReal.lt_add_right hε h2.ne') (ε' / 2) h2
  rwa [add_assoc, ENNReal.add_halves] at this

/-- Helper (the common core of the four erasure lemmas of the Rocq file): appending, at the
frontier of `osch`, schedulers for the continuations of all pairs in the support of a coupling
`S` with an injectivity property. -/
theorem ARcoupl_append_osch {A : Type _} [Countable A] (μ : Distr A) (F : A → Distr val)
    (ρ : CPState) (osch : full_info_oscheduler) (S : A → full_info_state × CPState → Prop)
    (ε1 ε' : ℝ≥0∞) (X2 : full_info_state × CPState → ℝ≥0∞) (ϕ : val → val → Prop)
    (Hcoupl : ARcoupl μ (osch_lim_exec osch.fi_osch ([], ρ)) S ε1)
    (Hinj : ∀ a1 a2 l ρ1 ρ2, S a1 (l, ρ1) → S a2 (l, ρ2) → a1 = a2 ∧ ρ1 = ρ2)
    (H : ∀ a l ρ', S a (l, ρ') → ∃ fp : full_info_oscheduler,
      ARcoupl (F a) (osch_lim_exec fp.fi_osch ([], ρ')) (adequacy_rel ϕ) (X2 (l, ρ') + ε')) :
    ∃ osch' : full_info_oscheduler, ARcoupl (μ ≫= F) (osch_lim_exec osch'.fi_osch ([], ρ))
      (adequacy_rel ϕ) (ε1 + Expval (osch_lim_exec osch.fi_osch ([], ρ)) X2 + ε') := by
  classical
  choose g hg using H
  let f : full_info_state → full_info_oscheduler := fun l =>
    if h : ∃ a ρ', S a (l, ρ') then
      g (Classical.choose h) l (Classical.choose (Classical.choose_spec h))
        (Classical.choose_spec (Classical.choose_spec h))
    else full_info_inhabitant
  refine ⟨full_info_append_osch osch f, ?_⟩
  set ν := osch_lim_exec osch.fi_osch ([], ρ) with hν
  let K : full_info_state × CPState → Distr (full_info_state × CPState) := fun p =>
    if h : ∃ prel, prel <+: p.1 ∧ is_frontier prel [] osch then
      osch_lim_exec (full_info_lift_osch (Classical.choose h) (f (Classical.choose h))).fi_osch p
    else dzero
  have Hsum : ∑' b, ν b * (X2 b + ε') ≤ Expval ν X2 + ε' := by
    simp only [mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    gcongr
    · exact le_rfl
    · calc (∑' b, ν b) * ε' ≤ 1 * ε' := by gcongr; exact ν.mass_le_one
        _ = ε' := one_mul _
  have Hfg : ∀ a b, (S a b ∧ 0 < μ a ∧ 0 < ν b) →
      ARcoupl (F a) (K b) (adequacy_rel ϕ) (X2 b + ε') := by
    rintro a ⟨l, c⟩ ⟨hS, -, hpos⟩
    have hfront : is_frontier l [] osch := ⟨ρ, c, hpos⟩
    have hex : ∃ prel, prel <+: l ∧ is_frontier prel [] osch := ⟨l, List.prefix_refl _, hfront⟩
    have hK : K (l, c) = osch_lim_exec (full_info_lift_osch (Classical.choose hex)
        (f (Classical.choose hex))).fi_osch (l, c) := dite_eq_left hex
    have hc : Classical.choose hex = l :=
      is_frontier_prefix_lemma _ _ osch l (Classical.choose_spec hex).1
        (Classical.choose_spec hex).2 (List.prefix_refl _) hfront
    rw [hK, hc]
    have hex' : ∃ a ρ', S a (l, ρ') := ⟨a, c, hS⟩
    have hf : f l = g (Classical.choose hex') l (Classical.choose (Classical.choose_spec hex'))
        (Classical.choose_spec (Classical.choose_spec hex')) := dite_eq_left hex'
    rw [hf]
    have key : ∀ a0 ρ0 (h0 : S a0 (l, ρ0)), a0 = a → ρ0 = c →
        ARcoupl (F a) (osch_lim_exec (full_info_lift_osch l (g a0 l ρ0 h0)).fi_osch (l, c))
          (adequacy_rel ϕ) (X2 (l, c) + ε') := by
      rintro a0 ρ0 h0 rfl rfl
      have := full_info_lift_osch_lim_exec l (g a0 l ρ0 h0) [] ρ0
      simp only [List.append_nil] at this
      rw [this]
      exact ARcoupl_dmap_lift_r _ _ _ ϕ _ (hg a0 l ρ0 h0)
    obtain ⟨ha, hρ⟩ := Hinj _ _ _ _ _ (Classical.choose_spec (Classical.choose_spec hex')) hS
    exact key _ _ _ ha hρ
  have h1 := ARcoupl_dbind_adv_rhs' (fun b => X2 b + ε') F K μ ν _ (adequacy_rel ϕ) ε1 _ Hsum Hfg
    (ARcoupl_pos_R _ _ _ _ Hcoupl)
  have h2 := ARcoupl_eq_trans_r _ _ _ _ _ _ h1
    (ARcoupl_eq_0 _ _ (full_info_append_osch_lim_exec osch ρ f))
  rwa [add_zero, ← add_assoc] at h2

/-- Helper (the scheduler of the Rocq proof of `wp_adequacy_step_fupdN`): a first stutter step
choosing, according to `μ`, which scheduler to continue with. -/
theorem ARcoupl_cons_osch {A : Type} [Countable A] (μ : Distr A) (G : A → Distr val)
    (ρ : CPState) (ϕ : val → val → Prop) (ε : ℝ≥0∞)
    (H : ∀ a, 0 < μ a → ∃ fp : full_info_oscheduler,
      ARcoupl (G a) (osch_lim_exec fp.fi_osch ([], ρ)) (adequacy_rel ϕ) ε) :
    ∃ osch : full_info_oscheduler,
      ARcoupl (μ ≫= G) (osch_lim_exec osch.fi_osch ([], ρ)) (adequacy_rel ϕ) ε := by
  classical
  let f0 : A → full_info_oscheduler := fun a =>
    if h : 0 < μ a then Classical.choose (H a h) else full_info_inhabitant
  let f : ℕ → full_info_oscheduler := fun x =>
    match decode_nat (A := A) (x - ρ.1.length) with
    | some a => f0 a
    | none => full_info_inhabitant
  refine ⟨full_info_cons_osch (fun _ => dmap (fun a => ρ.1.length + encode_nat a) μ) f, ?_⟩
  have hlim : osch_lim_exec (full_info_cons_osch
        (fun _ => dmap (fun a => ρ.1.length + encode_nat a) μ) f).fi_osch ([], ρ) =
      μ ≫= fun a => dmap (fun p : full_info_state × CPState =>
        ([(cfg_to_cfg' ρ, ρ.1.length + encode_nat a)] ++ p.1, p.2))
        (osch_lim_exec (f0 a).fi_osch ([], ρ)) := by
    rw [full_info_cons_osch_lim_exec, dmap, ← dbind_assoc]
    refine dbind_ext_right _ _ _ fun a => ?_
    rw [dret_id_left, out_of_bounds_step' _ _ (Nat.le_add_right _ _), dret_id_left]
    have hf : f (ρ.1.length + encode_nat a) = f0 a := by
      simp only [f, Nat.add_sub_cancel_left, decode_encode_nat]
    rw [hf]
    have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, ρ.1.length + encode_nat a)] (f0 a) [] ρ
    simp only [List.append_nil] at this
    exact this
  rw [hlim, ← zero_add ε]
  refine ARcoupl_dbind _ _ μ μ _ _ 0 ε ?_ (ARcoupl_pos_R _ _ _ _ (ARcoupl_eq μ))
  rintro a _ ⟨rfl, hpos, -⟩
  refine ARcoupl_dmap_lift_r _ _ _ ϕ _ ?_
  have hf0 : f0 a = Classical.choose (H a hpos) := dite_eq_left hpos
  rw [hf0]
  exact Classical.choose_spec (H a hpos)

/-! ## Iris lemmas -/

section iris_step_helpers

variable {GF : BundledGFunctors} [InvGS_gen .hasNoLC GF]

/-- Helper: commuting a pure universal quantifier with a pure premise out of
`|={∅}=> |={∅}▷=>^n` (Rocq: `iIntros (ε'' Hε'')` through the modalities, by the `iris_ext`
`FromForall` instances). -/
theorem fupd_step_fupdN_forall_pure_wand {A : Type _} {p q : A → Prop} (n : ℕ) :
    (∀ x, ⌜p x⌝ -∗ |={∅}=> |={∅}[∅]▷=>^[n] ⌜q x⌝) ⊢@{IProp GF}
      |={∅}=> |={∅}[∅]▷=>^[n] ∀ x, ⌜p x⌝ -∗ ⌜q x⌝ := by
  iintro H
  ihave H := fupd_step_fupdN_pure_forall_imp (r := ∀ x, p x → q x) n id $$ H
  imod H
  imodintro
  iapply step_fupdN_mono _ $$ H
  iintro %H %x %hx
  ipureintro
  exact H x hx

omit [InvGS_gen .hasNoLC GF] in
/-- Helper: eliminating `∀ x, ⌜p x⌝ -∗ ⌜q x⌝` at a point. -/
theorem forall_pure_wand_elim {A : Type _} {p q : A → Prop} (x : A) (hx : p x) :
    (∀ x, ⌜p x⌝ -∗ ⌜q x⌝) ⊢@{IProp GF} ⌜q x⌝ := by
  iintro H
  iapply H $$ %x %hx

end iris_step_helpers

section iris_lemmas

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `step_fupd_fupdN_S`. -/
theorem step_fupd_fupdN_S (n : ℕ) (P : IProp GF) :
    (|={∅}[∅]▷=>^[n+1] P) ⊣⊢ |={∅}=> |={∅}[∅]▷=>^[n+1] P :=
  ⟨fupd_intro, BIFUpdate.trans⟩

/-- Rocq: `fupdN_S`. -/
theorem fupdN_S (n : ℕ) (P : IProp GF) :
    (|={∅}[∅]▷=>^[n+1] P) ⊣⊢ |={∅}[∅]▷=> |={∅}[∅]▷=>^[n] P := .rfl

/-- Helper: `spec_auth_prog_agree` for `spec_interp`. -/
theorem spec_interp_prog_agree (ρ : CPState) (j : ℕ) (e : expr) :
    ⊢@{IProp GF} spec_interp ρ -∗ j ⤇ e -∗ ⌜ρ.1[j]? = some e⌝ :=
  spec_auth_prog_agree ρ.1 ρ.2 j e

/-- Rocq: `fupd_later_mono`. -/
theorem fupd_later_mono (n : ℕ) (P Q : IProp GF) (H : P ⊢ Q) :
    (|={⊤,∅}=> |={∅}[∅]▷=> |={∅}[∅]▷=>^[n] P) ⊢ |={⊤,∅}=> |={∅}[∅]▷=> |={∅}[∅]▷=>^[n] Q :=
  BIFUpdate.mono (step_fupdN_mono (n := n + 1) H)

end iris_lemmas

/-! ## Adequacy -/

section adequacy

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {sch_int_σ : Type} [DecidableEq sch_int_σ] [Countable sch_int_σ]

/-- Rocq: `wp_adequacy_val_fupd`. -/
theorem wp_adequacy_val_fupd (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)
    (ζ : sch_int_σ) [TapeOblivious sch_int_σ sch] (σ : state) (ε : ℝ≥0∞) (e : expr)
    (es : List expr) (ρ : CPState) (n : ℕ) (v : val) (ϕ : val → val → Prop) (ε' : ℝ≥0∞)
    (Hε' : 0 < ε') (Hval : to_val e = some v) :
    (state_interp σ : IProp GF) ∗ err_interp ε ∗ spec_interp ρ ∗
        WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }} ⊢
      |={⊤,∅}=> ⌜∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (e :: es, σ))) (osch_lim_exec osch.fi_osch ([], ρ))
          (adequacy_rel ϕ) (ε + ε')⌝ := by
  obtain rfl : e = Val v := (of_to_val (Λ := con_prob_lang) e v Hval).symm
  rw [wp_unfold]
  simp only [wp_pre, to_val_Val]
  iintro ⟨Hσ, Hε, Hs, Hwp⟩
  imod Hwp $$ %σ %ρ %ε [Hσ Hs Hε] with H
  · iframe
  iapply spec_coupl_ind
    (fun σ ρ ε => iprop(∀ ε', ⌜0 < ε'⌝ -∗ |={∅}=> ⌜∃ osch : full_info_oscheduler,
      ARcoupl (sch_exec sch n (ζ, (Val v :: es, σ))) (osch_lim_exec osch.fi_osch ([], ρ))
        (adequacy_rel ϕ) (ε + ε')⌝)) _
    $$ [] %σ %ρ %ε H %ε' %Hε'
  iintro !> %σ1 %ρ1 %ε1 H %ε2 %Hε2
  icases H with (%H | H | H | ⟨%S, %μ, %osch, %ε3, %X2, %r, %Herasable, %Hr, %Hineq, %Hcoupl,
    %Hinj, H⟩)
  · imodintro
    ipureintro
    exact ⟨full_info_inhabitant, ARcoupl_1 _ _ _ _ (H.trans le_self_add)⟩
  · imod H with ⟨-, Hs, -, %v', Hj, %Hϕ⟩
    ihave %Hsome := spec_interp_prog_agree ρ1 0 (Val v') $$ Hs Hj
    iapply fupd_mask_intro_discard LawfulSet.empty_subset
    ipureintro
    refine ⟨full_info_inhabitant, ?_⟩
    rw [sch_exec_is_final sch _ v n rfl, full_info_inhabitant_lim_exec]
    exact ARcoupl_dret _ _ _ _ ⟨v', Hsome, Hϕ⟩
  · iapply fupd_pure_forall_imp (p := fun x : ℝ≥0∞ × ℝ≥0∞ => ε1 < x.1 ∧ 0 < x.2)
      (q := fun x => ∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (Val v :: es, σ1))) (osch_lim_exec osch.fi_osch ([], ρ1))
          (adequacy_rel ϕ) (x.1 + x.2))
      fun h => ARcoupl_amplify (P := fun e => ∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (Val v :: es, σ1))) (osch_lim_exec osch.fi_osch ([], ρ1))
          (adequacy_rel ϕ) e) ε1 ε2 Hε2
        (fun e he => ⟨full_info_inhabitant, ARcoupl_1 _ _ _ _ he⟩)
        (fun a ha b hb => h (a, b) ⟨ha, hb⟩)
    iintro %⟨ε4, ε5⟩ %⟨h1, h2⟩
    icases H $$ %ε4 %h1 with ⟨H, -⟩
    iapply H $$ %ε5 %h2
  · rw [← sch_erasable_sch_erasable_val tape_oblivious_sch μ σ1 Herasable sch_int_σ sch
      (Val v :: es) ζ n inferInstance]
    iapply fupd_pure_forall_imp
      (p := fun x : state × full_info_state × CPState => S x.1 (x.2.1, x.2.2))
      (q := fun x => ∃ fp : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (Val v :: es, x.1))) (osch_lim_exec fp.fi_osch ([], x.2.2))
          (adequacy_rel ϕ) (X2 (x.2.1, x.2.2) + ε2))
      fun h => by
        obtain ⟨o, Ho⟩ := ARcoupl_append_osch μ
          (fun σ2 => sch_exec sch n (ζ, (Val v :: es, σ2))) ρ1 osch S ε3 ε2 X2 ϕ Hcoupl
          (fun a1 a2 l r1 r2 h1 h2 => Hinj a1 a2 r1 r2 l h1 h2)
          (fun a l ρ' hS => h (a, l, ρ') hS)
        exact ⟨o, ARcoupl_mon_grading _ _ _ _ _ (add_le_add Hineq le_rfl) Ho⟩
    iintro %⟨σ2, l, ρ2⟩ %HS
    imod H $$ %σ2 %l %ρ2 %HS with ⟨H, -⟩
    iapply H $$ %ε2 %Hε2

/-- Rocq: `spec_coupl_erasure`. -/
theorem spec_coupl_erasure (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)
    (ζ : sch_int_σ) [TapeOblivious sch_int_σ sch] (σ : state) (ρ : CPState) (ε : ℝ≥0∞)
    (Z : state → CPState → ℝ≥0∞ → IProp GF) (ϕ : val → val → Prop) (n : ℕ) (e : expr)
    (es : List expr) (ε' : ℝ≥0∞) (Hε' : 0 < ε') :
    ⊢ spec_coupl σ ρ ε Z -∗
      (∀ σ2 ρ2 ε2, Z σ2 ρ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n] ∀ ε'', ⌜0 < ε''⌝ -∗
        ⌜∃ osch : full_info_oscheduler,
          ARcoupl (sch_exec sch n (ζ, (e :: es, σ2))) (osch_lim_exec osch.fi_osch ([], ρ2))
            (adequacy_rel ϕ) (ε2 + ε'')⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (e :: es, σ))) (osch_lim_exec osch.fi_osch ([], ρ))
          (adequacy_rel ϕ) (ε + ε')⌝ := by
  iintro H Hcont
  iapply spec_coupl_ind
    (fun σ ρ ε => iprop(∀ ε', ⌜0 < ε'⌝ -∗
      (∀ σ2 ρ2 ε2, Z σ2 ρ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n] ∀ ε'', ⌜0 < ε''⌝ -∗
        ⌜∃ osch : full_info_oscheduler,
          ARcoupl (sch_exec sch n (ζ, (e :: es, σ2))) (osch_lim_exec osch.fi_osch ([], ρ2))
            (adequacy_rel ϕ) (ε2 + ε'')⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (e :: es, σ))) (osch_lim_exec osch.fi_osch ([], ρ))
          (adequacy_rel ϕ) (ε + ε')⌝)) Z
    $$ [] %σ %ρ %ε H %ε' %Hε' Hcont
  iintro !> %σ1 %ρ1 %ε1 H %ε2 %Hε2 Hcont
  icases H with (%H | H | H | ⟨%S, %μ, %osch, %ε3, %X2, %r, %Herasable, %Hr, %Hineq, %Hcoupl,
    %Hinj, H⟩)
  · imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    exact ⟨full_info_inhabitant, ARcoupl_1 _ _ _ _ (H.trans le_self_add)⟩
  · imod Hcont $$ %σ1 %ρ1 %ε1 H with H
    imodintro
    iapply step_fupdN_mono (forall_pure_wand_elim ε2 Hε2) $$ H
  · iapply fupd_step_fupdN_pure_forall_imp (p := fun x : ℝ≥0∞ × ℝ≥0∞ => ε1 < x.1 ∧ 0 < x.2)
      (q := fun x => ∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (e :: es, σ1))) (osch_lim_exec osch.fi_osch ([], ρ1))
          (adequacy_rel ϕ) (x.1 + x.2)) n
      fun h => ARcoupl_amplify (P := fun e' => ∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (e :: es, σ1))) (osch_lim_exec osch.fi_osch ([], ρ1))
          (adequacy_rel ϕ) e') ε1 ε2 Hε2
        (fun e he => ⟨full_info_inhabitant, ARcoupl_1 _ _ _ _ he⟩)
        (fun a ha b hb => h (a, b) ⟨ha, hb⟩)
    iintro %⟨ε4, ε5⟩ %⟨h1, h2⟩
    icases H $$ %ε4 %h1 with ⟨H, -⟩
    iapply H $$ %ε5 %h2 Hcont
  · rw [← sch_erasable_sch_erasable_val tape_oblivious_sch μ σ1 Herasable sch_int_σ sch
      (e :: es) ζ n inferInstance]
    iapply fupd_step_fupdN_pure_forall_imp
      (p := fun x : state × full_info_state × CPState => S x.1 (x.2.1, x.2.2))
      (q := fun x => ∃ fp : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (e :: es, x.1))) (osch_lim_exec fp.fi_osch ([], x.2.2))
          (adequacy_rel ϕ) (X2 (x.2.1, x.2.2) + ε2)) n
      fun h => by
        obtain ⟨o, Ho⟩ := ARcoupl_append_osch μ
          (fun σ2 => sch_exec sch n (ζ, (e :: es, σ2))) ρ1 osch S ε3 ε2 X2 ϕ Hcoupl
          (fun a1 a2 l r1 r2 h1 h2 => Hinj a1 a2 r1 r2 l h1 h2)
          (fun a l ρ' hS => h (a, l, ρ') hS)
        exact ⟨o, ARcoupl_mon_grading _ _ _ _ _ (add_le_add Hineq le_rfl) Ho⟩
    iintro %⟨σ2, l, ρ2⟩ %HS
    imod H $$ %σ2 %l %ρ2 %HS with ⟨H, -⟩
    iapply H $$ %ε2 %Hε2 Hcont

/-- Rocq: `spec_coupl_erasure'`. -/
theorem spec_coupl_erasure' (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)
    (ζ : sch_int_σ) [TapeOblivious sch_int_σ sch] (σ : state) (ρ : CPState) (ε : ℝ≥0∞)
    (Z : state → CPState → ℝ≥0∞ → IProp GF) (ϕ : val → val → Prop) (n : ℕ) (e : expr)
    (es : List expr) (e' : expr) (num : ℕ) (ε' : ℝ≥0∞) (Hε' : 0 < ε')
    (Hlookup : (e :: es)[num]? = some e') (Hval1 : to_val e = none) (Hval2 : to_val e' = none) :
    ⊢ spec_coupl σ ρ ε Z -∗
      (∀ σ2 ρ2 ε2, Z σ2 ρ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n+1] ∀ ε'', ⌜0 < ε''⌝ -∗
        ⌜∃ osch : full_info_oscheduler,
          ARcoupl (prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
              sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
            (osch_lim_exec osch.fi_osch ([], ρ2)) (adequacy_rel ϕ) (ε2 + ε'')⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n+1] ⌜∃ osch : full_info_oscheduler,
        ARcoupl (prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
            sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
          (osch_lim_exec osch.fi_osch ([], ρ)) (adequacy_rel ϕ) (ε + ε')⌝ := by
  iintro H Hcont
  iapply spec_coupl_ind
    (fun σ ρ ε => iprop(∀ ε', ⌜0 < ε'⌝ -∗
      (∀ σ2 ρ2 ε2, Z σ2 ρ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n+1] ∀ ε'', ⌜0 < ε''⌝ -∗
        ⌜∃ osch : full_info_oscheduler,
          ARcoupl (prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
              sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
            (osch_lim_exec osch.fi_osch ([], ρ2)) (adequacy_rel ϕ) (ε2 + ε'')⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n+1] ⌜∃ osch : full_info_oscheduler,
        ARcoupl (prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
            sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
          (osch_lim_exec osch.fi_osch ([], ρ)) (adequacy_rel ϕ) (ε + ε')⌝)) Z
    $$ [] %σ %ρ %ε H %ε' %Hε' Hcont
  iintro !> %σ1 %ρ1 %ε1 H %ε2 %Hε2 Hcont
  icases H with (%H | H | H | ⟨%S, %μ, %osch, %ε3, %X2, %r, %Herasable, %Hr, %Hineq, %Hcoupl,
    %Hinj, H⟩)
  · imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    exact ⟨full_info_inhabitant, ARcoupl_1 _ _ _ _ (H.trans le_self_add)⟩
  · imod Hcont $$ %σ1 %ρ1 %ε1 H with H
    imodintro
    iapply step_fupdN_mono (forall_pure_wand_elim ε2 Hε2) $$ H
  · iapply fupd_step_fupdN_pure_forall_imp (p := fun x : ℝ≥0∞ × ℝ≥0∞ => ε1 < x.1 ∧ 0 < x.2)
      (q := fun x => ∃ osch : full_info_oscheduler,
        ARcoupl (prim_step (Λ := con_prob_lang) e' σ1 ≫= fun t =>
            sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
          (osch_lim_exec osch.fi_osch ([], ρ1)) (adequacy_rel ϕ) (x.1 + x.2)) (n+1)
      fun h => ARcoupl_amplify (P := fun e'' => ∃ osch : full_info_oscheduler,
        ARcoupl (prim_step (Λ := con_prob_lang) e' σ1 ≫= fun t =>
            sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
          (osch_lim_exec osch.fi_osch ([], ρ1)) (adequacy_rel ϕ) e'') ε1 ε2 Hε2
        (fun e he => ⟨full_info_inhabitant, ARcoupl_1 _ _ _ _ he⟩)
        (fun a ha b hb => h (a, b) ⟨ha, hb⟩)
    iintro %⟨ε4, ε5⟩ %⟨h1, h2⟩
    icases H $$ %ε4 %h1 with ⟨H, -⟩
    iapply H $$ %ε5 %h2 Hcont
  · rw [Rcoupl_eq_elim _ _ (prim_coupl_step_prim_sch_erasable e n es σ1 ζ e' num μ Herasable
      Hlookup Hval1 Hval2)]
    iapply fupd_step_fupdN_pure_forall_imp
      (p := fun x : state × full_info_state × CPState => S x.1 (x.2.1, x.2.2))
      (q := fun x => ∃ fp : full_info_oscheduler,
        ARcoupl (prim_step (Λ := con_prob_lang) e' x.1 ≫= fun t =>
            sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
          (osch_lim_exec fp.fi_osch ([], x.2.2)) (adequacy_rel ϕ) (X2 (x.2.1, x.2.2) + ε2)) (n+1)
      fun h => by
        obtain ⟨o, Ho⟩ := ARcoupl_append_osch μ
          (fun σ2 => prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
            sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) ρ1 osch S ε3 ε2 X2 ϕ
          Hcoupl (fun a1 a2 l r1 r2 h1 h2 => Hinj a1 a2 r1 r2 l h1 h2)
          (fun a l ρ' hS => h (a, l, ρ') hS)
        exact ⟨o, ARcoupl_mon_grading _ _ _ _ _ (add_le_add Hineq le_rfl) Ho⟩
    iintro %⟨σ2, l, ρ2⟩ %HS
    imod H $$ %σ2 %l %ρ2 %HS with ⟨H, -⟩
    iapply H $$ %ε2 %Hε2 Hcont

omit [DecidableEq sch_int_σ] in
/-- Rocq: `prog_coupl_erasure`. -/
theorem prog_coupl_erasure (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)
    (ζ : sch_int_σ) [TapeOblivious sch_int_σ sch] (σ : state) (ρ : CPState) (ε : ℝ≥0∞)
    (Z : expr → state → List expr → CPState → ℝ≥0∞ → IProp GF) (ϕ : val → val → Prop) (n : ℕ)
    (e : expr) (es : List expr) (e' : expr) (num : ℕ) (ε' : ℝ≥0∞) (Hε' : 0 < ε')
    (_Hlookup : (e :: es)[num]? = some e') (_Hval1 : to_val e = none) :
    ⊢ prog_coupl e' σ ρ ε Z -∗
      (∀ e2 σ2 efs ρ2 ε2, Z e2 σ2 efs ρ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n+1] ∀ ε'', ⌜0 < ε''⌝ -∗
        ⌜∃ osch : full_info_oscheduler,
          ARcoupl (sch_exec sch n (ζ, ((e :: es).set num e2 ++ efs, σ2)))
            (osch_lim_exec osch.fi_osch ([], ρ2)) (adequacy_rel ϕ) (ε2 + ε'')⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n+1] ⌜∃ osch : full_info_oscheduler,
        ARcoupl (prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
            sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1)))
          (osch_lim_exec osch.fi_osch ([], ρ)) (adequacy_rel ϕ) (ε + ε')⌝ := by
  iintro ⟨%S, %osch, %ε1, %X2, %r, %Hred, %Hr, %Hineq, %Hcoupl, %Hinj, H⟩ Hcont
  iapply fupd_step_fupdN_pure_forall_imp
    (p := fun x : (expr × state × List expr) × full_info_state × CPState => S x.1 (x.2.1, x.2.2))
    (q := fun x => ∃ fp : full_info_oscheduler,
      ARcoupl (sch_exec sch n (ζ, ((e :: es).set num x.1.1 ++ x.1.2.2, x.1.2.1)))
        (osch_lim_exec fp.fi_osch ([], x.2.2)) (adequacy_rel ϕ) (X2 (x.2.1, x.2.2) + ε')) (n+1)
    fun h => by
      obtain ⟨o, Ho⟩ := ARcoupl_append_osch (prim_step (Λ := con_prob_lang) e' σ)
        (fun t => sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) ρ osch S ε1 ε'
        X2 ϕ Hcoupl Hinj (fun a l ρ' hS => h (a, l, ρ') hS)
      exact ⟨o, ARcoupl_mon_grading _ _ _ _ _ (add_le_add Hineq le_rfl) Ho⟩
  iintro %⟨⟨e2, σ2, efs⟩, l, ρ2⟩ %HS
  imod H $$ %e2 %σ2 %efs %l %ρ2 %HS with H
  imod Hcont $$ %e2 %σ2 %efs %ρ2 %(X2 (l, ρ2)) H with H
  imodintro
  iapply step_fupdN_mono (forall_pure_wand_elim ε' Hε') $$ H

/-- Rocq: `wp_adequacy_step_fupdN`. -/
theorem wp_adequacy_step_fupdN (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)
    (ζ : sch_int_σ) [TapeOblivious sch_int_σ sch] (σ σ' : state) (ε : ℝ≥0∞) (e : expr)
    (es es' : List expr) (ϕ : val → val → Prop) (n : ℕ) (ε' : ℝ≥0∞) (Hε' : 0 < ε') :
    (state_interp σ : IProp GF) ∗ err_interp ε ∗ spec_interp ((es', σ') : CPState) ∗
        WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }} ∗
        ([∗list] e' ∈ es, WP e' {{ _v, True }}) ⊢
      |={⊤,∅}=> |={∅}[∅]▷=>^[n] ⌜∃ osch : full_info_oscheduler,
        ARcoupl (sch_exec sch n (ζ, (e :: es, σ)))
          (osch_lim_exec osch.fi_osch ([], ((es', σ') : CPState))) (adequacy_rel ϕ) (ε + ε')⌝ := by
  induction n generalizing ζ σ σ' ε e es es' ε' with
  | zero =>
    simp only [Nat.repeat]
    cases Heq : to_val e with
    | some v =>
      iintro ⟨Hσ, Hε, Hs, Hwp, -⟩
      iapply wp_adequacy_val_fupd sch ζ σ ε e es ((es', σ') : CPState) 0 v ϕ ε' Hε' Heq
      iframe
    | none =>
      iintro -
      iapply fupd_mask_intro_discard LawfulSet.empty_subset
      ipureintro
      refine ⟨full_info_inhabitant, ?_⟩
      rw [sch_exec_O_not_final _ _ (to_final_None_2 _ Heq)]
      exact ARcoupl_dzero _ _ _
  | succ n IH =>
    cases Heq : to_val e with
    | some v =>
      iintro ⟨Hσ, Hε, Hs, Hwp, -⟩
      imod wp_adequacy_val_fupd sch ζ σ ε e es ((es', σ') : CPState) (n+1) v ϕ ε' Hε' Heq $$ [Hσ Hε Hs Hwp] with %H
      · iframe
      imodintro
      iapply step_fupdN_intro LawfulSet.subset_refl
      iapply laterN_intro
      ipureintro
      exact H
    | none =>
      rw [sch_exec_Sn_not_final _ _ _ (to_final_None_2 _ Heq), sch_step, ← dbind_assoc]
      dsimp only
      iintro ⟨Hσ, Hε, Hs, Hwp, Hwps⟩
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hclose
      iapply (step_fupd_fupdN_S n _).2
      iapply fupd_step_fupdN_pure_forall_imp (p := fun a => 0 < sch (ζ, (e :: es, σ)) a)
        (q := fun a => ∃ fp : full_info_oscheduler,
          ARcoupl (dmap (fun c => (a.1, c)) ((con_lang_mdp con_prob_lang).step a.2 (e :: es, σ))
              ≫= sch_exec sch n)
            (osch_lim_exec fp.fi_osch ([], ((es', σ') : CPState))) (adequacy_rel ϕ) (ε + ε'))
        (n+1) fun h => by exact ARcoupl_cons_osch _ _ _ ϕ _ h
      iintro %⟨sch_σ, k⟩ %Hpos
      imod Hclose
      change ℕ at k
      dsimp only
      cases Hk : (e :: es)[k]? with
      | none =>
        -- step a thread that is out of bounds
        rw [con_prob_lang_mdp_step_stutter e es σ sch_σ k _ Heq (.inl Hk)]
        iapply fupd_mask_intro LawfulSet.empty_subset
        iintro Hclose
        simp only [Nat.repeat]
        iintro !> !>
        imod Hclose
        iapply IH sch_σ σ σ' ε e es es' ε' Hε'
        iframe
      | some e' =>
        cases Hv' : to_val e' with
        | some v =>
          -- step a thread that is a value
          rw [con_prob_lang_mdp_step_stutter e es σ sch_σ k _ Heq (.inr ⟨e', v, Hk, Hv'⟩)]
          iapply fupd_mask_intro LawfulSet.empty_subset
          iintro Hclose
          simp only [Nat.repeat]
          iintro !> !>
          imod Hclose
          iapply IH sch_σ σ σ' ε e es es' ε' Hε'
          iframe
        | none =>
          rw [con_prob_lang_mdp_step_prim e es e' σ sch_σ k _ Heq Hk Hv']
          cases k with
          | zero =>
            -- step the main thread
            obtain rfl : e = e' := Option.some.inj Hk
            imod wp_unfold_none Heq $$ Hwp %σ %((es', σ') : CPState) %ε [Hσ Hs Hε] with Hlift
            · iframe
            iapply spec_coupl_erasure' sch sch_σ σ ((es', σ') : CPState) ε _ ϕ n e es e 0 ε' Hε' rfl Heq Heq $$ Hlift
            iintro %σ2 %ρ2 %ε2 H
            iapply fupd_step_fupdN_forall_pure_wand (n+1)
            iintro %ε'' %Hε''
            iapply prog_coupl_erasure sch sch_σ σ2 ρ2 ε2 _ ϕ n e es e 0 ε'' Hε'' rfl Heq $$ H
            iintro %e3 %σ3 %efs %ρ3 %ε3 H
            simp only [Nat.repeat]
            iintro !> !> !>
            iapply fupd_step_fupdN_forall_pure_wand n
            iintro %ε''' %Hε'''
            simp only [List.set_cons_zero, List.cons_append]
            iapply spec_coupl_erasure sch sch_σ σ3 ρ3 ε3 _ ϕ n e3 (es ++ efs) ε''' Hε''' $$ H
            iintro %σ4 %ρ4 %ε4 H
            iapply fupd_step_fupdN_forall_pure_wand n
            iintro %ε'''' %Hε''''
            imod H with ⟨Hσ, Hs, Hε, Hwp, Hefs⟩
            have IH' := IH sch_σ σ4 ρ4.2 ε4 e3 (es ++ efs) ρ4.1 ε'''' Hε''''
            rw [show ((ρ4.1, ρ4.2) : CPState) = ρ4 from rfl] at IH'
            iapply IH'
            iframe Hσ Hs Hε Hwp
            iapply BigSepL.bigSepL_append.2
            iframe
          | succ k =>
            -- step another thread
            have Hk' : es[k]? = some e' := by simpa using Hk
            icases BigSepL.bigSepL_insert_acc (Φ := fun _ e' => iprop(WP e' {{ _v, True }})) Hk'
              $$ Hwps with ⟨Hwp', Hwps⟩
            imod wp_unfold_none Hv' $$ Hwp' %σ %((es', σ') : CPState) %ε [Hσ Hs Hε] with Hlift
            · iframe
            iapply spec_coupl_erasure' sch sch_σ σ ((es', σ') : CPState) ε _ ϕ n e es e' (k+1) ε' Hε' Hk Heq Hv'
              $$ Hlift
            iintro %σ2 %ρ2 %ε2 H
            iapply fupd_step_fupdN_forall_pure_wand (n+1)
            iintro %ε'' %Hε''
            iapply prog_coupl_erasure sch sch_σ σ2 ρ2 ε2 _ ϕ n e es e' (k+1) ε'' Hε'' Hk Heq $$ H
            iintro %e3 %σ3 %efs %ρ3 %ε3 H
            simp only [Nat.repeat]
            iintro !> !> !>
            iapply fupd_step_fupdN_forall_pure_wand n
            iintro %ε''' %Hε'''
            simp only [List.set_cons_succ, List.cons_append]
            iapply spec_coupl_erasure sch sch_σ σ3 ρ3 ε3 _ ϕ n e (es.set k e3 ++ efs) ε''' Hε'''
              $$ H
            iintro %σ4 %ρ4 %ε4 H
            iapply fupd_step_fupdN_forall_pure_wand n
            iintro %ε'''' %Hε''''
            imod H with ⟨Hσ, Hs, Hε, Hwp', Hefs⟩
            have IH' := IH sch_σ σ4 ρ4.2 ε4 e (es.set k e3 ++ efs) ρ4.1 ε'''' Hε''''
            rw [show ((ρ4.1, ρ4.2) : CPState) = ρ4 from rfl] at IH'
            iapply IH'
            iframe Hσ Hs Hε Hwp
            iapply BigSepL.bigSepL_append.2
            iframe Hefs
            iapply Hwps $$ Hwp'

end adequacy


/-! ## Adequacy theorems -/

/-- Rocq: `foxtrot_adequacy_full_info_intermediate_multi`. The hypothesis `0 <= ε` is dropped. -/
theorem foxtrot_adequacy_full_info_intermediate_multi (GF : BundledGFunctors) [foxtrotGpreS GF]
    (ε : ℝ≥0∞) (ϕ : val → val → Prop) (n : ℕ) (e : expr) (es es' : List expr)
    (Hwp : ∀ [foxtrotGS GF], ⊢@{IProp GF} ↯ ε -∗
      bigSepM (M := tpoolF) (fun n e => n ⤇ e) (to_tpool es') -∗
      (WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }} ∗ [∗list] e' ∈ es, WP e' {{ _v, True }}))
    (sch_int_σ : Type) [DecidableEq sch_int_σ] [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (ζ : sch_int_σ)
    [TapeOblivious sch_int_σ sch] (σ σ' : state) (ε' : ℝ≥0∞) (Hε' : 0 < ε') :
    ∃ osch : full_info_oscheduler,
      ARcoupl (sch_exec sch n (ζ, (e :: es, σ)))
        (osch_lim_exec osch.fi_osch ([], ((es', σ') : CPState))) (adequacy_rel ϕ) (ε + ε') := by
  -- Handle the trivial `1 ≤ ε` case
  by_cases hε : 1 ≤ ε
  · exact ⟨full_info_inhabitant, ARcoupl_1 _ _ _ _ (hε.trans le_self_add)⟩
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 fun Hinv => ?_
  iintro -
  imod ghost_map_alloc (GF := GF) (H := locF) σ.heap with ⟨%γH, Hh, -⟩
  imod ghost_map_alloc (GF := GF) (H := locF) σ.tapes with ⟨%γT, Ht, -⟩
  imod spec_ra_init (GF := GF) es' σ' with ⟨%HspecGS, Hs, Hj, -, -⟩
  imod ec_alloc ε (lt_of_not_ge hε) with ⟨%γec, HecAuth, Hec⟩
  let HfoxtrotGS : foxtrotGS GF :=
    { foxtrotGS_invG := Hinv
      foxtrotGS_heap := inferInstance
      foxtrotGS_tapes := inferInstance
      foxtrotGS_heap_name := γH
      foxtrotGS_tapes_name := γT
      foxtrotGS_spec := HspecGS
      foxtrotGS_error := { γec := γec } }
  ihave H := @Hwp HfoxtrotGS $$ Hec Hj
  icases H with ⟨Hwp, Hwps⟩
  iapply wp_adequacy_step_fupdN (GF := GF) sch ζ σ σ' ε e es es' ϕ n ε' Hε'
  iframe Hwp Hwps HecAuth
  simp only [foxtrotGS_state_interp_eq, heap_auth, tapes_auth]
  iframe

/-- Rocq: `foxtrot_adequacy_full_info_intermediate`. The hypothesis `0 <= ε` is dropped. -/
theorem foxtrot_adequacy_full_info_intermediate (GF : BundledGFunctors) [foxtrotGpreS GF]
    (ε : ℝ≥0∞) (ϕ : val → val → Prop) (n : ℕ) (e e' : expr)
    (Hwp : ∀ [foxtrotGS GF], ⊢@{IProp GF} ↯ ε -∗ 0 ⤇ e' -∗
      WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }})
    (sch_int_σ : Type) [DecidableEq sch_int_σ] [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (ζ : sch_int_σ)
    [TapeOblivious sch_int_σ sch] (σ σ' : state) (ε' : ℝ≥0∞) (Hε' : 0 < ε') :
    ∃ osch : full_info_oscheduler,
      ARcoupl (sch_exec sch n (ζ, ([e], σ)))
        (osch_lim_exec osch.fi_osch ([], (([e'], σ') : CPState))) (adequacy_rel ϕ) (ε + ε') := by
  refine foxtrot_adequacy_full_info_intermediate_multi GF ε ϕ n e [] [e'] ?_ sch_int_σ sch ζ σ σ'
    ε' Hε'
  intro _
  iintro Hε Hj
  isplitl
  · iapply Hwp $$ Hε
    have h : Iris.Std.get? (M := tpoolF) (to_tpool [e']) 0 = some e' := by
      rw [ext_get?_eq, tpool_lookup]; rfl
    iapply BigSepM.bigSepM_lookup (Φ := fun n e => iprop(n ⤇ e)) h $$ Hj
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `foxtrot_adequacy_intermediate`. The hypothesis `0 <= ε` is dropped. -/
theorem foxtrot_adequacy_intermediate (GF : BundledGFunctors) [foxtrotGpreS GF]
    (ε : ℝ≥0∞) (ϕ : val → val → Prop) (n : ℕ) (e e' : expr)
    (Hwp : ∀ [foxtrotGS GF], ⊢@{IProp GF} ↯ ε -∗ 0 ⤇ e' -∗
      WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }})
    (sch_int_σ : Type) [DecidableEq sch_int_σ] [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (ζ : sch_int_σ)
    [TapeOblivious sch_int_σ sch] (σ σ' : state) (ε' : ℝ≥0∞) (Hε' : 0 < ε') :
    ∃ (sch_int_σ' : Type) (_ : DecidableEq sch_int_σ') (_ : Countable sch_int_σ')
      (sch' : scheduler (con_lang_mdp con_prob_lang) sch_int_σ') (ζ' : sch_int_σ')
      (_ : TapeOblivious sch_int_σ' sch'),
      ARcoupl (sch_exec sch n (ζ, ([e], σ))) (sch_lim_exec sch' (ζ', (([e'], σ') : CPState))) ϕ
        (ε + ε') := by
  obtain ⟨osch, Hcoupl⟩ :=
    foxtrot_adequacy_full_info_intermediate GF ε ϕ n e e' Hwp sch_int_σ sch ζ σ σ' ε' Hε'
  obtain ⟨sch', Htape, Hle⟩ := osch_to_sch osch.fi_osch
  refine ⟨full_info_state, Classical.decEq _, inferInstance, sch', [], Htape, ?_⟩
  have h1 : ARcoupl (sch_exec sch n (ζ, ([e], σ)))
      (osch_lim_exec_val osch.fi_osch ([], (([e'], σ') : CPState))) ϕ (ε + ε') := by
    rw [osch_lim_exec_exec_val, ← dret_id_right (sch_exec sch n (ζ, ([e], σ)))]
    refine ARcoupl_dbind' (ε + ε') 0 _ (fun a => dret a) _ _ _ (adequacy_rel ϕ) ϕ
      (add_zero _).symm ?_ Hcoupl
    rintro v ⟨l, ρ⟩ ⟨v', Hsome, Hϕ⟩
    have Hfin : (con_lang_mdp con_prob_lang).to_final ρ = some v' := by
      simp [con_lang_mdp_to_final_eq, con_lang_mdp_to_final, Hsome]
    simp only [Hfin]
    exact ARcoupl_dret _ _ _ _ Hϕ
  have h2 := ARcoupl_eq_trans_r _ _ _ _ _ _ h1
    (ARcoupl_eq_0 _ _ (Hle ([], (([e'], σ') : CPState))))
  rwa [add_zero] at h2

/-- Rocq: `ARcoupl_lub`. Rocq's `Rbar_le a (Rbar_plus b ε)` is `a ≤ b + ε` in `ℝ≥0∞`. -/
theorem ARcoupl_lub (e e' : expr) (σ σ' : state) (ε : ℝ≥0∞) (ϕ : val → val → Prop)
    (H : ∀ (n : ℕ) (sch_int_σ : Type) [DecidableEq sch_int_σ] [Countable sch_int_σ]
      (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (ζ : sch_int_σ)
      [TapeOblivious sch_int_σ sch] (ε' : ℝ≥0∞), 0 < ε' →
      ∃ (sch_int_σ' : Type) (_ : DecidableEq sch_int_σ') (_ : Countable sch_int_σ')
        (sch' : scheduler (con_lang_mdp con_prob_lang) sch_int_σ') (ζ' : sch_int_σ')
        (_ : TapeOblivious sch_int_σ' sch'),
        ARcoupl (sch_exec sch n (ζ, ([e], σ))) (sch_lim_exec sch' (ζ', (([e'], σ') : CPState)))
          ϕ (ε + ε')) :
    lub_termination_prob e σ ≤ lub_termination_prob e' σ' + ε := by
  rw [lub_termination_sup_seq_termination_n]
  refine iSup_le fun n => sSup_le ?_
  rintro r ⟨p, rfl⟩
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  obtain ⟨X, hX1, hX2, sch', ζ', hT, Hc⟩ :=
    @H n p.sch_int_σ p.eqdec p.countable p.sch p.ζ p.tape_oblivious δ (by exact_mod_cast hδ)
  have Hm := ARcoupl_mass_leq _ _ _ _ Hc
  calc _ = ∑' v, sch_exec p.sch n (p.ζ, (([e], σ) : CPState)) v := rfl
    _ ≤ ∑' b, sch_lim_exec sch' (ζ', (([e'], σ') : CPState)) b + (ε + δ) := Hm
    _ ≤ lub_termination_prob e' σ' + (ε + δ) := by
        gcongr
        exact le_sSup (⟨⟨X, ζ', hX1, hX2, sch', hT⟩, rfl⟩ : termination_prob' e' σ' _)
    _ = lub_termination_prob e' σ' + ε + δ := (add_assoc _ _ _).symm

/-- Rocq: `foxtrot_adequacy`. The hypothesis `0 <= ε` is dropped; Rocq's
`Rbar_le a (Rbar_plus b ε)` is `a ≤ b + ε` in `ℝ≥0∞`. -/
theorem foxtrot_adequacy (GF : BundledGFunctors) [foxtrotGpreS GF] (ϕ : val → val → Prop)
    (e e' : expr) (σ σ' : state) (ε : ℝ≥0∞)
    (Hwp : ∀ [foxtrotGS GF], ⊢@{IProp GF} ↯ ε -∗ 0 ⤇ e' -∗
      WP e {{ v, ∃ v' : val, 0 ⤇ Val v' ∗ ⌜ϕ v v'⌝ }}) :
    lub_termination_prob e σ ≤ lub_termination_prob e' σ' + ε :=
  ARcoupl_lub e e' σ σ' ε ϕ fun n sch_int_σ _ _ sch ζ _ ε' Hε' =>
    foxtrot_adequacy_intermediate GF ε ϕ n e e' Hwp sch_int_σ sch ζ σ σ' ε' Hε'

end Foxtrot
