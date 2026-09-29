module

public import Metrology.ConProbLang.Lang

/-!
# Oblivious schedulers

Ported from clutch/theories/foxtrot/oscheduler.v

An *oblivious scheduler* (`oscheduler osch_state`) maps its internal state and the current
configuration of `con_lang_mdp con_prob_lang` either to `none` (stop) or to a distribution over
(next internal state, thread id). Unlike an ordinary `Prob.scheduler`, it may step any thread
(`step'`) even when the main thread is a value, and execution (`osch_exec`) stops when the
scheduler returns `none`, returning the whole configuration.

## Rocq → Lean map
* `step'`, `out_of_bounds_step'`, `oscheduler` (+ `CoeFun`, `oscheduler.coe_mk`), `osch_step`,
  `osch_step_or_none`, `osch_pexec`, `sch_opexec_fold`, `osch_exec`, `osch_lim_exec`,
  `osch_exec_val`, `osch_lim_exec_val`, `oTapeOblivious`, `osch_to_sch`, ...: same names.
* Types: configurations are `(con_lang_mdp con_prob_lang).mdpstate` (local notation `CPState`),
  thread ids of the scheduler are `(con_lang_mdp con_prob_lang).mdpaction` (`CPAct`), values
  `.mdpstate_ret` (`CPRet`); as in `ConProbLang/Lang.lean`, this keeps terms well-typed at
  reducible transparency. `step'` takes its thread id as `ℕ` (as in Rocq); when rewriting
  under an action `p.2 : CPAct`, use `congrArg`/`exact` rather than `rw`.
* `osch` is an explicit argument of every definition/lemma of the Rocq section `step`
  (Rocq: section `Context (osch : oscheduler)`), e.g. `osch_exec osch n ρ`.
* `to_final` is `(con_lang_mdp con_prob_lang).to_final`; `heap ρ.2` is `ρ.2.heap`;
  `<[α := t]>` on tapes is `(·.insert α t)`.
* `osch_exec` is defined by recursion on `n` with an inner match on `osch ρ` (Rocq matches on
  the pair `osch ρ, n`); the defining equations are `osch_exec_is_none`, `osch_exec_0`,
  `osch_exec_Sn`.
* Rocq `λ '(sch_σ', mdp_a), ...` is written with projections `p.1`, `p.2`; in
  `osch_exec_exec_val` / `osch_lim_exec_exec_val` the Rocq pattern lambdas `λ '(_, a'), ...` are
  kept (`fun ⟨_, a'⟩ => ...`).
* `S n` is `n + 1`; `is_Some x` is `∃ μ, x = some μ`.
* ENNReal: `Sup_seq` becomes `⨆ n`; the `is_finite (Sup_seq ...)` lemmas become `≠ ∞`;
  `SeriesC` becomes `∑'`; `(x > 0)%R` becomes `0 < x`; `r : R` becomes `r : ℝ≥0∞`.
* `oTapeOblivious` is a `class` with field `otape_oblivious`, explicit arguments
  `(osch_int_σ) (osch)` as in Rocq's `Global Arguments oTapeOblivious (_) {_ _} (_)`.

## Deviations
* Proofs are restructured for `ℝ≥0∞` (monotone convergence `tsum_iSup_of_monotone` instead of
  `MCT_seriesC` + finiteness side conditions, pointwise monotonicity instead of `refRcoupl`).
  `osch_exec_val_mono` follows directly from `osch_exec_mono`; `osch_exec_val_is_final` goes
  through the helper `osch_exec_to_final`; `osch_lim_exec_dmap_le` and
  `osch_lim_exec_exec_val` go through `lim_distr_dbind_pmf`.

## Added helpers (not in Rocq)
`step'_eq_step` (on a non-final configuration `step'` is the MDP step), `step'_to_final`
(`step'` preserves the value of a final main thread), `osch_exec_to_final`,
`lim_distr_dbind_pmf` (binding after a `lim_distr` is the supremum of the binds),
`oscheduler.coe_mk`.

## Omissions
* Commented-out Rocq lemmas are not ported (`osch_pexec_exec_le_final`, `osch_lim_exec_final`,
  `osch_exec_val_pexec_relate`, ...), nor the commented-out `oscheduler_inhabited` /
  `oTapeOblivious_inhabitant`.
* `Global Arguments oscheduler (_) {_ _}`: in Lean `oscheduler osch_state` already takes the
  state type explicitly and the `Countable` instance implicitly (no `EqDecision` is needed).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate
set_option quotPrecheck false in
/-- The return type of `con_lang_mdp con_prob_lang` (reducibly `val`). -/
local notation "CPRet" => (con_lang_mdp con_prob_lang).mdpstate_ret
set_option quotPrecheck false in
/-- The action type of `con_lang_mdp con_prob_lang` (reducibly `ℕ`). -/
local notation "CPAct" => (con_lang_mdp con_prob_lang).mdpaction

/-- Rocq: `step'`. Unlike a scheduler step, we can take steps of other threads even if the
first thread is a value. -/
def step' (n : ℕ) (ρ : CPState) : Distr CPState :=
  match ρ.1[n]? with
  | none => -- thread id exceeds the number of threads, so we stutter
    dret ρ
  | some e =>
    match ConProbLang.to_val (Λ := con_prob_lang) e with
    | some _ => -- `e` is a value, so we stutter
      dret ρ
    | none => dmap (fun p => (ρ.1.set n p.1 ++ p.2.2, p.2.1)) (prim_step e ρ.2)

/-- Rocq: `out_of_bounds_step'`. -/
theorem out_of_bounds_step' (n : ℕ) (ρ : CPState) (h : ρ.1.length ≤ n) : step' n ρ = dret ρ := by
  unfold step'
  rw [List.getElem?_eq_none h]

/-- Helper (not in Rocq): on a non-final configuration, `step'` is the step of
`con_lang_mdp con_prob_lang`. -/
theorem step'_eq_step (n : ℕ) (ρ : CPState)
    (h : (con_lang_mdp con_prob_lang).to_final ρ = none) :
    step' n ρ = (con_lang_mdp con_prob_lang).step n ρ := by
  change con_lang_mdp_to_final con_prob_lang ρ = none at h
  unfold con_lang_mdp_to_final at h
  change step' n ρ = con_lang_mdp_step con_prob_lang n ρ
  unfold con_lang_mdp_step
  have h0 : (ρ.1[0]? >>= ConProbLang.to_val (Λ := con_prob_lang)) = none := by
    split at h <;> simp_all
  rw [h0]
  simp only [step']
  split <;> rename_i h1 <;> simp only [h1]
  · exact rfl
  · split <;> rename_i h2 <;> simp only [h2] <;> exact rfl

/-- Helper (not in Rocq): `step'` preserves the final value of the main thread. -/
theorem step'_to_final (n : ℕ) (ρ ρ' : CPState) (b : CPRet)
    (H : (con_lang_mdp con_prob_lang).to_final ρ = some b) (h : 0 < step' n ρ ρ') :
    (con_lang_mdp con_prob_lang).to_final ρ' = some b := by
  obtain ⟨l, s⟩ := ρ
  change con_lang_mdp_to_final con_prob_lang (l, s) = some b at H
  unfold con_lang_mdp_to_final at H
  change con_lang_mdp_to_final con_prob_lang ρ' = some b
  unfold step' at h
  dsimp only at h H
  cases h0 : l[0]? with
  | none => rw [h0] at H; cases H
  | some e0 =>
    rw [h0] at H
    dsimp only at H
    split at h
    · obtain rfl := dret_pos _ _ h
      unfold con_lang_mdp_to_final; rw [h0]; exact H
    · rename_i e hn
      split at h
      · obtain rfl := dret_pos _ _ h
        unfold con_lang_mdp_to_final; rw [h0]; exact H
      · rename_i hv
        obtain ⟨p, rfl, -⟩ := (dmap_pos _ _ _).1 h
        have hn0 : n ≠ 0 := by
          rintro rfl
          rw [h0] at hn
          cases hn
          rw [H] at hv
          cases hv
        have hlen : 0 < l.length := by
          rcases l with _ | ⟨x, l⟩
          · simp at h0
          · simp
        unfold con_lang_mdp_to_final
        dsimp only
        rw [List.getElem?_append_left (by simpa using hlen), List.getElem?_set_ne hn0, h0]
        exact H

/-- Helper (not in Rocq): the monotone-convergence identity for binding after a `lim_distr`. -/
theorem lim_distr_dbind_pmf {α β : Type*} [Countable α] [Countable β] (h : ℕ → Distr α)
    (Hmon : ∀ n a, h n a ≤ h (n + 1) a) (f : α → Distr β) (b : β) :
    (lim_distr h Hmon ≫= f) b = ⨆ n, (h n ≫= f) b := by
  simp only [dbind_unfold_pmf, lim_distr_pmf, ENNReal.iSup_mul]
  exact tsum_iSup_of_monotone fun a =>
    monotone_nat_of_le_succ fun n => mul_le_mul' (Hmon n a) le_rfl

section oscheduler

universe v

variable {osch_state : Type v} [Countable osch_state]

/-- Rocq: `oscheduler`. An oblivious scheduler: given its internal state and the current
configuration, either stops (`none`) or returns a distribution over the next internal state and
the thread to step. -/
structure oscheduler (osch_state : Type v) [Countable osch_state] where
  oscheduler_f : osch_state × CPState → Option (Distr (osch_state × CPAct))

instance : CoeFun (oscheduler osch_state)
    (fun _ => osch_state × CPState → Option (Distr (osch_state × CPAct))) :=
  ⟨oscheduler.oscheduler_f⟩

@[simp] theorem oscheduler.coe_mk (f : osch_state × CPState → Option (Distr (osch_state × CPAct)))
    (ρ : osch_state × CPState) : (⟨f⟩ : oscheduler osch_state) ρ = f ρ := rfl

/-! Everything below is dependent on an instance of an oscheduler. -/

variable (osch : oscheduler osch_state)

section step

/-- Rocq: `osch_step`. -/
def osch_step (ρ : osch_state × CPState) : Distr (osch_state × CPState) :=
  match osch ρ with
  | some μ => μ ≫= fun p => dmap (fun mdp_σ' : CPState => (p.1, mdp_σ')) (step' p.2 ρ.2)
  | none => dzero

/-- Rocq: `osch_step_or_none`. -/
def osch_step_or_none (a : osch_state × CPState) : Distr (osch_state × CPState) :=
  match osch a with
  | some _ => osch_step osch a
  | none => dret a

/-- Rocq: `osch_step_or_none_is_none`. -/
theorem osch_step_or_none_is_none (ρ : osch_state × CPState) (h : osch ρ = none) :
    osch_step_or_none osch ρ = dret ρ := by
  unfold osch_step_or_none; rw [h]

/-- Rocq: `osch_pexec`. -/
def osch_pexec (n : ℕ) (p : osch_state × CPState) : Distr (osch_state × CPState) :=
  iterM n (osch_step_or_none osch) p

/-- Rocq: `sch_opexec_fold`. -/
theorem sch_opexec_fold (n : ℕ) (p : osch_state × CPState) :
    iterM n (osch_step_or_none osch) p = osch_pexec osch n p := rfl

/-- Rocq: `osch_pexec_O`. -/
theorem osch_pexec_O (a : osch_state × CPState) : osch_pexec osch 0 a = dret a := rfl

/-- Rocq: `osch_pexec_Sn`. -/
theorem osch_pexec_Sn (a : osch_state × CPState) (n : ℕ) :
    osch_pexec osch (n + 1) a = osch_step_or_none osch a ≫= osch_pexec osch n := rfl

/-- Rocq: `osch_pexec_plus`. -/
theorem osch_pexec_plus (ρ : osch_state × CPState) (n m : ℕ) :
    osch_pexec osch (n + m) ρ = osch_pexec osch n ρ ≫= osch_pexec osch m :=
  iterM_plus _ _ _ _

/-- Rocq: `osch_pexec_1`. -/
theorem osch_pexec_1 : osch_pexec osch 1 = osch_step_or_none osch := by
  funext a
  rw [osch_pexec_Sn]
  exact dret_id_right _

/-- Rocq: `osch_pexec_Sn_r`. -/
theorem osch_pexec_Sn_r (a : osch_state × CPState) (n : ℕ) :
    osch_pexec osch (n + 1) a = osch_pexec osch n a ≫= osch_step_or_none osch := by
  rw [osch_pexec_plus, osch_pexec_1]

/-- Rocq: `osch_pexec_det_steps`. -/
theorem osch_pexec_det_steps (n m : ℕ) (a1 a2 : osch_state × CPState)
    (h : osch_pexec osch n a1 a2 = 1) :
    osch_pexec osch n a1 ≫= osch_pexec osch m = osch_pexec osch m a2 := by
  rw [pmf_1_eq_dret _ _ h, dret_id_left]

/-- Rocq: `osch_exec`. Returns the whole configuration once the scheduler stops. -/
def osch_exec : ℕ → osch_state × CPState → Distr (osch_state × CPState)
  | 0, ρ =>
    match osch ρ with
    | none => dret ρ
    | some _ => dzero
  | n + 1, ρ =>
    match osch ρ with
    | none => dret ρ
    | some μ => μ ≫= fun p => step' p.2 ρ.2 ≫= fun mdp_σ' => osch_exec n (p.1, mdp_σ')

/-- Rocq: `osch_exec_is_none`. -/
theorem osch_exec_is_none (ρ : osch_state × CPState) (n : ℕ) (h : osch ρ = none) :
    osch_exec osch n ρ = dret ρ := by
  cases n <;> simp only [osch_exec, h]

/-- Rocq: `osch_exec_0`. -/
theorem osch_exec_0 (ρ : osch_state × CPState) (h : ∃ μ, osch ρ = some μ) :
    osch_exec osch 0 ρ = dzero := by
  obtain ⟨μ, h⟩ := h
  simp only [osch_exec, h]

/-- Rocq: `osch_exec_Sn`. -/
theorem osch_exec_Sn (a : osch_state × CPState) (n : ℕ) :
    osch_exec osch (n + 1) a = osch_step_or_none osch a ≫= osch_exec osch n := by
  cases h : osch a with
  | none =>
    rw [osch_step_or_none_is_none _ _ h, dret_id_left, osch_exec_is_none _ _ _ h,
      osch_exec_is_none _ _ _ h]
  | some μ =>
    simp only [osch_exec, osch_step_or_none, osch_step, h]
    rw [← dbind_assoc]
    refine dbind_ext_right _ _ _ fun p => ?_
    rw [dmap, ← dbind_assoc]
    exact dbind_ext_right _ _ _ fun _ => (dret_id_left _ _).symm

/-- Rocq: `osch_exec_plus`. -/
theorem osch_exec_plus (a : osch_state × CPState) (n1 n2 : ℕ) :
    osch_exec osch (n1 + n2) a = osch_pexec osch n1 a ≫= osch_exec osch n2 := by
  induction n1 generalizing a with
  | zero => rw [osch_pexec_O, dret_id_left, Nat.zero_add]
  | succ n1 ih =>
    rw [Nat.add_right_comm, osch_exec_Sn, osch_pexec_Sn, ← dbind_assoc]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `osch_exec_pexec_relate`. -/
theorem osch_exec_pexec_relate (a : osch_state × CPState) (n : ℕ) :
    osch_exec osch n a = osch_pexec osch n a ≫=
      (fun e => match osch e with
        | none => dret e
        | some _ => dzero) := by
  induction n generalizing a with
  | zero =>
    rw [osch_pexec_O, dret_id_left]
    cases h : osch a <;> simp only [osch_exec, h]
  | succ n ih =>
    rw [osch_exec_Sn, osch_pexec_Sn, ← dbind_assoc]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `osch_exec_pos`. -/
theorem osch_exec_pos (n : ℕ) (a b : osch_state × CPState) (h : 0 < osch_exec osch n a b) :
    osch b = none := by
  rw [osch_exec_pexec_relate, dbind_pos] at h
  obtain ⟨e, h1, -⟩ := h
  split at h1
  · rename_i he
    obtain rfl := dret_pos _ _ h1
    exact he
  · exact absurd h1 (dzero_supp_empty _)

/-- Rocq: `osch_exec_mono`. -/
theorem osch_exec_mono (a : osch_state × CPState) (n : ℕ) (v : osch_state × CPState) :
    osch_exec osch n a v ≤ osch_exec osch (n + 1) a v := by
  induction n generalizing a with
  | zero =>
    cases h : osch a with
    | none => rw [osch_exec_is_none _ _ _ h, osch_exec_is_none _ _ _ h]
    | some μ => rw [osch_exec_0 _ _ ⟨μ, h⟩, dzero_0]; exact zero_le
  | succ n ih =>
    rw [osch_exec_Sn, osch_exec_Sn, dbind_unfold_pmf, dbind_unfold_pmf]
    exact ENNReal.tsum_le_tsum fun a' => mul_le_mul' le_rfl (ih a')

/-- Rocq: `osch_exec_mono'`. -/
theorem osch_exec_mono' (ρ : osch_state × CPState) (n m : ℕ) (v : osch_state × CPState)
    (h : n ≤ m) : osch_exec osch n ρ v ≤ osch_exec osch m ρ v :=
  monotone_nat_of_le_succ (f := fun x => osch_exec osch x ρ v)
    (fun k => osch_exec_mono osch ρ k v) h

/-- Rocq: `osch_exec_mono_term`. -/
theorem osch_exec_mono_term (a b : osch_state × CPState) (n m : ℕ)
    (Hv : ∑' b, osch_exec osch n a b = 1) (Hleq : n ≤ m) :
    osch_exec osch m a b = osch_exec osch n a b := by
  refine le_antisymm ?_ (osch_exec_mono' osch a n m b Hleq)
  by_contra hlt
  push Not at hlt
  have : ∑' b, osch_exec osch n a b < ∑' b, osch_exec osch m a b :=
    ENNReal.tsum_lt_tsum (SeriesC_ne_top _) (fun b' => osch_exec_mono' osch a n m b' Hleq) hlt
  rw [Hv] at this
  exact absurd (osch_exec osch m a).mass_le_one (not_le.2 this)

/-- Rocq: `is_finite_Sup_seq_osch_exec`. -/
theorem is_finite_Sup_seq_osch_exec (a b : osch_state × CPState) :
    ⨆ n, osch_exec osch n a b ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => pmf_le_1 _ _)

/-- Rocq: `is_finite_Sup_seq_SeriesC_osch_exec`. -/
theorem is_finite_Sup_seq_SeriesC_osch_exec (a : osch_state × CPState) :
    ⨆ n, ∑' b, osch_exec osch n a b ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => pmf_SeriesC _)

/-! ### Full evaluation (limit of stratification) -/

/-- Rocq: `osch_lim_exec`. -/
def osch_lim_exec (ρ : osch_state × CPState) : Distr (osch_state × CPState) :=
  lim_distr (fun n => osch_exec osch n ρ) (fun n v => osch_exec_mono osch ρ n v)

/-- Rocq: `osch_lim_exec_unfold`. -/
theorem osch_lim_exec_unfold (a b : osch_state × CPState) :
    osch_lim_exec osch a b = ⨆ n, osch_exec osch n a b := rfl

/-- Rocq: `osch_lim_exec_is_sup`. -/
theorem osch_lim_exec_is_sup (n : ℕ) (a b : osch_state × CPState) :
    osch_exec osch n a b ≤ osch_lim_exec osch a b :=
  le_iSup (fun m => osch_exec osch m a b) n

/-- Rocq: `osch_lim_exec_dmap_le`. -/
theorem osch_lim_exec_dmap_le {B : Type*} [Countable B] (f : osch_state × CPState → B)
    (a : osch_state × CPState) (b : B) (r : ℝ≥0∞)
    (H1 : ∀ n, dmap f (osch_exec osch n a) b ≤ r) : dmap f (osch_lim_exec osch a) b ≤ r := by
  unfold dmap osch_lim_exec
  rw [lim_distr_dbind_pmf]
  exact iSup_le H1

/-- Rocq: `osch_lim_exec_Sup_seq`. -/
theorem osch_lim_exec_Sup_seq (a : osch_state × CPState) :
    ∑' b, osch_lim_exec osch a b = ⨆ n, ∑' b, osch_exec osch n a b := by
  simp only [osch_lim_exec_unfold]
  exact tsum_iSup_of_monotone fun b =>
    monotone_nat_of_le_succ fun n => osch_exec_mono osch a n b

/-- Rocq: `osch_lim_exec_step`. -/
theorem osch_lim_exec_step (a : osch_state × CPState) :
    osch_lim_exec osch a = osch_step_or_none osch a ≫= osch_lim_exec osch := by
  ext b
  rw [dbind_unfold_pmf, osch_lim_exec_unfold]
  simp only [osch_lim_exec_unfold, ENNReal.mul_iSup]
  rw [tsum_iSup_of_monotone
    (f := fun n a' => osch_step_or_none osch a a' * osch_exec osch n a' b)
    fun a' => monotone_nat_of_le_succ fun n => mul_le_mul' le_rfl (osch_exec_mono osch a' n b)]
  simp only [← dbind_unfold_pmf, ← osch_exec_Sn]
  exact (Monotone.iSup_nat_add (f := fun n => osch_exec osch n a b)
    (monotone_nat_of_le_succ fun n => osch_exec_mono osch a n b) 1).symm

/-- Rocq: `osch_lim_exec_pexec`. -/
theorem osch_lim_exec_pexec (n : ℕ) (a : osch_state × CPState) :
    osch_lim_exec osch a = osch_pexec osch n a ≫= osch_lim_exec osch := by
  induction n generalizing a with
  | zero => rw [osch_pexec_O, dret_id_left]
  | succ n ih =>
    rw [osch_pexec_Sn, ← dbind_assoc, osch_lim_exec_step]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `osch_lim_exec_None`. -/
theorem osch_lim_exec_None (a : osch_state × CPState) (h : osch a = none) :
    osch_lim_exec osch a = dret a := by
  ext b
  simp only [osch_lim_exec_unfold, osch_exec_is_none _ _ _ h, iSup_const]

/-- Rocq: `osch_lim_exec_leq`. -/
theorem osch_lim_exec_leq (a b : osch_state × CPState) (r : ℝ≥0∞)
    (Hexec : ∀ n, osch_exec osch n a b ≤ r) : osch_lim_exec osch a b ≤ r :=
  iSup_le Hexec

/-- Rocq: `osch_lim_exec_leq_mass`. -/
theorem osch_lim_exec_leq_mass (a : osch_state × CPState) (r : ℝ≥0∞)
    (Hm : ∀ n, ∑' b, osch_exec osch n a b ≤ r) : ∑' b, osch_lim_exec osch a b ≤ r := by
  rw [osch_lim_exec_Sup_seq]
  exact iSup_le Hm

/-- Rocq: `osch_lim_exec_term`. -/
theorem osch_lim_exec_term (n : ℕ) (a : osch_state × CPState)
    (Hv : ∑' b, osch_exec osch n a b = 1) : osch_lim_exec osch a = osch_exec osch n a := by
  ext b
  rw [osch_lim_exec_unfold]
  refine le_antisymm (iSup_le fun n' => ?_) (le_iSup (fun m => osch_exec osch m a b) n)
  rcases le_total n n' with h | h
  · exact (osch_exec_mono_term osch a b n n' Hv h).le
  · exact osch_exec_mono' osch a n' n b h

/-- Rocq: `osch_lim_exec_pos`. -/
theorem osch_lim_exec_pos (a b : osch_state × CPState) (h : 0 < osch_lim_exec osch a b) :
    ∃ n, 0 < osch_exec osch n a b := by
  rw [osch_lim_exec_unfold] at h
  exact lt_iSup_iff.1 h

/-- Rocq: `osch_lim_exec_pos_res`. -/
theorem osch_lim_exec_pos_res (x y : osch_state × CPState) (H : 0 < osch_lim_exec osch x y) :
    osch y = none := by
  obtain ⟨n, H⟩ := osch_lim_exec_pos osch x y H
  exact osch_exec_pos osch n x y H

/-- Rocq: `osch_lim_exec_continuous_prob`. -/
theorem osch_lim_exec_continuous_prob (a : osch_state × CPState)
    (ϕ : osch_state × CPState → Bool) (r : ℝ≥0∞)
    (Hm : ∀ n, prob (osch_exec osch n a) ϕ ≤ r) : prob (osch_lim_exec osch a) ϕ ≤ r := by
  unfold prob at Hm ⊢
  have Haux : ∀ v, (if ϕ v then osch_lim_exec osch a v else 0) =
      ⨆ n, if ϕ v then osch_exec osch n a v else 0 := by
    intro v
    cases ϕ v <;> simp [osch_lim_exec_unfold]
  simp only [Haux]
  rw [tsum_iSup_of_monotone]
  · exact iSup_le Hm
  · intro v
    refine monotone_nat_of_le_succ fun n => ?_
    cases ϕ v
    · exact le_rfl
    · exact osch_exec_mono osch a n v

/-! `osch_exec_val` returns the value if final. -/

/-- Rocq: `osch_exec_val`. -/
def osch_exec_val (n : ℕ) (ρ : osch_state × CPState) : Distr CPRet :=
  osch_exec osch n ρ ≫= fun ρ =>
    match (con_lang_mdp con_prob_lang).to_final ρ.2 with
    | some v => dret v
    | none => dzero

/-- Rocq: `osch_exec_val_not_final_None`. -/
theorem osch_exec_val_not_final_None (ρ : osch_state × CPState) (n : ℕ)
    (h1 : (con_lang_mdp con_prob_lang).to_final ρ.2 = none) (h2 : osch ρ = none) :
    osch_exec_val osch n ρ = dzero := by
  unfold osch_exec_val
  rw [osch_exec_is_none _ _ _ h2, dret_id_left]
  simp only [h1]

/-- Rocq: `osch_exec_val_Sn`. -/
theorem osch_exec_val_Sn (a : osch_state × CPState) (n : ℕ) :
    osch_exec_val osch (n + 1) a = osch_step_or_none osch a ≫= osch_exec_val osch n := by
  unfold osch_exec_val
  rw [osch_exec_Sn, ← dbind_assoc]

/-- Rocq: `osch_exec_val_plus`. -/
theorem osch_exec_val_plus (a : osch_state × CPState) (n1 n2 : ℕ) :
    osch_exec_val osch (n1 + n2) a = osch_pexec osch n1 a ≫= osch_exec_val osch n2 := by
  induction n1 generalizing a with
  | zero => rw [osch_pexec_O, dret_id_left, Nat.zero_add]
  | succ n1 ih =>
    rw [Nat.add_right_comm, osch_exec_val_Sn, osch_pexec_Sn, ← dbind_assoc]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `osch_exec_val_mono`. -/
theorem osch_exec_val_mono (a : osch_state × CPState) (n : ℕ) (v : CPRet) :
    osch_exec_val osch n a v ≤ osch_exec_val osch (n + 1) a v := by
  unfold osch_exec_val
  rw [dbind_unfold_pmf, dbind_unfold_pmf]
  exact ENNReal.tsum_le_tsum fun a' => mul_le_mul' (osch_exec_mono osch a n a') le_rfl

/-- Rocq: `osch_exec_val_mono'`. -/
theorem osch_exec_val_mono' (ρ : osch_state × CPState) (n m : ℕ) (v : CPRet) (h : n ≤ m) :
    osch_exec_val osch n ρ v ≤ osch_exec_val osch m ρ v :=
  monotone_nat_of_le_succ (f := fun x => osch_exec_val osch x ρ v)
    (fun k => osch_exec_val_mono osch ρ k v) h

/-- Rocq: `osch_exec_val_mono_term`. -/
theorem osch_exec_val_mono_term (a : osch_state × CPState) (b : CPRet) (n m : ℕ)
    (Hv : ∑' b, osch_exec_val osch n a b = 1) (Hleq : n ≤ m) :
    osch_exec_val osch m a b = osch_exec_val osch n a b := by
  refine le_antisymm ?_ (osch_exec_val_mono' osch a n m b Hleq)
  by_contra hlt
  push Not at hlt
  have : ∑' b, osch_exec_val osch n a b < ∑' b, osch_exec_val osch m a b :=
    ENNReal.tsum_lt_tsum (SeriesC_ne_top _) (fun b' => osch_exec_val_mono' osch a n m b' Hleq) hlt
  rw [Hv] at this
  exact absurd (osch_exec_val osch m a).mass_le_one (not_le.2 this)

/-- Rocq: `osch_exec_val_is_final_None`. -/
theorem osch_exec_val_is_final_None (a : osch_state × CPState) (b : CPRet) (m : ℕ)
    (H : (con_lang_mdp con_prob_lang).to_final a.2 = some b) (h : osch a = none) :
    osch_exec_val osch m a b = 1 := by
  unfold osch_exec_val
  rw [osch_exec_is_none _ _ _ h, dret_id_left]
  simp only [H]
  exact dret_1_1 _ _ rfl

/-- Helper (not in Rocq): every configuration reached by `osch_exec` from a final
configuration is final with the same value. -/
theorem osch_exec_to_final (n : ℕ) (a y : osch_state × CPState) (b : CPRet)
    (H : (con_lang_mdp con_prob_lang).to_final a.2 = some b) (h : 0 < osch_exec osch n a y) :
    (con_lang_mdp con_prob_lang).to_final y.2 = some b := by
  induction n generalizing a with
  | zero =>
    cases hs : osch a with
    | none =>
      rw [osch_exec_is_none _ _ _ hs] at h
      obtain rfl := dret_pos _ _ h
      exact H
    | some μ =>
      rw [osch_exec_0 _ _ ⟨μ, hs⟩] at h
      exact absurd h (dzero_supp_empty _)
  | succ n ih =>
    cases hs : osch a with
    | none =>
      rw [osch_exec_is_none _ _ _ hs] at h
      obtain rfl := dret_pos _ _ h
      exact H
    | some μ =>
      simp only [osch_exec, hs] at h
      obtain ⟨p, h1, -⟩ := (dbind_pos _ _ _).1 h
      obtain ⟨σ', h2, h3⟩ := (dbind_pos _ _ _).1 h1
      exact ih (p.1, σ') (step'_to_final p.2 a.2 σ' b H h3) h2

/-- Rocq: `osch_exec_val_is_final`. -/
theorem osch_exec_val_is_final (a : osch_state × CPState) (b : CPRet) (m : ℕ)
    (H : (con_lang_mdp con_prob_lang).to_final a.2 = some b) (x : CPRet) :
    osch_exec_val osch m a x ≤ dret b x := by
  unfold osch_exec_val
  rw [dbind_unfold_pmf]
  calc _ ≤ ∑' y, osch_exec osch m a y * dret b x := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        rcases eq_or_ne (osch_exec osch m a y) 0 with h0 | h0
        · simp [h0]
        · rw [osch_exec_to_final osch m a y b H (pos_iff_ne_zero.2 h0)]
    _ = (∑' y, osch_exec osch m a y) * dret b x := ENNReal.tsum_mul_right
    _ ≤ 1 * dret b x := mul_le_mul' (pmf_SeriesC _) le_rfl
    _ = dret b x := one_mul _

/-- Rocq: `is_finite_Sup_seq_osch_exec_val`. -/
theorem is_finite_Sup_seq_osch_exec_val (a : osch_state × CPState) (b : CPRet) :
    ⨆ n, osch_exec_val osch n a b ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => pmf_le_1 _ _)

/-- Rocq: `is_finite_Sup_seq_SeriesC_osch_exec_val`. -/
theorem is_finite_Sup_seq_SeriesC_osch_exec_val (a : osch_state × CPState) :
    ⨆ n, ∑' b, osch_exec_val osch n a b ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => pmf_SeriesC _)

/-! ### Full evaluation (limit of stratification) -/

/-- Rocq: `osch_lim_exec_val`. -/
def osch_lim_exec_val (ρ : osch_state × CPState) : Distr CPRet :=
  lim_distr (fun n => osch_exec_val osch n ρ) (fun n v => osch_exec_val_mono osch ρ n v)

/-- Rocq: `osch_lim_exec_val_unfold`. -/
theorem osch_lim_exec_val_unfold (a : osch_state × CPState) (b : CPRet) :
    osch_lim_exec_val osch a b = ⨆ n, osch_exec_val osch n a b := rfl

/-- Rocq: `osch_lim_exec_val_Sup_seq`. -/
theorem osch_lim_exec_val_Sup_seq (a : osch_state × CPState) :
    ∑' b, osch_lim_exec_val osch a b = ⨆ n, ∑' b, osch_exec_val osch n a b := by
  simp only [osch_lim_exec_val_unfold]
  exact tsum_iSup_of_monotone fun b =>
    monotone_nat_of_le_succ fun n => osch_exec_val_mono osch a n b

/-- Rocq: `osch_lim_exec_val_step`. -/
theorem osch_lim_exec_val_step (a : osch_state × CPState) :
    osch_lim_exec_val osch a = osch_step_or_none osch a ≫= osch_lim_exec_val osch := by
  ext b
  rw [dbind_unfold_pmf, osch_lim_exec_val_unfold]
  simp only [osch_lim_exec_val_unfold, ENNReal.mul_iSup]
  rw [tsum_iSup_of_monotone
    (f := fun n a' => osch_step_or_none osch a a' * osch_exec_val osch n a' b)
    fun a' => monotone_nat_of_le_succ fun n =>
      mul_le_mul' le_rfl (osch_exec_val_mono osch a' n b)]
  simp only [← dbind_unfold_pmf, ← osch_exec_val_Sn]
  exact (Monotone.iSup_nat_add (f := fun n => osch_exec_val osch n a b)
    (monotone_nat_of_le_succ fun n => osch_exec_val_mono osch a n b) 1).symm

/-- Rocq: `osch_lim_exec_val_pexec`. -/
theorem osch_lim_exec_val_pexec (n : ℕ) (a : osch_state × CPState) :
    osch_lim_exec_val osch a = osch_pexec osch n a ≫= osch_lim_exec_val osch := by
  induction n generalizing a with
  | zero => rw [osch_pexec_O, dret_id_left]
  | succ n ih =>
    rw [osch_pexec_Sn, ← dbind_assoc, osch_lim_exec_val_step]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `osch_lim_exec_val_final`. -/
theorem osch_lim_exec_val_final (a : osch_state × CPState) (b : CPRet)
    (H : (con_lang_mdp con_prob_lang).to_final a.2 = some b) (h : osch a = none) :
    osch_lim_exec_val osch a b = 1 :=
  le_antisymm (pmf_le_1 _ _)
    (le_iSup_of_le 0 (osch_exec_val_is_final_None osch a b 0 H h).symm.le)

/-- Rocq: `osch_lim_exec_val_leq`. -/
theorem osch_lim_exec_val_leq (a : osch_state × CPState) (b : CPRet) (r : ℝ≥0∞)
    (Hexec : ∀ n, osch_exec_val osch n a b ≤ r) : osch_lim_exec_val osch a b ≤ r :=
  iSup_le Hexec

/-- Rocq: `osch_lim_exec_val_leq_mass`. -/
theorem osch_lim_exec_val_leq_mass (a : osch_state × CPState) (r : ℝ≥0∞)
    (Hm : ∀ n, ∑' b, osch_exec_val osch n a b ≤ r) : ∑' b, osch_lim_exec_val osch a b ≤ r := by
  rw [osch_lim_exec_val_Sup_seq]
  exact iSup_le Hm

/-- Rocq: `osch_lim_exec_val_term`. -/
theorem osch_lim_exec_val_term (n : ℕ) (a : osch_state × CPState)
    (Hv : ∑' b, osch_exec_val osch n a b = 1) :
    osch_lim_exec_val osch a = osch_exec_val osch n a := by
  ext b
  rw [osch_lim_exec_val_unfold]
  refine le_antisymm (iSup_le fun n' => ?_) (le_iSup (fun m => osch_exec_val osch m a b) n)
  rcases le_total n n' with h | h
  · exact (osch_exec_val_mono_term osch a b n n' Hv h).le
  · exact osch_exec_val_mono' osch a n' n b h

/-- Rocq: `osch_lim_exec_val_pos`. -/
theorem osch_lim_exec_val_pos (a : osch_state × CPState) (b : CPRet)
    (h : 0 < osch_lim_exec_val osch a b) : ∃ n, 0 < osch_exec_val osch n a b := by
  rw [osch_lim_exec_val_unfold] at h
  exact lt_iSup_iff.1 h

/-- Rocq: `osch_lim_exec_val_continuous_prob`. -/
theorem osch_lim_exec_val_continuous_prob (a : osch_state × CPState) (ϕ : CPRet → Bool)
    (r : ℝ≥0∞) (Hm : ∀ n, prob (osch_exec_val osch n a) ϕ ≤ r) :
    prob (osch_lim_exec_val osch a) ϕ ≤ r := by
  unfold prob at Hm ⊢
  have Haux : ∀ v, (if ϕ v then osch_lim_exec_val osch a v else 0) =
      ⨆ n, if ϕ v then osch_exec_val osch n a v else 0 := by
    intro v
    cases ϕ v <;> simp [osch_lim_exec_val_unfold]
  simp only [Haux]
  rw [tsum_iSup_of_monotone]
  · exact iSup_le Hm
  · intro v
    refine monotone_nat_of_le_succ fun n => ?_
    cases ϕ v
    · exact le_rfl
    · exact osch_exec_val_mono osch a n v

/-- Rocq: `osch_lim_exec_val_is_final`. -/
theorem osch_lim_exec_val_is_final (a : osch_state × CPState) (b : CPRet)
    (H : (con_lang_mdp con_prob_lang).to_final a.2 = some b) (x : CPRet) :
    osch_lim_exec_val osch a x ≤ dret b x :=
  iSup_le fun n => osch_exec_val_is_final osch a b n H x

/-- Rocq: `osch_exec_exec_val`. -/
theorem osch_exec_exec_val (a : osch_state × CPState) (n : ℕ) :
    osch_exec_val osch n a = osch_exec osch n a ≫= (fun ⟨_, a'⟩ =>
      match (con_lang_mdp con_prob_lang).to_final a' with
      | some b => dret b
      | none => dzero) := rfl

/-- Rocq: `osch_lim_exec_exec_val`. -/
theorem osch_lim_exec_exec_val (a : osch_state × CPState) :
    osch_lim_exec_val osch a = osch_lim_exec osch a ≫= (fun ⟨_, a'⟩ =>
      match (con_lang_mdp con_prob_lang).to_final a' with
      | some b => dret b
      | none => dzero) := by
  ext b
  unfold osch_lim_exec
  rw [lim_distr_dbind_pmf, osch_lim_exec_val_unfold]
  simp only [osch_exec_exec_val]

end step

end oscheduler

/-! ## Oblivious-scheduler type classes -/

section osch_typeclasses

/-- Rocq: `oTapeOblivious`. -/
class oTapeOblivious (osch_int_σ : Type*) [Countable osch_int_σ]
    (osch : oscheduler osch_int_σ) : Prop where
  otape_oblivious : ∀ (ζ : osch_int_σ) (ρ ρ' : CPState), ρ.1 = ρ'.1 → ρ.2.heap = ρ'.2.heap →
    osch (ζ, ρ) = osch (ζ, ρ')

/-- Rocq: `osch_tape_oblivious`. -/
theorem osch_tape_oblivious {si : Type*} [Countable si] {osch : oscheduler si}
    [oTapeOblivious si osch] (ζ : si) (ρ ρ' : CPState) (h1 : ρ.1 = ρ'.1)
    (h2 : ρ.2.heap = ρ'.2.heap) : osch (ζ, ρ) = osch (ζ, ρ') :=
  oTapeOblivious.otape_oblivious ζ ρ ρ' h1 h2

/-- Rocq: `osch_tape_oblivious_state_upd_tapes`. -/
theorem osch_tape_oblivious_state_upd_tapes {si : Type*} [Countable si] {osch : oscheduler si}
    [oTapeOblivious si osch] (ζ : si) (α : Loc) (t : tape) (σ : state) (es : List expr) :
    osch (ζ, ((es, state_upd_tapes (·.insert α t) σ) : CPState)) =
      osch (ζ, ((es, σ) : CPState)) :=
  osch_tape_oblivious ζ _ _ rfl rfl

end osch_typeclasses

/-- Rocq: `osch_to_sch`. Every tape-oblivious oblivious scheduler is dominated by a
tape-oblivious (ordinary) scheduler. -/
theorem osch_to_sch {osch_int_σ : Type*} [Countable osch_int_σ] (osch : oscheduler osch_int_σ)
    [Htape : oTapeOblivious osch_int_σ osch] :
    ∃ sch : scheduler (con_lang_mdp con_prob_lang) osch_int_σ,
      TapeOblivious osch_int_σ sch ∧
        ∀ x y, osch_lim_exec_val osch x y ≤ sch_lim_exec sch x y := by
  let sch : scheduler (con_lang_mdp con_prob_lang) osch_int_σ :=
    ⟨fun x => match osch x with | some d => d | none => dzero⟩
  refine ⟨sch, ⟨fun ζ ρ ρ' h1 h2 => ?_⟩, ?_⟩
  · simp only [sch]
    rw [Htape.otape_oblivious ζ ρ ρ' h1 h2]
  · rintro ⟨o, m⟩ v
    apply osch_lim_exec_val_leq
    intro n
    induction n generalizing o m v with
    | zero =>
      cases hf : (con_lang_mdp con_prob_lang).to_final m with
      | some v' =>
        rw [sch_lim_exec_final _ _ _ hf]
        exact osch_exec_val_is_final osch _ v' 0 hf v
      | none =>
        cases hs : osch (o, m) with
        | none =>
          rw [osch_exec_val_not_final_None osch _ 0 hf hs, dzero_0]; exact zero_le
        | some μ =>
          unfold osch_exec_val
          rw [osch_exec_0 osch _ ⟨μ, hs⟩, dbind_dzero, dzero_0]; exact zero_le
    | succ n ih =>
      cases hf : (con_lang_mdp con_prob_lang).to_final m with
      | some v' =>
        rw [sch_lim_exec_final _ _ _ hf]
        exact osch_exec_val_is_final osch _ v' (n + 1) hf v
      | none =>
        cases hs : osch (o, m) with
        | none =>
          rw [osch_exec_val_not_final_None osch _ _ hf hs, dzero_0]; exact zero_le
        | some μ =>
          rw [osch_exec_val_Sn, sch_lim_exec_not_final _ _ (to_final_None_2 _ hf)]
          have hsch : sch (o, m) = μ := by simp only [sch, hs]
          have hstep : osch_step_or_none osch (o, m) = sch_step sch (o, m) := by
            simp only [osch_step_or_none, osch_step, sch_step, hs, hsch]
            refine dbind_ext_right _ _ _ fun p => ?_
            exact congrArg (dmap _) (step'_eq_step p.2 m hf)
          rw [hstep]
          exact distr_le_dbind _ _ _ _ (distr_le_refl _) (fun x w => ih x.1 x.2 w) v

end Foxtrot
