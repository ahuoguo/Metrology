module

public import Metrology.Prob.Distribution

/-!
# Markov decision processes and schedulers

Ported from clutch/theories/prob/mdp.v

An `mdp` bundles a state type, a return type and an action type, together with a step
function `step : mdpaction → mdpstate → Distr mdpstate` and a partial `to_final` function.
A `scheduler δ sch_state` chooses (a distribution of) actions, carrying an internal state.

Compared with the Rocq development:
* `is_Some x` is `∃ b, x = some b`;
* `EqDecision` / `Countable` fields become `DecidableEq` / `Countable` instance fields;
* Rocq's `λ '(sch_σ', mdp_a), ...` in `sch_step` is written with projections `p.1`, `p.2`;
* the three carriers of `mdp` live in independent universes (`mdp.{u, w, x}`: state, return
  and action types respectively), as in Rocq where no relation between them is imposed;
* `Sup_seq` of reals becomes `⨆ n, _` in `ℝ≥0∞`; the Rocq `is_finite (Sup_seq ...)` lemmas
  become `≠ ∞` statements.

Note on `prob/markov.v`: it is not ported. Its only importer among the Coneris / Foxtrot /
`con_prob_lang` sources is `con_prob_lang/typing/contextual_refinement.v`, which uses nothing
from it (the `From clutch.prob Require Import markov` line is dead); porters should simply drop
that import.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Prob

universe u v w x

/-! ## Markov decision process -/

section mdp_mixin

variable {mdpstate mdpstate_ret mdpaction : Type*} [Countable mdpstate]

/-- Rocq: `MdpMixin`. -/
structure MdpMixin (step : mdpaction → mdpstate → Distr mdpstate)
    (to_final : mdpstate → Option mdpstate_ret) : Prop where
  mixin_to_final_is_final :
    ∀ a, (∃ b, to_final a = some b) → ∀ ac a', step ac a a' = 0

end mdp_mixin

/-- Rocq: `mdp`. -/
structure mdp where
  mdpstate : Type u
  mdpstate_ret : Type w
  mdpaction : Type x
  mdpstate_eqdec : DecidableEq mdpstate
  mdpstate_count : Countable mdpstate
  mdpstate_ret_eqdec : DecidableEq mdpstate_ret
  mdpstate_ret_count : Countable mdpstate_ret
  mdpaction_eqdec : DecidableEq mdpaction
  mdpaction_count : Countable mdpaction
  step : mdpaction → mdpstate → Distr mdpstate
  to_final : mdpstate → Option mdpstate_ret
  mdp_mixin : MdpMixin step to_final

attribute [instance] mdp.mdpstate_eqdec mdp.mdpstate_count mdp.mdpstate_ret_eqdec
  mdp.mdpstate_ret_count mdp.mdpaction_eqdec mdp.mdpaction_count

export mdp (step to_final)

/-! ## Schedulers -/

section scheduler

variable {δ : mdp.{u, w, x}} {sch_state : Type v} [Countable sch_state]

/-- Rocq: `scheduler`. -/
structure scheduler (δ : mdp.{u, w, x}) (sch_state : Type v) [Countable sch_state] where
  scheduler_f : sch_state × δ.mdpstate → Distr (sch_state × δ.mdpaction)

instance : CoeFun (scheduler δ sch_state)
    (fun _ => sch_state × δ.mdpstate → Distr (sch_state × δ.mdpaction)) :=
  ⟨scheduler.scheduler_f⟩

@[simp] theorem scheduler.coe_mk (f : sch_state × δ.mdpstate → Distr (sch_state × δ.mdpaction))
    (ρ : sch_state × δ.mdpstate) : (⟨f⟩ : scheduler δ sch_state) ρ = f ρ := rfl

/-- Rocq: `sch_int_state_f`. -/
def sch_int_state_f (s : scheduler δ sch_state) (ρ : sch_state × δ.mdpstate) :
    Distr sch_state := lmarg (s ρ)

/-- Rocq: `sch_action_f`. -/
def sch_action_f (s : scheduler δ sch_state) (ρ : sch_state × δ.mdpstate) :
    Distr δ.mdpaction := rmarg (s ρ)

section is_final

/-- Rocq: `to_final_is_final`. -/
theorem to_final_is_final (a : δ.mdpstate) (h : ∃ b, δ.to_final a = some b) :
    ∀ ac a', δ.step ac a a' = 0 :=
  δ.mdp_mixin.mixin_to_final_is_final a h

/-- Rocq: `is_final`. -/
def is_final (a : δ.mdpstate) : Prop := ∃ b, δ.to_final a = some b

/-- Rocq: `to_final_None`. -/
theorem to_final_None (a : δ.mdpstate) : ¬ is_final a ↔ δ.to_final a = none := by
  unfold is_final
  cases δ.to_final a <;> simp

/-- Rocq: `to_final_None_1`. -/
theorem to_final_None_1 (a : δ.mdpstate) (h : ¬ is_final a) : δ.to_final a = none :=
  (to_final_None a).1 h

/-- Rocq: `to_final_None_2`. -/
theorem to_final_None_2 (a : δ.mdpstate) (h : δ.to_final a = none) : ¬ is_final a :=
  (to_final_None a).2 h

/-- Rocq: `to_final_Some`. -/
theorem to_final_Some (a : δ.mdpstate) : is_final a ↔ ∃ b, δ.to_final a = some b := Iff.rfl

/-- Rocq: `to_final_Some_1`. -/
theorem to_final_Some_1 (a : δ.mdpstate) (h : is_final a) : ∃ b, δ.to_final a = some b := h

/-- Rocq: `to_final_Some_2`. -/
theorem to_final_Some_2 (a : δ.mdpstate) (b : δ.mdpstate_ret) (h : δ.to_final a = some b) :
    is_final a := ⟨b, h⟩

/-- Rocq: `is_final_dzero`. -/
theorem is_final_dzero (a : δ.mdpstate) (ac : δ.mdpaction) (h : is_final a) :
    δ.step ac a = dzero :=
  distr_ext fun a' => to_final_is_final a h ac a'

/-- Rocq: `is_final_dec`. -/
instance is_final_dec (a : δ.mdpstate) : Decidable (is_final a) :=
  decidable_of_iff (¬ δ.to_final a = none) (by rw [← to_final_None, not_not])

end is_final

/-! Everything below depends on a scheduler (and an mdp). -/

variable (sch : scheduler δ sch_state)

section reducible

/-- Rocq: `reducible`. -/
def reducible (ρ : sch_state × δ.mdpstate) : Prop :=
  ∃ ac a', 0 < sch_action_f sch ρ ac ∧ 0 < δ.step ac ρ.2 a'

/-- Rocq: `irreducible`. -/
def irreducible (ρ : sch_state × δ.mdpstate) : Prop :=
  ∀ ac a', sch_action_f sch ρ ac = 0 ∨ δ.step ac ρ.2 a' = 0

/-- Rocq: `stuck`. -/
def stuck (a : sch_state × δ.mdpstate) : Prop := ¬ is_final a.2 ∧ irreducible sch a

/-- Rocq: `not_stuck`. -/
def not_stuck (a : sch_state × δ.mdpstate) : Prop := is_final a.2 ∨ reducible sch a

/-- Rocq: `not_reducible`. -/
theorem not_reducible (a : sch_state × δ.mdpstate) : ¬ reducible sch a ↔ irreducible sch a := by
  unfold reducible irreducible
  simp only [not_exists, not_and, pos_iff_ne_zero, ne_eq, not_not]
  constructor
  · intro H ac a'
    by_cases h : sch_action_f sch a ac = 0
    · exact Or.inl h
    · exact Or.inr (H ac a' h)
  · intro H ac a' h
    exact (H ac a').resolve_left h

/-- Rocq: `reducible_not_final`. -/
theorem reducible_not_final (a : sch_state × δ.mdpstate) (h : reducible sch a) :
    ¬ is_final a.2 := by
  intro hf
  obtain ⟨ac, a', _, h2⟩ := h
  rw [is_final_dzero _ ac hf] at h2
  simp at h2

/-- Rocq: `is_final_irreducible`. -/
theorem is_final_irreducible (a : sch_state × δ.mdpstate) (h : is_final a.2) :
    irreducible sch a := fun ac a' => Or.inr (by rw [is_final_dzero _ ac h]; rfl)

/-- Rocq: `not_not_stuck`. -/
theorem not_not_stuck (a : sch_state × δ.mdpstate) : ¬ not_stuck sch a ↔ stuck sch a := by
  unfold stuck not_stuck
  rw [← not_reducible]
  tauto

/-- Rocq: `reducible_not_stuck`. -/
theorem reducible_not_stuck (a : sch_state × δ.mdpstate) (h : reducible sch a) :
    not_stuck sch a := Or.inr h

end reducible

section step

/-- Rocq: `sch_step`. Takes a strict step and returns the whole configuration, including the
scheduler state. -/
def sch_step (ρ : sch_state × δ.mdpstate) : Distr (sch_state × δ.mdpstate) :=
  sch ρ ≫= fun p => dmap (fun mdp_σ' => (p.1, mdp_σ')) (δ.step p.2 ρ.2)

/-- Rocq: `sch_stepN`. -/
def sch_stepN (n : ℕ) (p : sch_state × δ.mdpstate) : Distr (sch_state × δ.mdpstate) :=
  iterM n (sch_step sch) p

/-- Rocq: `sch_stepN_O`. -/
theorem sch_stepN_O : sch_stepN sch 0 = dret := rfl

/-- Rocq: `sch_stepN_Sn`. -/
theorem sch_stepN_Sn (a : sch_state × δ.mdpstate) (n : ℕ) :
    sch_stepN sch (n + 1) a = sch_step sch a ≫= sch_stepN sch n := rfl

/-- Rocq: `sch_stepN_1`. -/
theorem sch_stepN_1 (a : sch_state × δ.mdpstate) : sch_stepN sch 1 a = sch_step sch a := by
  rw [sch_stepN_Sn, sch_stepN_O, dret_id_right]

/-- Rocq: `sch_stepN_plus`. -/
theorem sch_stepN_plus (a : sch_state × δ.mdpstate) (n m : ℕ) :
    sch_stepN sch (n + m) a = sch_stepN sch n a ≫= sch_stepN sch m :=
  iterM_plus _ _ _ _

/-- Rocq: `sch_stepN_Sn_inv`. -/
theorem sch_stepN_Sn_inv (n : ℕ) (a0 a2 : sch_state × δ.mdpstate)
    (h : 0 < sch_stepN sch (n + 1) a0 a2) :
    ∃ a1, 0 < sch_step sch a0 a1 ∧ 0 < sch_stepN sch n a1 a2 := by
  rw [sch_stepN_Sn, dbind_pos] at h
  obtain ⟨a1, h1, h2⟩ := h
  exact ⟨a1, h2, h1⟩

/-- Rocq: `sch_stepN_det_steps`. -/
theorem sch_stepN_det_steps (n m : ℕ) (a1 a2 : sch_state × δ.mdpstate)
    (h : sch_stepN sch n a1 a2 = 1) :
    sch_stepN sch n a1 ≫= sch_stepN sch m = sch_stepN sch m a2 := by
  rw [pmf_1_eq_dret _ _ h, dret_id_left]

/-- Rocq: `sch_stepN_det_trans`. -/
theorem sch_stepN_det_trans (n m : ℕ) (a1 a2 a3 : sch_state × δ.mdpstate)
    (h1 : sch_stepN sch n a1 a2 = 1) (h2 : sch_stepN sch m a2 a3 = 1) :
    sch_stepN sch (n + m) a1 a3 = 1 := by
  rw [sch_stepN_plus, pmf_1_eq_dret _ _ h1, dret_id_left, pmf_1_eq_dret _ _ h2]
  exact dret_1_1 _ _ rfl

/-- Rocq: `sch_step_or_final`. Does a non-strict step and returns the whole configuration. -/
def sch_step_or_final (a : sch_state × δ.mdpstate) : Distr (sch_state × δ.mdpstate) :=
  match δ.to_final a.2 with
  | some _ => dret a
  | none => sch_step sch a

/-- Rocq: `sch_step_or_final_is_final`. -/
theorem sch_step_or_final_is_final (ρ : sch_state × δ.mdpstate) (h : is_final ρ.2) :
    sch_step_or_final sch ρ = dret ρ := by
  obtain ⟨b, hb⟩ := h
  unfold sch_step_or_final
  rw [hb]

/-- Rocq: `sch_step_or_final_not_final`. -/
theorem sch_step_or_final_not_final (ρ : sch_state × δ.mdpstate) (h : ¬ is_final ρ.2) :
    sch_step_or_final sch ρ = sch_step sch ρ := by
  unfold sch_step_or_final
  rw [to_final_None_1 _ h]

/-- Rocq: `sch_pexec`. -/
def sch_pexec (n : ℕ) (p : sch_state × δ.mdpstate) : Distr (sch_state × δ.mdpstate) :=
  iterM n (sch_step_or_final sch) p

/-- Rocq: `sch_pexec_fold`. -/
theorem sch_pexec_fold (n : ℕ) (p : sch_state × δ.mdpstate) :
    iterM n (sch_step_or_final sch) p = sch_pexec sch n p := rfl

/-- Rocq: `sch_pexec_O`. -/
theorem sch_pexec_O (a : sch_state × δ.mdpstate) : sch_pexec sch 0 a = dret a := rfl

/-- Rocq: `sch_pexec_Sn`. -/
theorem sch_pexec_Sn (a : sch_state × δ.mdpstate) (n : ℕ) :
    sch_pexec sch (n + 1) a = sch_step_or_final sch a ≫= sch_pexec sch n := rfl

/-- Rocq: `sch_pexec_plus`. -/
theorem sch_pexec_plus (ρ : sch_state × δ.mdpstate) (n m : ℕ) :
    sch_pexec sch (n + m) ρ = sch_pexec sch n ρ ≫= sch_pexec sch m :=
  iterM_plus _ _ _ _

/-- Rocq: `sch_pexec_1`. -/
theorem sch_pexec_1 : sch_pexec sch 1 = sch_step_or_final sch := by
  funext a
  rw [sch_pexec_Sn]
  exact dret_id_right _

/-- Rocq: `sch_pexec_Sn_r`. -/
theorem sch_pexec_Sn_r (a : sch_state × δ.mdpstate) (n : ℕ) :
    sch_pexec sch (n + 1) a = sch_pexec sch n a ≫= sch_step_or_final sch := by
  rw [sch_pexec_plus, sch_pexec_1]

/-- Rocq: `sch_pexec_is_final`. -/
theorem sch_pexec_is_final (n : ℕ) (a : sch_state × δ.mdpstate) (h : is_final a.2) :
    sch_pexec sch n a = dret a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sch_pexec_Sn, sch_step_or_final_is_final _ _ h, dret_id_left, ih]

/-- Rocq: `sch_pexec_det_steps`. -/
theorem sch_pexec_det_steps (n m : ℕ) (a1 a2 : sch_state × δ.mdpstate)
    (h : sch_pexec sch n a1 a2 = 1) :
    sch_pexec sch n a1 ≫= sch_pexec sch m = sch_pexec sch m a2 := by
  rw [pmf_1_eq_dret _ _ h, dret_id_left]

/-- Rocq: `sch_exec`. Takes non-strict steps and returns the final `mdpstate_ret`
(in a language setting, the value). -/
def sch_exec : ℕ → sch_state × δ.mdpstate → Distr δ.mdpstate_ret
  | 0, ρ =>
    match δ.to_final ρ.2 with
    | some b => dret b
    | none => dzero
  | n + 1, ρ =>
    match δ.to_final ρ.2 with
    | some b => dret b
    | none => sch_step sch ρ ≫= sch_exec n

/-- Rocq: `sch_exec_is_final`. -/
theorem sch_exec_is_final (ρ : sch_state × δ.mdpstate) (b : δ.mdpstate_ret) (n : ℕ)
    (h : δ.to_final ρ.2 = some b) : sch_exec sch n ρ = dret b := by
  cases n <;> simp only [sch_exec, h]

/-- Rocq: `sch_exec_Sn`. -/
theorem sch_exec_Sn (a : sch_state × δ.mdpstate) (n : ℕ) :
    sch_exec sch (n + 1) a = sch_step_or_final sch a ≫= sch_exec sch n := by
  cases h : δ.to_final a.2 with
  | some b =>
    rw [sch_step_or_final_is_final _ _ ⟨b, h⟩, dret_id_left, sch_exec_is_final _ _ _ _ h,
      sch_exec_is_final _ _ _ _ h]
  | none =>
    rw [sch_step_or_final_not_final _ _ (to_final_None_2 _ h)]
    simp only [sch_exec, h]

/-- Rocq: `sch_exec_plus`. -/
theorem sch_exec_plus (a : sch_state × δ.mdpstate) (n1 n2 : ℕ) :
    sch_exec sch (n1 + n2) a = sch_pexec sch n1 a ≫= sch_exec sch n2 := by
  induction n1 generalizing a with
  | zero => rw [sch_pexec_O, dret_id_left, Nat.zero_add]
  | succ n1 ih =>
    rw [Nat.add_right_comm, sch_exec_Sn, sch_pexec_Sn, ← dbind_assoc]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `sch_exec_pexec_relate`. -/
theorem sch_exec_pexec_relate (a : sch_state × δ.mdpstate) (n : ℕ) :
    sch_exec sch n a = sch_pexec sch n a ≫=
      (fun e => match δ.to_final e.2 with
        | some b => dret b
        | none => dzero) := by
  induction n generalizing a with
  | zero => rw [sch_pexec_O, dret_id_left']; rfl
  | succ n ih =>
    rw [sch_pexec_Sn, ← dbind_assoc']
    cases h : δ.to_final a.2 with
    | some b =>
      rw [sch_step_or_final_is_final _ _ ⟨b, h⟩, dret_id_left',
        sch_pexec_is_final _ _ _ ⟨b, h⟩, dret_id_left', sch_exec_is_final _ _ _ _ h, h]
    | none =>
      rw [sch_step_or_final_not_final _ _ (to_final_None_2 _ h)]
      simp only [sch_exec, h]
      exact dbind_ext_right _ _ _ ih

/-- Rocq: `sch_exec_mono`. -/
theorem sch_exec_mono (a : sch_state × δ.mdpstate) (n : ℕ) (v : δ.mdpstate_ret) :
    sch_exec sch n a v ≤ sch_exec sch (n + 1) a v := by
  induction n generalizing a with
  | zero =>
    cases h : δ.to_final a.2 with
    | some b => rw [sch_exec_is_final _ _ _ _ h, sch_exec_is_final _ _ _ _ h]
    | none => simp only [sch_exec, h, dzero_0]; exact zero_le
  | succ n ih =>
    rw [sch_exec_Sn, sch_exec_Sn, dbind_unfold_pmf, dbind_unfold_pmf]
    exact ENNReal.tsum_le_tsum fun a' => mul_le_mul' le_rfl (ih a')

/-- Rocq: `sch_exec_mono'`. -/
theorem sch_exec_mono' (ρ : sch_state × δ.mdpstate) (n m : ℕ) (v : δ.mdpstate_ret)
    (h : n ≤ m) : sch_exec sch n ρ v ≤ sch_exec sch m ρ v :=
  monotone_nat_of_le_succ (f := fun x => sch_exec sch x ρ v) (fun k => sch_exec_mono sch ρ k v) h

/-- Rocq: `sch_exec_mono_term`. -/
theorem sch_exec_mono_term (a : sch_state × δ.mdpstate) (b : δ.mdpstate_ret) (n m : ℕ)
    (Hv : ∑' b, sch_exec sch n a b = 1) (Hleq : n ≤ m) :
    sch_exec sch m a b = sch_exec sch n a b := by
  refine le_antisymm ?_ (sch_exec_mono' sch a n m b Hleq)
  by_contra hlt
  push Not at hlt
  have : ∑' b, sch_exec sch n a b < ∑' b, sch_exec sch m a b :=
    ENNReal.tsum_lt_tsum (SeriesC_ne_top _) (fun b' => sch_exec_mono' sch a n m b' Hleq) hlt
  rw [Hv] at this
  exact absurd (sch_exec sch m a).mass_le_one (not_le.2 this)

/-- Rocq: `sch_exec_O_not_final`. -/
theorem sch_exec_O_not_final (a : sch_state × δ.mdpstate) (h : ¬ is_final a.2) :
    sch_exec sch 0 a = dzero := by
  simp only [sch_exec, to_final_None_1 _ h]

/-- Rocq: `sch_exec_Sn_not_final`. -/
theorem sch_exec_Sn_not_final (a : sch_state × δ.mdpstate) (n : ℕ) (h : ¬ is_final a.2) :
    sch_exec sch (n + 1) a = sch_step sch a ≫= sch_exec sch n := by
  rw [sch_exec_Sn, sch_step_or_final_not_final _ _ h]

/-- Rocq: `sch_pexec_exec_le_final`. -/
theorem sch_pexec_exec_le_final (n : ℕ) (a a' : sch_state × δ.mdpstate) (b : δ.mdpstate_ret)
    (h : δ.to_final a'.2 = some b) : sch_pexec sch n a a' ≤ sch_exec sch n a b := by
  induction n generalizing a with
  | zero =>
    rw [sch_pexec_O]
    by_cases hx : a = a'
    · subst hx
      rw [sch_exec_is_final _ _ _ _ h, dret_1_1 _ _ rfl, dret_1_1 _ _ rfl]
    · rw [dret_0 _ _ (Ne.symm hx)]; exact zero_le
  | succ n ih =>
    rw [sch_exec_Sn, sch_pexec_Sn, dbind_unfold_pmf, dbind_unfold_pmf]
    exact ENNReal.tsum_le_tsum fun a'' => mul_le_mul' le_rfl (ih a'')

/-- Rocq: `sch_pexec_exec_det`. -/
theorem sch_pexec_exec_det (n : ℕ) (a a' : sch_state × δ.mdpstate) (b : δ.mdpstate_ret)
    (Hf : δ.to_final a'.2 = some b) (h : sch_pexec sch n a a' = 1) :
    sch_exec sch n a b = 1 :=
  le_antisymm (pmf_le_1 _ _) (h ▸ sch_pexec_exec_le_final sch n a a' b Hf)

/-- Rocq: `sch_exec_pexec_val_neq_le`. -/
theorem sch_exec_pexec_val_neq_le (n m : ℕ) (a a' : sch_state × δ.mdpstate)
    (b b' : δ.mdpstate_ret) (Hf : δ.to_final a'.2 = some b') (Hneq : b ≠ b') :
    sch_exec sch m a b + sch_pexec sch n a a' ≤ 1 := by
  calc sch_exec sch m a b + sch_pexec sch n a a'
      ≤ sch_exec sch (max n m) a b + sch_exec sch (max n m) a b' := by
        gcongr
        · exact sch_exec_mono' sch a m _ b (le_max_right _ _)
        · exact (sch_pexec_exec_le_final sch n a a' b' Hf).trans
            (sch_exec_mono' sch a n _ b' (le_max_left _ _))
    _ ≤ ∑' b, sch_exec sch (max n m) a b := pmf_plus_neq_SeriesC _ _ _ Hneq
    _ ≤ 1 := pmf_SeriesC _

/-- Rocq: `sch_pexec_exec_det_neg`. -/
theorem sch_pexec_exec_det_neg (n m : ℕ) (a a' : sch_state × δ.mdpstate)
    (b b' : δ.mdpstate_ret) (Hf : δ.to_final a'.2 = some b') (Hexec : sch_pexec sch n a a' = 1)
    (Hv : b ≠ b') : sch_exec sch m a b = 0 := by
  have Hle := sch_exec_pexec_val_neq_le sch n m a a' b b' Hf Hv
  rw [Hexec] at Hle
  by_contra h0
  have : 1 < sch_exec sch m a b + 1 := by
    rw [add_comm]; exact ENNReal.lt_add_right ENNReal.one_ne_top h0
  exact absurd Hle (not_le.2 this)

/-- Rocq: `is_finite_Sup_seq_sch_exec`. -/
theorem is_finite_Sup_seq_sch_exec (a : sch_state × δ.mdpstate) (b : δ.mdpstate_ret) :
    ⨆ n, sch_exec sch n a b ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => pmf_le_1 _ _)

/-- Rocq: `is_finite_Sup_seq_SeriesC_sch_exec`. -/
theorem is_finite_Sup_seq_SeriesC_sch_exec (a : sch_state × δ.mdpstate) :
    ⨆ n, ∑' b, sch_exec sch n a b ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ => pmf_SeriesC _)

/-! ### Full evaluation (limit of stratification) -/

/-- Rocq: `sch_lim_exec`. -/
def sch_lim_exec (ρ : sch_state × δ.mdpstate) : Distr δ.mdpstate_ret :=
  lim_distr (fun n => sch_exec sch n ρ) (fun n v => sch_exec_mono sch ρ n v)

/-- Rocq: `sch_lim_exec_unfold`. -/
theorem sch_lim_exec_unfold (a : sch_state × δ.mdpstate) (b : δ.mdpstate_ret) :
    sch_lim_exec sch a b = ⨆ n, sch_exec sch n a b := rfl

/-- Rocq: `sch_lim_exec_Sup_seq`. -/
theorem sch_lim_exec_Sup_seq (a : sch_state × δ.mdpstate) :
    ∑' b, sch_lim_exec sch a b = ⨆ n, ∑' b, sch_exec sch n a b := by
  simp only [sch_lim_exec_unfold]
  exact tsum_iSup_of_monotone fun b =>
    monotone_nat_of_le_succ fun n => sch_exec_mono sch a n b

/-- Rocq: `sch_lim_exec_step`. -/
theorem sch_lim_exec_step (a : sch_state × δ.mdpstate) :
    sch_lim_exec sch a = sch_step_or_final sch a ≫= sch_lim_exec sch := by
  ext b
  rw [dbind_unfold_pmf, sch_lim_exec_unfold]
  simp only [sch_lim_exec_unfold, ENNReal.mul_iSup]
  rw [tsum_iSup_of_monotone (f := fun n a' => sch_step_or_final sch a a' * sch_exec sch n a' b)
    fun a' => monotone_nat_of_le_succ fun n => mul_le_mul' le_rfl (sch_exec_mono sch a' n b)]
  simp only [← dbind_unfold_pmf, ← sch_exec_Sn]
  exact (Monotone.iSup_nat_add (f := fun n => sch_exec sch n a b)
    (monotone_nat_of_le_succ fun n => sch_exec_mono sch a n b) 1).symm

/-- Rocq: `sch_lim_exec_pexec`. -/
theorem sch_lim_exec_pexec (n : ℕ) (a : sch_state × δ.mdpstate) :
    sch_lim_exec sch a = sch_pexec sch n a ≫= sch_lim_exec sch := by
  induction n generalizing a with
  | zero => rw [sch_pexec_O, dret_id_left]
  | succ n ih =>
    rw [sch_pexec_Sn, ← dbind_assoc, sch_lim_exec_step]
    exact dbind_ext_right _ _ _ ih

/-- Rocq: `sch_lim_exec_det_final`. -/
theorem sch_lim_exec_det_final (n : ℕ) (a a' : sch_state × δ.mdpstate) (b : δ.mdpstate_ret)
    (Hb : δ.to_final a'.2 = some b) (Hpe : sch_pexec sch n a a' = 1) :
    sch_lim_exec sch a = dret b := by
  ext b'
  rw [sch_lim_exec_unfold]
  by_cases hb : b = b'
  · subst hb
    rw [dret_1_1 _ _ rfl]
    refine le_antisymm (iSup_le fun _ => pmf_le_1 _ _) ?_
    exact le_iSup_of_le n (sch_pexec_exec_det sch n a a' b Hb Hpe).symm.le
  · rw [dret_0 _ _ (Ne.symm hb)]
    simp only [sch_pexec_exec_det_neg sch n _ a a' b' b Hb Hpe (Ne.symm hb), iSup_const]

/-- Rocq: `sch_lim_exec_final`. -/
theorem sch_lim_exec_final (a : sch_state × δ.mdpstate) (b : δ.mdpstate_ret)
    (h : δ.to_final a.2 = some b) : sch_lim_exec sch a = dret b :=
  sch_lim_exec_det_final sch 0 a a b h (by rw [sch_pexec_O]; exact dret_1_1 _ _ rfl)

/-- Rocq: `sch_lim_exec_not_final`. -/
theorem sch_lim_exec_not_final (a : sch_state × δ.mdpstate) (Hn : ¬ is_final a.2) :
    sch_lim_exec sch a = sch_step sch a ≫= sch_lim_exec sch := by
  rw [sch_lim_exec_step, sch_step_or_final_not_final _ _ Hn]

/-- Rocq: `sch_lim_exec_leq`. -/
theorem sch_lim_exec_leq (a : sch_state × δ.mdpstate) (b : δ.mdpstate_ret) (r : ℝ≥0∞)
    (Hexec : ∀ n, sch_exec sch n a b ≤ r) : sch_lim_exec sch a b ≤ r :=
  iSup_le Hexec

/-- Rocq: `sch_lim_exec_leq_mass`. -/
theorem sch_lim_exec_leq_mass (a : sch_state × δ.mdpstate) (r : ℝ≥0∞)
    (Hm : ∀ n, ∑' b, sch_exec sch n a b ≤ r) : ∑' b, sch_lim_exec sch a b ≤ r := by
  rw [sch_lim_exec_Sup_seq]
  exact iSup_le Hm

/-- Rocq: `sch_lim_exec_term`. -/
theorem sch_lim_exec_term (n : ℕ) (a : sch_state × δ.mdpstate)
    (Hv : ∑' b, sch_exec sch n a b = 1) : sch_lim_exec sch a = sch_exec sch n a := by
  ext b
  rw [sch_lim_exec_unfold]
  refine le_antisymm (iSup_le fun n' => ?_) (le_iSup (fun m => sch_exec sch m a b) n)
  rcases le_total n n' with h | h
  · exact (sch_exec_mono_term sch a b n n' Hv h).le
  · exact sch_exec_mono' sch a n' n b h

/-- Rocq: `sch_lim_exec_pos`. -/
theorem sch_lim_exec_pos (a : sch_state × δ.mdpstate) (b : δ.mdpstate_ret)
    (h : 0 < sch_lim_exec sch a b) : ∃ n, 0 < sch_exec sch n a b := by
  rw [sch_lim_exec_unfold] at h
  exact lt_iSup_iff.1 h

/-- Rocq: `sch_lim_exec_continuous_prob`. -/
theorem sch_lim_exec_continuous_prob (a : sch_state × δ.mdpstate)
    (ϕ : δ.mdpstate_ret → Bool) (r : ℝ≥0∞) (Hm : ∀ n, prob (sch_exec sch n a) ϕ ≤ r) :
    prob (sch_lim_exec sch a) ϕ ≤ r := by
  unfold prob at Hm ⊢
  have Haux : ∀ v, (if ϕ v then sch_lim_exec sch a v else 0) =
      ⨆ n, if ϕ v then sch_exec sch n a v else 0 := by
    intro v
    cases ϕ v <;> simp [sch_lim_exec_unfold]
  simp only [Haux]
  rw [tsum_iSup_of_monotone]
  · exact iSup_le Hm
  · intro v
    refine monotone_nat_of_le_succ fun n => ?_
    cases ϕ v
    · exact le_rfl
    · exact sch_exec_mono sch a n v

end step

end scheduler

end Prob
