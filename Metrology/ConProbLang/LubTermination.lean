module

public import Metrology.ConProbLang.Erasure

/-!
# Least upper bound of termination probabilities

Ported from clutch/theories/con_prob_lang/lub_termination.v

The termination probability of a configuration under a tape-oblivious scheduler, and its least
upper bound over all tape-oblivious schedulers.

## Rocq → Lean
* Probabilities are `ℝ≥0∞`; `SeriesC` is `∑'`.
* `Lub_Rbar P` (the least upper bound in `Rbar` of a predicate `P : R → Prop`) is `sSup {r | P r}`
  in `ℝ≥0∞`; `Sup_seq` is `⨆ n`.
* `termination_prob_type` (a nested `sigT` in Rocq:
  `{ sch_int_σ & sch_int_σ * { Heq & { Hcount & { sch & TapeOblivious sch_int_σ sch } } } }`) is a
  structure with fields `sch_int_σ`, `ζ`, `eqdec`, `countable`, `sch`, `tape_oblivious` (in the
  Rocq order); Rocq's `projT1 p`, `(projT2 p).1`, ... are these fields. `eqdec`, `countable`
  and `tape_oblivious` are registered as instances.
* `lub_termination_prob_eq` (Rocq: `Rbar.Finite (real (lub_termination_prob e σ)) =
  lub_termination_prob e σ`, i.e. finiteness) is stated as
  `ENNReal.ofReal (lub_termination_prob e σ).toReal = lub_termination_prob e σ`; the helper
  `lub_termination_prob_le_one` gives the bound. The Rocq proof's lower bound (`0 ≤`) and the
  inhabitant of `termination_prob_type` it needs are unnecessary in `ℝ≥0∞`.
* Configurations `cfg` are typed as `(con_lang_mdp con_prob_lang).mdpstate` (reducibly
  `List expr × state` only at default transparency; see `Lang.lean`).

The Rocq file defines no tactics.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

namespace con_prob_lang

set_option quotPrecheck false in
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-- Rocq: `termination_prob`. -/
def termination_prob (cfg : CPState) (sch_int_σ : Type) (ζ : sch_int_σ)
    [DecidableEq sch_int_σ] [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) [TapeOblivious sch_int_σ sch] :
    ℝ≥0∞ :=
  ∑' v, sch_lim_exec sch (ζ, cfg) v

/-- Rocq: `termination_prob_type`: a tape-oblivious scheduler together with its initial state. -/
structure termination_prob_type : Type 1 where
  sch_int_σ : Type
  ζ : sch_int_σ
  eqdec : DecidableEq sch_int_σ
  countable : Countable sch_int_σ
  sch : @scheduler (con_lang_mdp con_prob_lang) sch_int_σ countable
  tape_oblivious : @TapeOblivious sch_int_σ countable sch

attribute [instance] termination_prob_type.eqdec termination_prob_type.countable
  termination_prob_type.tape_oblivious

/-- Rocq: `termination_n_prob`. -/
def termination_n_prob (n : ℕ) (cfg : CPState) (sch_int_σ : Type) (ζ : sch_int_σ)
    [DecidableEq sch_int_σ] [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) [TapeOblivious sch_int_σ sch] :
    ℝ≥0∞ :=
  ∑' v, sch_exec sch n (ζ, cfg) v

/-- Rocq: `termination_prob'`. -/
def termination_prob' (e : expr) (σ : state) (r : ℝ≥0∞) : Prop :=
  ∃ p : termination_prob_type,
    @termination_prob ([e], σ) p.sch_int_σ p.ζ p.eqdec p.countable p.sch p.tape_oblivious = r

/-- Rocq: `termination_n_prob'`. -/
def termination_n_prob' (n : ℕ) (e : expr) (σ : state) (r : ℝ≥0∞) : Prop :=
  ∃ p : termination_prob_type,
    @termination_n_prob n ([e], σ) p.sch_int_σ p.ζ p.eqdec p.countable p.sch p.tape_oblivious = r

/-- Rocq: `lub_termination_prob`. -/
def lub_termination_prob (e : expr) (σ : state) : ℝ≥0∞ := sSup {r | termination_prob' e σ r}

/-- Rocq: `lub_termination_n_prob`. -/
def lub_termination_n_prob (n : ℕ) (e : expr) (σ : state) : ℝ≥0∞ :=
  sSup {r | termination_n_prob' n e σ r}

/-- Rocq: `lub_termination_sup_seq_termination_n`. -/
theorem lub_termination_sup_seq_termination_n (e : expr) (σ : state) :
    lub_termination_prob e σ = ⨆ n, lub_termination_n_prob n e σ := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro r ⟨p, rfl⟩
    unfold termination_prob
    rw [sch_lim_exec_Sup_seq]
    exact iSup_mono fun n => le_sSup ⟨p, rfl⟩
  · refine iSup_le fun n => sSup_le ?_
    rintro r ⟨p, rfl⟩
    refine le_trans ?_ (le_sSup (⟨p, rfl⟩ : termination_prob' e σ _))
    unfold termination_n_prob termination_prob
    exact ENNReal.tsum_le_tsum fun v =>
      le_iSup (fun n => sch_exec p.sch n (p.ζ, (([e], σ) : CPState)) v) n

/-- Helper (not in Rocq): the least upper bound of termination probabilities is at most `1`. -/
theorem lub_termination_prob_le_one (e : expr) (σ : state) : lub_termination_prob e σ ≤ 1 := by
  refine sSup_le ?_
  rintro r ⟨p, rfl⟩
  exact pmf_SeriesC _

/-- Rocq: `lub_termination_prob_eq` (finiteness of `lub_termination_prob`). -/
theorem lub_termination_prob_eq (e : expr) (σ : state) :
    ENNReal.ofReal (lub_termination_prob e σ).toReal = lub_termination_prob e σ :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (lub_termination_prob_le_one e σ))

end con_prob_lang

end ConProbLang
