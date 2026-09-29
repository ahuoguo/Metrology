module

public import Metrology.ConProbLang.Metatheory
public import Metrology.ConProbLang.Common.SchErasable
public import Metrology.Prob.Couplings

/-!
# Erasure of state steps for tape-oblivious schedulers

Ported from clutch/theories/con_prob_lang/erasure.v

Main results: for a tape-oblivious scheduler (`TapeOblivious`), a state step
(`state_step σ α`, i.e. appending a uniformly sampled value to the allocated tape `α`) is
scheduler-erasable (`state_step_sch_erasable`, `state_step_sch_erasable_val`,
`iterM_state_step_sch_erasable`), and so it does not change the distribution of thread pools
(`pexec_coupl_step_pexec`), of results (`prim_coupl_step_prim`) or of the limit execution
(`sch_limprim_coupl_step_sch_limprim`, `sch_lim_exec_eq_erasure`). The lemmas
`prim_coupl_step_prim(_pexec)_sch_erasable` / `prim_coupl_step_prim(_pexec)'` erase a state
step in front of a `prim_step` of a thread, via `force_first_thread_scheduler`.

Everything lives in `ConProbLang.con_prob_lang` (Rocq's file is outside the module, but uses
its names unqualified).

## Rocq → Lean
* `Rcoupl μ1 μ2 eq` statements are kept; since `Rcoupl μ1 μ2 (· = ·) ↔ μ1 = μ2`
  (`Rcoupl_eq`/`Rcoupl_eq_elim`), the proofs go through equational helpers
  (`prim_coupl_upd_tapes_dom_eq`, `pexec_coupl_step_pexec_eq`).
* The class of schedulers `λ t Heq Hcount sch', TapeOblivious t sch'` is written
  `fun t _ _ sch' => TapeOblivious t sch'`. Scheduler states live in an arbitrary universe
  (`TapeOblivious` is universe polymorphic); where a `sch_erasable` hypothesis is combined with a
  scheduler, its universe is tied to that scheduler's state type (`Type u`).
* `λ '(e', s, l), ..` is written with projections `t.1`, `t.2.1`, `t.2.2`; `<[num:=e']> es` is
  `es.set num e'`; `prim_step` is `prim_step (Λ := con_prob_lang)`; `σ.(tapes) !! α` is
  `σ.tapes[α]?`.
* Rocq's `{Countable sch_int_σ}` bundles `EqDecision`; here `[DecidableEq sch_int_σ]` is only
  required where `sch_erasable` is used.
* The section `erasure_helpers` (with its `IH` over `sch_pexec sch m`) is generalised: `IH` is
  `tape_erasable_cont k` for an arbitrary continuation `k` of a head step, and the `Local`
  lemmas `ind_case_det`, `ind_case_dzero`, `ind_case_alloc`, `ind_case_rand_some`,
  `ind_case_rand_empty`, `ind_case_rand_some_neq`, `ind_case_rand` state
  `head_step e σ ≫= k = dunifP N ≫= λ z, head_step e (σ with α ↦ zs ++ [z]) ≫= k` (Rocq states
  the same with `Rcoupl .. eq` and `k` specialised to the thread-pool update followed by
  `sch_pexec sch m`). The case analysis at the end of `prim_coupl_upd_tapes_dom` is the helper
  `head_step_tape_erasure`, lifted step by step through `prim_step_tape_erasure`,
  `mdp_step_tape_erasure` and `sch_step_or_final_tape_erasure`.
* `force_first_thread_scheduler` (Rocq `Local Definition`) drops its unused
  `TapeOblivious sch_int_σ sch` argument; `force_first_thread_scheduler_tape_oblivious` is a
  theorem (not an instance).

## Added helpers (not in Rocq)
`dmap_dbind_eq'`, `tape_erasable_cont`, `ind_case_indep`, `head_step_tape_erasure`,
`prim_step_tape_erasure`, `mdp_step_tape_erasure`, `sch_step_or_final_tape_erasure`,
`prim_coupl_upd_tapes_dom_eq`, `pexec_coupl_step_pexec_eq`,
`force_first_thread_scheduler_sch_step_or_final`, `force_first_thread_scheduler_sch_pexec`,
`force_first_thread_scheduler_first_step`.

The Rocq file defines no tactics.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

universe u

namespace con_prob_lang

set_option quotPrecheck false in
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-- Helper: binding after a `dmap`. -/
theorem dmap_dbind_eq' {α β γ : Type*} [Countable α] [Countable β] [Countable γ]
    (f : α → β) (μ : Distr α) (k : β → Distr γ) : dmap f μ ≫= k = μ ≫= fun a => k (f a) := by
  rw [dmap, ← dbind_assoc]
  exact dbind_ext_right _ _ _ fun a => dret_id_left _ _

section erasure_helpers

variable {Y : Type} [Countable Y]

/-- Helper (not in Rocq): the property of a continuation `k` of a head step that appending a
uniformly sampled value to an allocated tape can be erased. In the Rocq section
`erasure_helpers` this is the induction hypothesis `IH` specialised to the continuation
`λ a, dmap (λ x, x.2.1) (sch_pexec sch m a)`. -/
def tape_erasable_cont (k : expr × state × List expr → Distr Y) : Prop :=
  ∀ (e : expr) (σ : state) (efs : List expr) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1))),
    σ.tapes[α]? = some ⟨N, zs⟩ →
    k (e, σ, efs) = dunifP N ≫= fun z => k (e, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ, efs)

variable (k : expr × state × List expr → Distr Y) (IH : tape_erasable_cont k)
include IH

/-- Rocq: `ind_case_det` (generalised to any erasable continuation `k`). -/
theorem ind_case_det (e : expr) (σ : state) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1)))
    (Hα : σ.tapes[α]? = some ⟨N, zs⟩) (Hdet : is_det_head_step e σ = true) :
    head_step e σ ≫= k =
      dunifP N ≫= fun z => head_step e (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) ≫= k := by
  obtain ⟨e2, σ2, efs, Hd⟩ := (det_step_pred_ex_rel _ _).1 ((is_det_head_step_true _ _).1 Hdet)
  rw [det_head_step_singleton _ _ _ _ _ Hd, dret_id_left]
  rw [dbind_ext_right _ _ _ fun z => by
    rw [det_head_step_singleton _ _ _ _ _ (det_head_step_upd_tapes N _ _ _ _ _ α z zs Hd Hα),
      dret_id_left]]
  rw [det_step_eq_tapes _ _ _ _ _ Hd] at Hα
  exact IH _ _ _ _ _ _ Hα

omit IH in
/-- Rocq: `ind_case_dzero` (generalised to any erasable continuation `k`). -/
theorem ind_case_dzero (e : expr) (σ : state) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1)))
    (Hα : σ.tapes[α]? = some ⟨N, zs⟩) (Hz : head_step e σ = dzero) :
    head_step e σ ≫= k =
      dunifP N ≫= fun z => head_step e (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) ≫= k := by
  rw [Hz, dbind_dzero]
  rw [dbind_ext_right _ _ _ fun z => by
    rw [head_step_dzero_upd_tapes α e σ N zs z ((map_mem_iff _ _).2 ⟨_, Hα⟩) Hz, dbind_dzero]]
  exact (dzero_dbind _).symm

/-- Rocq: `ind_case_alloc` (generalised to any erasable continuation `k`). -/
theorem ind_case_alloc (z : ℤ) (σ : state) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1)))
    (Hα : σ.tapes[α]? = some ⟨N, zs⟩) :
    head_step (AllocTape (Val (LitV (LitInt z)))) σ ≫= k =
      dunifP N ≫= fun a0 =>
        head_step (AllocTape (Val (LitV (LitInt z))))
          (state_upd_tapes (·.insert α ⟨N, zs ++ [a0]⟩) σ) ≫= k := by
  rw [dbind_ext_right _ _ (fun (n : Fin (N + 1)) => k (Val (LitV (LitLbl (fresh_loc σ.tapes))),
      state_upd_tapes (·.insert α ⟨N, zs ++ [n]⟩)
        (state_upd_tapes (·.insert (fresh_loc σ.tapes) ⟨z.toNat, []⟩) σ), [])) fun n => by
    simp only [head_step, dret_id_left, state_upd_tapes_tapes]
    rw [← fresh_loc_upd_some σ α ⟨N, zs⟩ _ Hα, fresh_loc_upd_swap σ α _ _ _ Hα]]
  simp only [head_step, dret_id_left]
  exact IH _ _ _ _ _ _ (fresh_loc_lookup σ α _ _ Hα)

/-- Helper: the cases where the head step samples independently of the tape `α`. -/
theorem ind_case_indep (σ : state) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1)))
    (Hα : σ.tapes[α]? = some ⟨N, zs⟩) (M : ℕ) (f : Fin (M + 1) → expr) :
    dmap (fun n => (f n, σ, ([] : List expr))) (dunifP M) ≫= k =
      dunifP N ≫= fun a0 =>
        dmap (fun n => (f n, state_upd_tapes (·.insert α ⟨N, zs ++ [a0]⟩) σ, ([] : List expr)))
          (dunifP M) ≫= k := by
  simp only [dmap_dbind_eq']
  rw [dbind_comm]
  exact dbind_ext_right _ _ _ fun n => IH _ _ _ _ _ _ Hα

/-- Rocq: `ind_case_rand_some` (generalised to any erasable continuation `k`). -/
theorem ind_case_rand_some (z : ℤ) (σ : state) (α α' : Loc) (N M : ℕ) (n : Fin (N + 1))
    (ns : List (Fin (N + 1))) (ns' : List (Fin (M + 1))) (Hz : N = z.toNat)
    (Hα : σ.tapes[α]? = some ⟨M, ns'⟩) (Hα' : σ.tapes[α']? = some ⟨N, n :: ns⟩) :
    head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α')))) σ ≫= k =
      dunifP M ≫= fun a0 =>
        head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α'))))
          (state_upd_tapes (·.insert α ⟨M, ns' ++ [a0]⟩) σ) ≫= k := by
  subst Hz
  by_cases hαα : α = α'
  · subst hαα
    rw [Hα'] at Hα
    cases Hα
    simp only [head_step, Hα', state_upd_tapes_tapes, Std.ExtTreeMap.getElem?_insert_self,
      List.cons_append, ite_true, dret_id_left, state_upd_tapes_twice]
    rw [IH _ _ _ α _ ns (by simp)]
    simp only [state_upd_tapes_twice]
  · simp only [head_step, Hα', state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ hαα, ite_true,
      dret_id_left]
    simp only [upd_diff_tape_comm σ α α' _ _ hαα]
    exact IH _ _ _ _ _ _ (by simpa [map_getElem?_insert_ne _ _ _ _ (Ne.symm hαα)] using Hα)

/-- Rocq: `ind_case_rand_empty` (generalised to any erasable continuation `k`). -/
theorem ind_case_rand_empty (z : ℤ) (σ : state) (α α' : Loc) (N M : ℕ)
    (ns : List (Fin (N + 1))) (Hz : M = z.toNat)
    (Hα : σ.tapes[α]? = some ⟨N, ns⟩) (Hα' : σ.tapes[α']? = some ⟨M, []⟩) :
    head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α')))) σ ≫= k =
      dunifP N ≫= fun a0 =>
        head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α'))))
          (state_upd_tapes (·.insert α ⟨N, ns ++ [a0]⟩) σ) ≫= k := by
  subst Hz
  by_cases hαα : α = α'
  · subst hαα
    rw [Hα'] at Hα
    cases Hα
    simp only [head_step, Hα', state_upd_tapes_tapes, Std.ExtTreeMap.getElem?_insert_self,
      List.nil_append, ite_true, dret_id_left, state_upd_tapes_twice,
      state_upd_tapes_no_change σ α _ [] Hα', dmap_dbind_eq']
  · simp only [head_step, Hα', state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ hαα,
      ite_true]
    exact ind_case_indep k IH σ α N ns Hα _ _

/-- Rocq: `ind_case_rand_some_neq` (generalised to any erasable continuation `k`). -/
theorem ind_case_rand_some_neq (z : ℤ) (σ : state) (α α' : Loc) (N M : ℕ)
    (ns : List (Fin (N + 1))) (ns' : List (Fin (M + 1))) (Hz : N ≠ z.toNat)
    (Hα : σ.tapes[α]? = some ⟨M, ns'⟩) (Hα' : σ.tapes[α']? = some ⟨N, ns⟩) :
    head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α')))) σ ≫= k =
      dunifP M ≫= fun a0 =>
        head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α'))))
          (state_upd_tapes (·.insert α ⟨M, ns' ++ [a0]⟩) σ) ≫= k := by
  by_cases hαα : α = α'
  · subst hαα
    rw [Hα'] at Hα
    cases Hα
    simp only [head_step, Hα', state_upd_tapes_tapes, Std.ExtTreeMap.getElem?_insert_self, Hz,
      ite_false]
    exact ind_case_indep k IH σ α N ns Hα' _ _
  · simp only [head_step, Hα', state_upd_tapes_tapes, map_getElem?_insert_ne _ _ _ _ hαα, Hz,
      ite_false]
    exact ind_case_indep k IH σ α M ns' Hα _ _

/-- Rocq: `ind_case_rand` (generalised to any erasable continuation `k`). -/
theorem ind_case_rand (z : ℤ) (σ : state) (α : Loc) (N M : ℕ) (ns : List (Fin (M + 1)))
    (_Hz : N = z.toNat) (Hα : σ.tapes[α]? = some ⟨M, ns⟩) :
    head_step (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ ≫= k =
      dunifP M ≫= fun a0 =>
        head_step (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit)))
          (state_upd_tapes (·.insert α ⟨M, ns ++ [a0]⟩) σ) ≫= k := by
  simp only [head_step]
  exact ind_case_indep k IH σ α M ns Hα _ _

/-- Helper (not in Rocq; the case analysis at the end of `prim_coupl_upd_tapes_dom`): appending a
sampled value to an allocated tape before a head step can be erased. -/
theorem head_step_tape_erasure (e : expr) (σ : state) (α : Loc) (N : ℕ)
    (zs : List (Fin (N + 1))) (Hα : σ.tapes[α]? = some ⟨N, zs⟩) :
    head_step e σ ≫= k =
      dunifP N ≫= fun z => head_step e (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) ≫= k := by
  rcases det_or_prob_or_dzero e σ with HD | HP | HZ
  · exact ind_case_det k IH e σ α N zs Hα ((is_det_head_step_true _ _).2 HD)
  · cases HP with
    | AllocTapePSP _ _ z _ => exact ind_case_alloc k IH z σ α N zs Hα
    | RandTapePSP α' _ N' n ns z hN h => exact ind_case_rand_some k IH z σ α α' N' N n ns zs hN Hα h
    | RandEmptyPSP N' α' _ z hN h => exact ind_case_rand_empty k IH z σ α α' N N' zs hN Hα h
    | RandTapeOtherPSP N' M' α' _ ns z hne hM h =>
      exact ind_case_rand_some_neq k IH z σ α α' N' N ns zs (hM ▸ hne) Hα h
    | RandNoTapePSP N' _ z hN => exact ind_case_rand k IH z σ α N' N zs hN Hα
  · exact ind_case_dzero k e σ α N zs Hα HZ

/-- Helper (not in Rocq): `head_step_tape_erasure` lifted to `prim_step`. -/
theorem prim_step_tape_erasure (e : expr) (σ : state) (α : Loc) (N : ℕ)
    (zs : List (Fin (N + 1))) (Hα : σ.tapes[α]? = some ⟨N, zs⟩) :
    prim_step (Λ := con_prob_lang) e σ ≫= k =
      dunifP N ≫= fun z =>
        prim_step (Λ := con_prob_lang) e (state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) ≫= k := by
  have h : ∀ σ, prim_step (Λ := con_prob_lang) e σ =
      dmap (conEctxLanguage.fill_lift' (Λ := con_prob_ectx_lang) (con_prob_ectx_lang.decomp e).1)
        (head_step (con_prob_ectx_lang.decomp e).2 σ) := fun _ => rfl
  simp only [h, dmap_dbind_eq']
  refine head_step_tape_erasure _ ?_ _ σ α N zs Hα
  intro e' σ' efs α N zs H
  exact IH _ _ _ _ _ _ H

end erasure_helpers

section erasure_steps

variable {Y : Type} [Countable Y]

/-- Helper (not in Rocq): `prim_step_tape_erasure` lifted to a step of the MDP
`con_lang_mdp con_prob_lang`. -/
theorem mdp_step_tape_erasure (k : CPState → Distr Y)
    (Hk : ∀ (es : List expr) (σ : state) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1))),
      σ.tapes[α]? = some ⟨N, zs⟩ →
      k (es, σ) = dunifP N ≫= fun z => k (es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ))
    (tid : ℕ) (es : List expr) (σ : state) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1)))
    (Hα : σ.tapes[α]? = some ⟨N, zs⟩) :
    (con_lang_mdp con_prob_lang).step tid (es, σ) ≫= k =
      dunifP N ≫= fun z =>
        (con_lang_mdp con_prob_lang).step tid (es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ)
          ≫= k := by
  simp only [con_lang_mdp_step_eq, con_lang_mdp_step]
  rcases es[0]? >>= ConProbLang.to_val with _ | v
  · dsimp only
    rcases es[tid]? with _ | e
    · exact (dret_id_left k (es, σ)).trans ((Hk _ _ _ _ _ Hα).trans
        (dbind_ext_right _ _ _ fun z => (dret_id_left k _).symm))
    · dsimp only
      rcases ConProbLang.to_val (Λ := con_prob_lang) e with _ | w
      · dsimp only
        exact (dmap_dbind_eq' _ _ k).trans
          ((prim_step_tape_erasure (fun p => k (es.set tid p.1 ++ p.2.2, p.2.1))
            (fun _ _ _ _ _ _ H => Hk _ _ _ _ _ H) e σ α N zs Hα).trans
          (dbind_ext_right _ _ _ fun z => (dmap_dbind_eq' _ _ k).symm))
      · exact (dret_id_left k (es, σ)).trans ((Hk _ _ _ _ _ Hα).trans
          (dbind_ext_right _ _ _ fun z => (dret_id_left k _).symm))
  · exact (dbind_dzero k).trans ((dzero_dbind (dunifP N)).symm.trans
      (dbind_ext_right _ _ _ fun z => (dbind_dzero k).symm))

/-- Helper (not in Rocq): `mdp_step_tape_erasure` lifted to `sch_step_or_final` of a
tape-oblivious scheduler. -/
theorem sch_step_or_final_tape_erasure {sch_int_σ : Type*} [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) [TapeOblivious sch_int_σ sch]
    (k : sch_int_σ × CPState → Distr Y)
    (Hk : ∀ (ζ : sch_int_σ) (es : List expr) (σ : state) (α : Loc) (N : ℕ)
      (zs : List (Fin (N + 1))), σ.tapes[α]? = some ⟨N, zs⟩ →
      k (ζ, (es, σ)) =
        dunifP N ≫= fun z => k (ζ, (es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ)))
    (ζ : sch_int_σ) (es : List expr) (σ : state) (α : Loc) (N : ℕ) (zs : List (Fin (N + 1)))
    (Hα : σ.tapes[α]? = some ⟨N, zs⟩) :
    sch_step_or_final sch (ζ, (es, σ)) ≫= k =
      dunifP N ≫= fun z =>
        sch_step_or_final sch (ζ, (es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ)) ≫= k := by
  have L : ∀ ρ : sch_int_σ × CPState, sch_step sch ρ ≫= k =
      sch ρ ≫= fun p => (con_lang_mdp con_prob_lang).step p.2 ρ.2 ≫= fun m => k (p.1, m) :=
    fun ρ => by
      unfold sch_step
      rw [← dbind_assoc]
      exact dbind_ext_right _ _ _ fun p => dmap_dbind_eq' _ _ _
  cases h : (con_lang_mdp con_prob_lang).to_final ((es, σ) : CPState) with
  | none =>
    have h' : ∀ z : Fin (N + 1), (con_lang_mdp con_prob_lang).to_final
        ((es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) : CPState) = none := fun _ => h
    calc sch_step_or_final sch (ζ, (es, σ)) ≫= k
        = sch (ζ, (es, σ)) ≫= fun p =>
            (con_lang_mdp con_prob_lang).step p.2 (es, σ) ≫= fun m => k (p.1, m) := by
          rw [sch_step_or_final_not_final _ _ (to_final_None_2 _ h)]; exact L _
      _ = sch (ζ, (es, σ)) ≫= fun p => dunifP N ≫= fun z =>
            (con_lang_mdp con_prob_lang).step p.2
              (es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) ≫= fun m => k (p.1, m) :=
          dbind_ext_right _ _ _ fun p => mdp_step_tape_erasure (fun m => k (p.1, m))
            (fun _ _ _ _ _ H => Hk _ _ _ _ _ _ H) p.2 es σ α N zs Hα
      _ = dunifP N ≫= fun z => sch (ζ, (es, σ)) ≫= fun p =>
            (con_lang_mdp con_prob_lang).step p.2
              (es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ) ≫= fun m => k (p.1, m) :=
          dbind_comm _ _ _
      _ = dunifP N ≫= fun z =>
            sch_step_or_final sch (ζ, (es, state_upd_tapes (·.insert α ⟨N, zs ++ [z]⟩) σ)) ≫= k :=
          dbind_ext_right _ _ _ fun z => by
            rw [sch_step_or_final_not_final _ _ (to_final_None_2 _ (h' z)), L,
              sch_tape_oblivious_state_upd_tapes]
  | some v =>
    rw [sch_step_or_final_is_final _ _ ⟨v, h⟩, dret_id_left]
    refine (Hk _ _ _ _ _ _ Hα).trans (dbind_ext_right _ _ _ fun z => ?_)
    rw [sch_step_or_final_is_final _ _ ⟨v, h⟩, dret_id_left]

end erasure_steps

section erasure

variable {sch_int_σ : Type*} [Countable sch_int_σ]

/-- Helper (not in Rocq): the equational form of `prim_coupl_upd_tapes_dom`. -/
theorem prim_coupl_upd_tapes_dom_eq (m : ℕ) (es1 : List expr) (σ1 : state) (α : Loc) (N : ℕ)
    (ns : List (Fin (N + 1))) (ζ : sch_int_σ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [TapeOblivious sch_int_σ sch]
    (H : σ1.tapes[α]? = some ⟨N, ns⟩) :
    dmap (fun x => x.2.1) (sch_pexec sch m (ζ, (es1, σ1))) =
      dunifP N ≫= fun n =>
        dmap (fun x => x.2.1)
          (sch_pexec sch m (ζ, (es1, state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ1))) := by
  induction m generalizing es1 σ1 α N ns ζ with
  | zero =>
    have h0 : ∀ ρ : sch_int_σ × CPState,
        dmap (fun x => x.2.1) (sch_pexec sch 0 ρ) = dret ρ.2.1 := fun ρ => by
      rw [sch_pexec_O, dmap_dret]
    rw [h0, dbind_ext_right _ _ _ fun n => h0 _]
    exact (dret_const _ _ (dunifP_mass N)).symm
  | succ m ih =>
    have hS : ∀ ρ : sch_int_σ × CPState,
        dmap (fun x => x.2.1) (sch_pexec sch (m + 1) ρ) =
          sch_step_or_final sch ρ ≫= fun ρ' => dmap (fun x => x.2.1) (sch_pexec sch m ρ') :=
      fun ρ => by rw [sch_pexec_Sn, dmap_dbind]
    rw [hS, dbind_ext_right _ _ _ fun n => hS _]
    exact sch_step_or_final_tape_erasure sch _
      (fun ζ es σ α N zs H => ih es σ α N zs ζ H) ζ es1 σ1 α N ns H

/-- Rocq: `prim_coupl_upd_tapes_dom`. -/
theorem prim_coupl_upd_tapes_dom (m : ℕ) (es1 : List expr) (σ1 : state) (α : Loc) (N : ℕ)
    (ns : List (Fin (N + 1))) (ζ : sch_int_σ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [TapeOblivious sch_int_σ sch]
    (H : σ1.tapes[α]? = some ⟨N, ns⟩) :
    Rcoupl
      (dmap (fun x => x.2.1) (sch_pexec sch m (ζ, (es1, σ1))))
      (dunifP N ≫= fun n =>
        dmap (fun x => x.2.1)
          (sch_pexec sch m (ζ, (es1, state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ1))))
      (· = ·) := by
  rw [prim_coupl_upd_tapes_dom_eq m es1 σ1 α N ns ζ H]
  exact Rcoupl_eq _

/-- Helper (not in Rocq): the equational form of `pexec_coupl_step_pexec`. -/
theorem pexec_coupl_step_pexec_eq (m : ℕ) (es1 : List expr) (σ1 : state) (α : Loc) (bs : tape)
    (ζ : sch_int_σ) {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ}
    [TapeOblivious sch_int_σ sch] (H : σ1.tapes[α]? = some bs) :
    dmap (fun ρ => ρ.2.1) (sch_pexec sch m (ζ, (es1, σ1))) =
      dmap (fun ρ => ρ.2.1) (state_step σ1 α ≫= fun σ2 => sch_pexec sch m (ζ, (es1, σ2))) := by
  obtain ⟨N, ns⟩ := bs
  rw [state_step_unfold _ _ _ _ H, dmap_dbind_eq', dmap_dbind]
  exact prim_coupl_upd_tapes_dom_eq m es1 σ1 α N ns ζ H

/-- Rocq: `pexec_coupl_step_pexec`. -/
theorem pexec_coupl_step_pexec (m : ℕ) (es1 : List expr) (σ1 : state) (α : Loc) (bs : tape)
    (ζ : sch_int_σ) {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ}
    [TapeOblivious sch_int_σ sch] (H : σ1.tapes[α]? = some bs) :
    Rcoupl
      (dmap (fun ρ => ρ.2.1) (sch_pexec sch m (ζ, (es1, σ1))))
      (dmap (fun ρ => ρ.2.1) (state_step σ1 α ≫= fun σ2 => sch_pexec sch m (ζ, (es1, σ2))))
      (· = ·) := by
  rw [pexec_coupl_step_pexec_eq m es1 σ1 α bs ζ H]
  exact Rcoupl_eq _

end erasure

/-- Rocq: `state_step_sch_erasable`. -/
theorem state_step_sch_erasable (σ1 : state) (α : Loc) (bs : tape) (H : σ1.tapes[α]? = some bs) :
    sch_erasable (fun t _ _ sch' => TapeOblivious t sch') (state_step σ1 α) σ1 := by
  intro sch_state _ _ sch es ζ m HP
  exact (pexec_coupl_step_pexec_eq m es σ1 α bs ζ H).symm

/-- Rocq: `prim_coupl_step_prim`. -/
theorem prim_coupl_step_prim {sch_int_σ : Type*} [DecidableEq sch_int_σ] [Countable sch_int_σ]
    (m : ℕ) (es1 : List expr) (σ1 : state) (α : Loc) (bs : tape) (ζ : sch_int_σ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch]
    (H : σ1.tapes[α]? = some bs) :
    Rcoupl
      (sch_exec sch m (ζ, (es1, σ1)))
      (state_step σ1 α ≫= fun σ2 => sch_exec sch m (ζ, (es1, σ2)))
      (· = ·) := by
  rw [sch_erasable_sch_erasable_val _ _ _ (state_step_sch_erasable σ1 α bs H) sch_int_σ sch es1 ζ
    m HTO]
  exact Rcoupl_eq _

/-- Rocq: `state_step_sch_erasable_val`. -/
theorem state_step_sch_erasable_val (σ1 : state) (α : Loc) (bs : tape)
    (H : σ1.tapes[α]? = some bs) :
    sch_erasable_val (fun t _ _ sch' => TapeOblivious t sch') (state_step σ1 α) σ1 := by
  intro sch_state _ _ sch es ζ m HP
  exact (Rcoupl_eq_elim _ _ (prim_coupl_step_prim m es σ1 α bs ζ H)).symm

/-- Rocq: `iterM_state_step_sch_erasable`. -/
theorem iterM_state_step_sch_erasable (σ1 : state) (α : Loc) (bs : tape) (n : ℕ)
    (H : σ1.tapes[α]? = some bs) :
    sch_erasable (fun t _ _ sch' => TapeOblivious t sch')
      (iterM n (fun σ => state_step σ α) σ1) σ1 := by
  induction n generalizing σ1 bs with
  | zero => exact dret_sch_erasable (Λ := con_prob_lang) σ1 _
  | succ n ih =>
    rw [iterM_Sn]
    refine sch_erasable_dbind _ _ _ _ (state_step_sch_erasable σ1 α bs H) fun σ' K' => ?_
    obtain ⟨N, ns⟩ := bs
    rw [state_step_unfold _ _ _ _ H, dmap_pos] at K'
    obtain ⟨z, rfl, -⟩ := K'
    exact ih _ ⟨N, ns ++ [z]⟩ (by simp)

/-- Rocq: `limprim_coupl_step_limprim_aux`. -/
theorem limprim_coupl_step_limprim_aux {sch_int_σ : Type*} [DecidableEq sch_int_σ]
    [Countable sch_int_σ] (e1 : List expr) (σ1 : state) (α : Loc) (bs : tape)
    (v : (con_lang_mdp con_prob_lang).mdpstate_ret) (ζ : sch_int_σ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch]
    (Hsome : σ1.tapes[α]? = some bs) :
    sch_lim_exec sch (ζ, (e1, σ1)) v =
      (state_step σ1 α ≫= fun σ2 => sch_lim_exec sch (ζ, (e1, σ2))) v := by
  rw [sch_erasable_sch_lim_exec _ _ sch σ1 e1 ζ (state_step_sch_erasable σ1 α bs Hsome) HTO]

/-- Rocq: `sch_limprim_coupl_step_sch_limprim`. -/
theorem sch_limprim_coupl_step_sch_limprim {sch_int_σ : Type*} [DecidableEq sch_int_σ]
    [Countable sch_int_σ] (e1 : List expr) (σ1 : state) (α : Loc) (bs : tape) (ζ : sch_int_σ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch]
    (Hsome : σ1.tapes[α]? = some bs) :
    Rcoupl
      (sch_lim_exec sch (ζ, (e1, σ1)))
      (state_step σ1 α ≫= fun σ2 => sch_lim_exec sch (ζ, (e1, σ2)))
      (· = ·) := by
  rw [sch_erasable_sch_lim_exec _ _ sch σ1 e1 ζ (state_step_sch_erasable σ1 α bs Hsome) HTO]
  exact Rcoupl_eq _

/-- Rocq: `sch_lim_exec_eq_erasure`. -/
theorem sch_lim_exec_eq_erasure {sch_int_σ : Type*} [DecidableEq sch_int_σ] [Countable sch_int_σ]
    (αs : List Loc) (e : List expr) (σ : state) (ζ : sch_int_σ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch] :
    αs ⊆ get_active σ →
      sch_lim_exec sch (ζ, (e, σ)) =
        foldlM state_step σ αs ≫= fun σ' => sch_lim_exec sch (ζ, (e, σ')) := by
  induction αs generalizing σ with
  | nil => intro _; rw [foldlM_nil, dret_id_left]
  | cons α αs IH =>
    intro Hα
    have hmem : α ∈ σ.tapes := Std.ExtTreeMap.mem_keys.1 (Hα List.mem_cons_self)
    obtain ⟨bs, hbs⟩ := (map_mem_iff _ _).1 hmem
    rw [foldlM_cons, ← dbind_assoc]
    rw [dbind_ext_right_strong _ _ (fun σ' => sch_lim_exec sch (ζ, (e, σ'))) fun σ' hσ' => by
      refine (IH σ' ?_).symm
      rw [state_step_support_equiv_rel] at hσ'
      obtain ⟨α, N, n, ns, σ, hα⟩ := hσ'
      intro α' hα'
      have := Hα (List.mem_cons_of_mem _ hα')
      simp only [get_active, Std.ExtTreeMap.mem_keys, state_upd_tapes_tapes,
        Std.ExtTreeMap.mem_insert] at this ⊢
      exact Or.inr this]
    exact (sch_erasable_sch_lim_exec _ _ sch σ e ζ (state_step_sch_erasable σ α bs hbs) HTO).symm

section force_first_thread

variable {sch_int_σ : Type*} [Countable sch_int_σ]

/-- Rocq: `force_first_thread_scheduler` (a `Local Definition`). Before running `sch` from
`initial`, first step thread `num`. (The Rocq definition also takes an unused
`TapeOblivious sch_int_σ sch` argument, dropped here.) -/
def force_first_thread_scheduler (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)
    (num : ℕ) (initial : sch_int_σ) : scheduler (con_lang_mdp con_prob_lang) (Option sch_int_σ) :=
  ⟨fun p =>
    match p.1 with
    | none => dret (some initial, num)
    | some ζ' => dmap (fun q => (some q.1, q.2)) (sch (ζ', p.2))⟩

/-- Rocq: `force_first_thread_scheduler_tape_oblivious`. -/
theorem force_first_thread_scheduler_tape_oblivious
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    [HTO : TapeOblivious sch_int_σ sch] :
    TapeOblivious _ (force_first_thread_scheduler sch num initial) := by
  constructor
  intro ζ ρ ρ' h1 h2
  cases ζ with
  | none => rfl
  | some ζ' =>
    show dmap _ (sch (ζ', ρ)) = dmap _ (sch (ζ', ρ'))
    rw [HTO.tape_oblivious ζ' ρ ρ' h1 h2]

/-- Helper (not in Rocq): once started, `force_first_thread_scheduler` steps like `sch`. -/
theorem force_first_thread_scheduler_sch_step_or_final
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    (ζ : sch_int_σ) (ρ : CPState) :
    sch_step_or_final (force_first_thread_scheduler sch num initial) (some ζ, ρ) =
      dmap (fun p => (some p.1, p.2)) (sch_step_or_final sch (ζ, ρ)) := by
  by_cases hf : is_final ρ
  · rw [sch_step_or_final_is_final _ _ hf, sch_step_or_final_is_final _ _ hf, dmap_dret]
  · rw [sch_step_or_final_not_final _ _ hf, sch_step_or_final_not_final _ _ hf]
    unfold sch_step
    show dmap _ (sch (ζ, ρ)) ≫= _ = _
    rw [dmap_dbind_eq', dmap_dbind]
    refine dbind_ext_right _ _ _ fun q => ?_
    rw [dmap_comp]
    rfl

/-- Helper (not in Rocq): `sch_pexec` of a started `force_first_thread_scheduler`. -/
theorem force_first_thread_scheduler_sch_pexec
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    (n : ℕ) (ζ : sch_int_σ) (ρ : CPState) :
    sch_pexec (force_first_thread_scheduler sch num initial) n (some ζ, ρ) =
      dmap (fun p => (some p.1, p.2)) (sch_pexec sch n (ζ, ρ)) := by
  induction n generalizing ζ ρ with
  | zero => rw [sch_pexec_O, sch_pexec_O, dmap_dret]
  | succ n ih =>
    rw [sch_pexec_Sn, sch_pexec_Sn, force_first_thread_scheduler_sch_step_or_final,
      dmap_dbind_eq', dmap_dbind]
    exact dbind_ext_right _ _ _ fun q => ih q.1 q.2

/-- Rocq: `force_first_thread_scheduler_pexec_lemma`. -/
theorem force_first_thread_scheduler_pexec_lemma (ζ : sch_int_σ) (ρ : CPState)
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    (n : ℕ) :
    dmap (fun ρ => ρ.2.1) (sch_pexec sch n (ζ, ρ)) =
      dmap (fun ρ => ρ.2.1)
        (sch_pexec (force_first_thread_scheduler sch num initial) n (some ζ, ρ)) := by
  rw [force_first_thread_scheduler_sch_pexec, dmap_comp]
  rfl

/-- Helper (not in Rocq): the forced first step of `force_first_thread_scheduler`. -/
theorem force_first_thread_scheduler_first_step (e1 e : expr) (es1 : List expr) (σ1 : state)
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    (H : (e :: es1)[num]? = some e1) (Hv : to_val e = none) (Hv' : to_val e1 = none) :
    sch_step_or_final (force_first_thread_scheduler sch num initial) (none, (e :: es1, σ1)) =
      prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        dret (some initial, (((e :: es1).set num t.1 ++ t.2.2, t.2.1) : CPState)) := by
  have hnf : ¬ is_final (δ := con_lang_mdp con_prob_lang) (e :: es1, σ1) := by
    apply to_final_None_2
    simp [con_lang_mdp_to_final_eq, con_lang_mdp_to_final, Hv]
  rw [sch_step_or_final_not_final _ _ hnf]
  unfold sch_step
  show dret _ ≫= _ = _
  rw [dret_id_left]
  have hstep : (con_lang_mdp con_prob_lang).step num ((e :: es1, σ1) : CPState) =
      dmap (fun p => ((e :: es1).set num p.1 ++ p.2.2, p.2.1)) (prim_step (Λ := con_prob_lang) e1 σ1) := by
    simp only [con_lang_mdp_step_eq, con_lang_mdp_step]
    simp [H, Hv, Hv']
  rw [hstep]
  exact dmap_comp _ _ _

/-- Rocq: `force_first_thread_scheduler_pexec_lemma'`. -/
theorem force_first_thread_scheduler_pexec_lemma' (e1 e : expr) (es1 : List expr) (σ1 : state)
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    (n : ℕ) (H : (e :: es1)[num]? = some e1) (Hv : to_val e = none) (Hv' : to_val e1 = none) :
    dmap (fun ρ => ρ.2.1) (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_pexec sch n (initial, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))) =
      dmap (fun ρ => ρ.2.1)
        (sch_pexec (force_first_thread_scheduler sch num initial) (n + 1) (none, (e :: es1, σ1))) := by
  rw [sch_pexec_Sn, force_first_thread_scheduler_first_step e1 e es1 σ1 sch num initial H Hv Hv',
]
  refine (dmap_dbind _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (dmap _) (dbind_assoc _ _ _))
  refine Eq.trans ?_ (dmap_dbind _ _ _).symm
  refine dbind_ext_right _ _ _ fun t => ?_
  exact (force_first_thread_scheduler_pexec_lemma _ _ sch num initial n).trans
    (congrArg _ (dret_id_left _ _).symm)

end force_first_thread

/-- Rocq: `prim_coupl_step_prim_pexec_sch_erasable`. -/
theorem prim_coupl_step_prim_pexec_sch_erasable {sch_int_σ : Type u} [DecidableEq sch_int_σ]
    [Countable sch_int_σ] (e : expr) (n : ℕ) (es1 : List expr) (σ1 : state) (ζ : sch_int_σ)
    (e1 : expr) (num : ℕ) (μ : Distr state)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch]
    (H1 : sch_erasable (fun (t : Type u) _ _ sch => TapeOblivious t sch) μ σ1)
    (H2 : (e :: es1)[num]? = some e1) (H3 : to_val e = none) (H4 : to_val e1 = none) :
    Rcoupl
      (dmap (fun ρ => ρ.2.1) (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_pexec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))))
      (dmap (fun ρ => ρ.2.1) (μ ≫= fun σ2 => prim_step (Λ := con_prob_lang) e1 σ2 ≫= fun t =>
        sch_pexec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))))
      (· = ·) := by
  have HTO' := force_first_thread_scheduler_tape_oblivious sch num ζ
  have : dmap (fun ρ => ρ.2.1) (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_pexec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))) =
      dmap (fun ρ => ρ.2.1) (μ ≫= fun σ2 => prim_step (Λ := con_prob_lang) e1 σ2 ≫= fun t =>
        sch_pexec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))) := by
    refine (force_first_thread_scheduler_pexec_lemma' e1 e es1 σ1 sch num ζ n H2 H3 H4).trans ?_
    refine (H1 _ (force_first_thread_scheduler sch num ζ) (e :: es1) none (n + 1) HTO').symm.trans ?_
    refine (dmap_dbind _ _ _).trans (Eq.trans ?_ (dmap_dbind _ _ _).symm)
    exact dbind_ext_right _ _ _ fun σ2 =>
      (force_first_thread_scheduler_pexec_lemma' e1 e es1 σ2 sch num ζ n H2 H3 H4).symm
  rw [this]
  exact Rcoupl_eq _

/-- Rocq: `prim_coupl_step_prim_pexec'`. -/
theorem prim_coupl_step_prim_pexec' {sch_int_σ : Type*} [DecidableEq sch_int_σ]
    [Countable sch_int_σ] (e : expr) (n : ℕ) (es1 : List expr) (σ1 : state) (α : Loc) (bs : tape)
    (ζ : sch_int_σ) (e1 : expr) (num : ℕ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch]
    (H1 : σ1.tapes[α]? = some bs)
    (H2 : (e :: es1)[num]? = some e1) (H3 : to_val e = none) (H4 : to_val e1 = none) :
    Rcoupl
      (dmap (fun ρ => ρ.2.1) (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_pexec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))))
      (dmap (fun ρ => ρ.2.1) (state_step σ1 α ≫= fun σ2 =>
        prim_step (Λ := con_prob_lang) e1 σ2 ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))))
      (· = ·) :=
  prim_coupl_step_prim_pexec_sch_erasable e n es1 σ1 ζ e1 num _
    (state_step_sch_erasable σ1 α bs H1) H2 H3 H4

section force_first_thread

variable {sch_int_σ : Type*} [Countable sch_int_σ]

/-- Rocq: `force_first_thread_scheduler_lemma`. -/
theorem force_first_thread_scheduler_lemma (ζ : sch_int_σ) (ρ : CPState)
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    (n : ℕ) :
    sch_exec sch n (ζ, ρ) = sch_exec (force_first_thread_scheduler sch num initial) n (some ζ, ρ) := by
  induction n generalizing ζ ρ with
  | zero => rfl
  | succ n ih =>
    rw [sch_exec_Sn, sch_exec_Sn, force_first_thread_scheduler_sch_step_or_final, dmap_dbind_eq']
    exact dbind_ext_right _ _ _ fun q => ih q.1 q.2

/-- Rocq: `force_first_thread_scheduler_lemma'`. -/
theorem force_first_thread_scheduler_lemma' (e1 e : expr) (es1 : List expr) (σ1 : state)
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (num : ℕ) (initial : sch_int_σ)
    (n : ℕ) (H : (e :: es1)[num]? = some e1) (Hv : to_val e = none) (Hv' : to_val e1 = none) :
    (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_exec sch n (initial, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))) =
      sch_exec (force_first_thread_scheduler sch num initial) (n + 1) (none, (e :: es1, σ1)) := by
  rw [sch_exec_Sn, force_first_thread_scheduler_first_step e1 e es1 σ1 sch num initial H Hv Hv']
  refine Eq.trans ?_ (dbind_assoc _ _ _)
  refine dbind_ext_right _ _ _ fun t => ?_
  exact (force_first_thread_scheduler_lemma _ _ sch num initial n).trans (dret_id_left _ _).symm

end force_first_thread

/-- Rocq: `prim_coupl_step_prim_sch_erasable`. -/
theorem prim_coupl_step_prim_sch_erasable {sch_int_σ : Type u} [DecidableEq sch_int_σ]
    [Countable sch_int_σ] (e : expr) (n : ℕ) (es1 : List expr) (σ1 : state) (ζ : sch_int_σ)
    (e1 : expr) (num : ℕ) (μ : Distr state)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch]
    (H1 : sch_erasable (fun (t : Type u) _ _ sch => TapeOblivious t sch) μ σ1)
    (H2 : (e :: es1)[num]? = some e1) (H3 : to_val e = none) (H4 : to_val e1 = none) :
    Rcoupl
      (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_exec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1)))
      (μ ≫= fun σ2 => prim_step (Λ := con_prob_lang) e1 σ2 ≫= fun t =>
        sch_exec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1)))
      (· = ·) := by
  have H1' := sch_erasable_sch_erasable_val _ _ _ H1
  have HTO' := force_first_thread_scheduler_tape_oblivious sch num ζ
  have : (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_exec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))) =
      (μ ≫= fun σ2 => prim_step (Λ := con_prob_lang) e1 σ2 ≫= fun t =>
        sch_exec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1))) := by
    refine (force_first_thread_scheduler_lemma' e1 e es1 σ1 sch num ζ n H2 H3 H4).trans ?_
    refine (H1' _ (force_first_thread_scheduler sch num ζ) (e :: es1) none (n + 1) HTO').symm.trans ?_
    exact dbind_ext_right _ _ _ fun σ2 =>
      (force_first_thread_scheduler_lemma' e1 e es1 σ2 sch num ζ n H2 H3 H4).symm
  rw [this]
  exact Rcoupl_eq _

/-- Rocq: `prim_coupl_step_prim'`. -/
theorem prim_coupl_step_prim' {sch_int_σ : Type*} [DecidableEq sch_int_σ]
    [Countable sch_int_σ] (e : expr) (n : ℕ) (es1 : List expr) (σ1 : state) (α : Loc) (bs : tape)
    (ζ : sch_int_σ) (e1 : expr) (num : ℕ)
    {sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ} [HTO : TapeOblivious sch_int_σ sch]
    (H1 : σ1.tapes[α]? = some bs)
    (H2 : (e :: es1)[num]? = some e1) (H3 : to_val e = none) (H4 : to_val e1 = none) :
    Rcoupl
      (prim_step (Λ := con_prob_lang) e1 σ1 ≫= fun t =>
        sch_exec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1)))
      (state_step σ1 α ≫= fun σ2 => prim_step (Λ := con_prob_lang) e1 σ2 ≫= fun t =>
        sch_exec sch n (ζ, ((e :: es1).set num t.1 ++ t.2.2, t.2.1)))
      (· = ·) :=
  prim_coupl_step_prim_sch_erasable e n es1 σ1 ζ e1 num _
    (state_step_sch_erasable σ1 α bs H1) H2 H3 H4

end con_prob_lang

end ConProbLang
