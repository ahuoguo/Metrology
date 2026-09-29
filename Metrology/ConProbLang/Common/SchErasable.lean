module

public import Metrology.ConProbLang.Common.ConLanguage

/-!
# Scheduler-erasable state distributions

Ported from clutch/theories/common/sch_erasable.v

A distribution `μ` on states is *scheduler-erasable* at `σ` (relative to a class `P` of
schedulers) if, for every scheduler in `P`, first sampling a state from `μ` and then running the
scheduler yields the same distribution of thread pools as running it from `σ` directly.

Compared with the Rocq development:
* The section `Variable P` becomes an explicit argument
  `P : ∀ (t : Type v) [DecidableEq t] [Countable t], scheduler (con_lang_mdp Λ) t → Prop`
  of `sch_erasable` / `sch_erasable_val`, and of every lemma (Rocq: `Global Arguments P (_) {_ _} (_)`;
  in Lean too `P t sch` infers the instance arguments). The scheduler
  state lives in an arbitrary universe `v`.
* `μ σ' > 0` becomes `0 < μ σ'`; `SeriesC μ = 1` becomes `∑' a, μ a = 1`.
* In `sch_erasable_sch_lim_exec`, the Rocq `Sup_seq`/`MCT_seriesC` argument becomes the
  monotone-convergence theorem for `ℝ≥0∞` sums (`ENNReal.mul_iSup`, `tsum_iSup_of_monotone`),
  since `sch_lim_exec` is a pointwise `⨆`.
* The Rocq proof-local `g` of `sch_erasable_sch_erasable_val` is the helper definition
  `sch_erasable_final_of_threads`, with the helper lemma `sch_exec_final_of_threads`.
* The commented-out Rocq lemma `sch_erasable_dret_val` is not ported.
* Rocq `sch_erasable_dbind_predicate` binds its `Countable A` instance implicitly; here
  `[Countable A]`.

No tactics are defined in the Rocq file.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

universe v

section sch_erasable

variable {Λ : conLanguage}
variable (P : ∀ (t : Type v) [DecidableEq t] [Countable t], scheduler (con_lang_mdp Λ) t → Prop)

/-- Rocq: `sch_erasable`. -/
def sch_erasable (μ : Distr Λ.state) (σ : Λ.state) : Prop :=
  ∀ (sch_state : Type v) [DecidableEq sch_state] [Countable sch_state]
    (sch : scheduler (con_lang_mdp Λ) sch_state) (es : List Λ.expr) (ζ : sch_state) (m : ℕ),
    P sch_state sch →
    dmap (fun x => x.2.1) (μ ≫= fun σ' => sch_pexec sch m (ζ, (es, σ'))) =
      dmap (fun x => x.2.1) (sch_pexec sch m (ζ, (es, σ)))

/-- Rocq: `sch_erasable_val`. -/
def sch_erasable_val (μ : Distr Λ.state) (σ : Λ.state) : Prop :=
  ∀ (sch_state : Type v) [DecidableEq sch_state] [Countable sch_state]
    (sch : scheduler (con_lang_mdp Λ) sch_state) (es : List Λ.expr) (ζ : sch_state) (m : ℕ),
    P sch_state sch →
    (μ ≫= fun σ' => sch_exec sch m (ζ, (es, σ'))) = sch_exec sch m (ζ, (es, σ))

/-- Helper (the Rocq proof's local `g`): the final value of a thread pool, as a distribution. -/
def sch_erasable_final_of_threads (es : List Λ.expr) : Distr Λ.val :=
  match es[0]? >>= to_val with
  | some b => dret b
  | none => dzero

/-- Helper: in `sch_exec_pexec_relate`, the `to_final` continuation only depends on the thread
pool, so `sch_exec` factors through `dmap (fun x => x.2.1)`. -/
theorem sch_exec_final_of_threads {sch_state : Type v} [Countable sch_state]
    (sch : scheduler (con_lang_mdp Λ) sch_state) (n : ℕ)
    (ρ : sch_state × (con_lang_mdp Λ).mdpstate) :
    sch_exec sch n ρ = dmap (fun x => x.2.1) (sch_pexec sch n ρ) ≫= sch_erasable_final_of_threads := by
  rw [sch_exec_pexec_relate, dmap, ← dbind_assoc]
  refine dbind_ext_right _ _ _ fun ⟨ζ, es, σ⟩ => ?_
  rw [dret_id_left]
  simp only [con_lang_mdp_to_final_eq, con_lang_mdp_to_final, sch_erasable_final_of_threads]
  cases es[0]? with
  | none => rfl
  | some e => simp only [Option.bind_eq_bind, Option.bind_some]; cases to_val e <;> rfl

/-- Rocq: `sch_erasable_sch_erasable_val`. -/
theorem sch_erasable_sch_erasable_val (μ : Distr Λ.state) (σ : Λ.state) :
    sch_erasable P μ σ → sch_erasable_val P μ σ := by
  intro H0 sch_state _ _ sch es ζ n HP
  have H := H0 sch_state sch es ζ n HP
  rw [dbind_ext_right _ _ _ fun σ' => sch_exec_final_of_threads sch n (ζ, (es, σ')),
    sch_exec_final_of_threads, ← H]
  simp only [dmap, ← dbind_assoc]
  rfl

/-- Rocq: `sch_erasable_dbind`. -/
theorem sch_erasable_dbind (μ1 : Distr Λ.state) (μ2 : Λ.state → Distr Λ.state) (σ : Λ.state) :
    sch_erasable P μ1 σ → (∀ σ', 0 < μ1 σ' → sch_erasable P (μ2 σ') σ') →
      sch_erasable P (μ1 ≫= μ2) σ := by
  intro H1 H2 sch_state _ _ sch es ζ m HP
  rw [← dbind_assoc', ← H1 sch_state sch es ζ m HP, dmap, dmap, ← dbind_assoc, ← dbind_assoc]
  refine dbind_eq _ _ _ _ (fun σ' hσ' => ?_) (fun _ => rfl)
  have := H2 σ' hσ' sch_state sch es ζ m HP
  rw [dmap, dmap, ← dbind_assoc] at this
  rw [← dbind_assoc]
  exact this

/-- Rocq: `sch_erasable_sch_lim_exec`. -/
theorem sch_erasable_sch_lim_exec (μ : Distr Λ.state) {sch_state : Type v} [DecidableEq sch_state]
    [Countable sch_state] (sch : scheduler (con_lang_mdp Λ) sch_state) (σ : Λ.state)
    (es : List Λ.expr) (ζ : sch_state) :
    sch_erasable P μ σ → P sch_state sch →
      (μ ≫= fun σ' => sch_lim_exec sch (ζ, (es, σ'))) = sch_lim_exec sch (ζ, (es, σ)) := by
  intro Hs HP
  have He := sch_erasable_sch_erasable_val P μ σ Hs
  ext c
  rw [dbind_unfold_pmf, sch_lim_exec_unfold]
  simp only [sch_lim_exec_unfold, ENNReal.mul_iSup]
  rw [tsum_iSup_of_monotone (f := fun n a => μ a * sch_exec sch n (ζ, (es, a)) c)
    fun a => monotone_nat_of_le_succ fun n => mul_le_mul' le_rfl (sch_exec_mono sch _ n c)]
  refine iSup_congr fun n => ?_
  rw [← He sch_state sch es ζ n HP, dbind_unfold_pmf]

/-- Rocq: `sch_erasable_pexec_sch_lim_exec`. -/
theorem sch_erasable_pexec_sch_lim_exec {sch_state : Type v} [DecidableEq sch_state]
    [Countable sch_state] (sch : scheduler (con_lang_mdp Λ) sch_state) (μ : Distr Λ.state)
    (n : ℕ) (σ : Λ.state) (e : List Λ.expr) (ζ : sch_state) :
    sch_erasable P μ σ → P sch_state sch →
      ((μ ≫= fun σ' => sch_pexec sch n (ζ, (e, σ'))) ≫= sch_lim_exec sch) =
        sch_lim_exec sch (ζ, (e, σ)) := by
  intro Hμ HP
  rw [← sch_erasable_sch_lim_exec P μ sch σ e ζ Hμ HP, ← dbind_assoc]
  exact dbind_ext_right _ _ _ fun σ' => (sch_lim_exec_pexec sch n _).symm

/-- Rocq: `sch_erasable_dbind_predicate`. -/
theorem sch_erasable_dbind_predicate {A : Type*} [Countable A] (μ : Distr A)
    (μ1 μ2 : Distr Λ.state) (σ : Λ.state) (f : A → Bool) :
    ∑' a, μ a = 1 →
    sch_erasable P μ1 σ →
    sch_erasable P μ2 σ →
    sch_erasable P (μ ≫= fun x => if f x then μ1 else μ2) σ := by
  intro Hsum H1 H2 sch_state _ _ sch es ζ m HP
  rw [← dbind_assoc', dmap_dbind]
  rw [dbind_ext_right _ _ (fun _ => dmap (fun x => x.2.1) (sch_pexec sch m (ζ, (es, σ))))
    fun x => by
      cases f x
      · exact H2 sch_state sch es ζ m HP
      · exact H1 sch_state sch es ζ m HP]
  exact dbind_const _ _ Hsum

end sch_erasable

section sch_erasable_functions

/-- Rocq: `dret_sch_erasable`. -/
theorem dret_sch_erasable {Λ : conLanguage} (σ : Λ.state)
    (P : ∀ (t : Type v) [DecidableEq t] [Countable t], scheduler (con_lang_mdp Λ) t → Prop) :
    sch_erasable P (dret σ) σ := by
  intro sch_state _ _ sch es ζ m _
  rw [dret_id_left']

end sch_erasable_functions

end ConProbLang
