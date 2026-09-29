module

public import Metrology.Foxtrot.Oscheduler

/-!
# Full-information oblivious schedulers

Ported from clutch/theories/foxtrot/full_info.v

A *full-information* oblivious scheduler (`full_info_oscheduler`) is an oblivious scheduler whose
internal state is the whole history `full_info_state` of the execution: the list of
tape-erased configurations (`cfg'`) visited so far, each paired with the thread that was stepped
from it. This file builds such schedulers compositionally (`full_info_lift_osch`,
`full_info_cons_osch`, `full_info_stutter_osch`, `full_info_one_step_stutter_osch`,
`full_info_append_osch`) and computes their (limit) executions.

## Rocq → Lean map
* `cfg'`, `full_info_state`, `cfg_to_cfg'`, `full_info_oscheduler` (constructor `MkFullInfoOsch`,
  fields `fi_osch`, `fi_osch_tape_oblivious`, `fi_osch_valid`, `fi_osch_consistent`), and all
  lemmas: same names.
* The coercion `fi_osch :> oscheduler _` is a `Coe` instance plus a `CoeFun` instance (so both
  `osch_exec osch n ρ` and `osch (l, ρ)` work for `osch : full_info_oscheduler`); the typeclass
  field `fi_osch_tape_oblivious ::` is registered as an instance.
* `gmap loc val` is `Std.ExtTreeMap Loc val` (a `Countable` instance `heap_map_countable` is
  added here); `heap ρ.2` is `ρ.2.heap`.
* `prefix l l'` / `l `prefix_of` l'` is `l <+: l'`.
* `decide (∃ ..)` + `epsilon` is `if h : ∃ .. then .. Classical.choose h ..` (classical).
* Rocq `λ '(l, ρ), ...` pattern lambdas in scheduler definitions and in `dmap`s are written with
  projections `p.1`, `p.2`; `f <$> o` on options is `Option.map f o`.
* `full_info_cons_distr μ l ρ : Distr (full_info_state × CPAct)` (Rocq: `distr (_ * nat)`;
  `CPAct` is reducibly `ℕ`); `μ : cfg' → Distr ℕ` as in Rocq.
* Statements write the coercion explicitly: `osch_exec osch.fi_osch n ρ`,
  `osch_lim_exec osch.fi_osch ρ` (the `Coe` instance elaborates to the same term), while
  scheduler application is `osch (l, ρ)` (`= osch.fi_osch.oscheduler_f (l, ρ)`).
* `cfg_to_cfg'` and `full_info_cons_distr` take `ρ : CPState` (reducibly `cfg`), and the thread
  id `j` in `fi_osch_valid` / `full_info_cons_distr_valid` is `ℕ`, so that
  `l ++ [(cfg_to_cfg' ρ, j)] : full_info_state` elaborates.
* The file uses `open scoped Classical` (Rocq `decide` on propositions).
* `S n` is `n + 1`; `(x > 0)%R` is `0 < x`; reals are `ℝ≥0∞`.

## Deviations
* Proofs are restructured: `full_info_cons_osch_exec_n` and
  `full_info_append_osch_exec_prefix` are derived from a general helper
  `full_info_osch_exec_prefix_congr` (two full-information schedulers that agree on all
  histories extending a prefix have the same executions from such histories); the obligations of
  `full_info_cons_osch` / `full_info_append_osch` reuse the fields of the component schedulers.
  Limit arguments use monotone convergence (`dbind_Sup_seq`, `lim_distr_dbind_pmf`) instead of
  `SeriesC_Sup_seq_swap` and its side conditions.

## Added helpers (not in Rocq)
`heap_map_countable`, `cfg_to_cfg'_fst`, `full_info_lift_osch_none` (the lifted scheduler stops
outside its prefix), `full_info_cons_osch_nil` (the cons scheduler at the empty history),
`full_info_osch_exec_prefix_congr`, `dbind_pmf_le_strong`.

## Omissions
None (no setoid/Proper plumbing in the Rocq file).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

open scoped Classical

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate
set_option quotPrecheck false in
/-- The action type of `con_lang_mdp con_prob_lang` (reducibly `ℕ`). -/
local notation "CPAct" => (con_lang_mdp con_prob_lang).mdpaction

/-- Helper (not in Rocq): heaps are countable (Rocq: derived for `gmap loc val`). -/
instance heap_map_countable : Countable (Std.ExtTreeMap Loc val) := by
  refine Function.Injective.countable (f := fun m : Std.ExtTreeMap Loc val => m.toList) ?_
  intro m m' h
  exact Std.ExtTreeMap.toList_inj.1 h

/-- Helper (not in Rocq): pointwise monotonicity of `dbind` on the support. -/
theorem dbind_pmf_le_strong {α β : Type*} [Countable α] [Countable β] (μ : Distr α)
    (f g : α → Distr β) (b : β) (h : ∀ a, 0 < μ a → f a b ≤ g a b) :
    (μ ≫= f) b ≤ (μ ≫= g) b := by
  rw [dbind_unfold_pmf, dbind_unfold_pmf]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rcases eq_or_ne (μ a) 0 with h0 | h0
  · simp [h0]
  · exact mul_le_mul' le_rfl (h a (pos_iff_ne_zero.2 h0))

section full_info

/-- Rocq: `cfg'`. Tape-erased configurations. -/
abbrev cfg' : Type := List expr × Std.ExtTreeMap Loc val

/-- Rocq: `full_info_state`. The history: visited configurations and the thread stepped. -/
abbrev full_info_state : Type := List (cfg' × ℕ)

/-- Rocq: `cfg_to_cfg'`. -/
def cfg_to_cfg' (ρ : CPState) : cfg' := (ρ.1, ρ.2.heap)

@[simp] theorem cfg_to_cfg'_fst (ρ : CPState) : (cfg_to_cfg' ρ).1 = ρ.1 := rfl

/-- Rocq: `full_info_oscheduler`. -/
structure full_info_oscheduler where
  MkFullInfoOsch ::
  fi_osch : oscheduler full_info_state
  fi_osch_tape_oblivious : oTapeOblivious _ fi_osch
  fi_osch_valid : ∀ (l : full_info_state) (ρ : CPState) (j : ℕ) (l' : full_info_state) μ,
    fi_osch (l, ρ) = some μ → 0 < μ (l', j) → l' = l ++ [(cfg_to_cfg' ρ, j)]
  fi_osch_consistent : ∀ (l : full_info_state) (ρ : CPState), fi_osch (l, ρ) = none →
    ∀ ρ', fi_osch (l, ρ') = none

attribute [instance] full_info_oscheduler.fi_osch_tape_oblivious

instance : Coe full_info_oscheduler (oscheduler full_info_state) :=
  ⟨full_info_oscheduler.fi_osch⟩

instance : CoeFun full_info_oscheduler
    (fun _ => full_info_state × CPState → Option (Distr (full_info_state × CPAct))) :=
  ⟨fun o => o.fi_osch.oscheduler_f⟩

/-- Rocq: `full_info_reachable_prefix`. -/
theorem full_info_reachable_prefix (osch : full_info_oscheduler) (n : ℕ) (l : full_info_state)
    (ρ : CPState) (l' : full_info_state) (ρ' : CPState)
    (H : 0 < osch_exec osch.fi_osch n (l, ρ) (l', ρ')) : l <+: l' := by
  induction n generalizing l ρ with
  | zero =>
    cases h : osch.fi_osch (l, ρ) with
    | none =>
      rw [osch_exec_is_none _ _ _ h] at H
      cases dret_pos _ _ H
      exact List.prefix_refl _
    | some μ =>
      rw [osch_exec_0 _ _ ⟨μ, h⟩] at H
      exact absurd H (dzero_supp_empty _)
  | succ n ih =>
    cases h : osch.fi_osch (l, ρ) with
    | none =>
      rw [osch_exec_is_none _ _ _ h] at H
      cases dret_pos _ _ H
      exact List.prefix_refl _
    | some μ =>
      simp only [osch_exec, h] at H
      obtain ⟨p, H1, H2⟩ := (dbind_pos _ _ _).1 H
      obtain ⟨σ', H3, -⟩ := (dbind_pos _ _ _).1 H1
      have hp := osch.fi_osch_valid l ρ p.2 p.1 μ h H2
      have := ih p.1 σ' H3
      rw [hp] at this
      exact (List.prefix_append _ _).trans this

/-- Rocq: `full_info_lim_reachable_prefix`. -/
theorem full_info_lim_reachable_prefix (osch : full_info_oscheduler) (l : full_info_state)
    (ρ : CPState) (l' : full_info_state) (ρ' : CPState)
    (H : 0 < osch_lim_exec osch.fi_osch (l, ρ) (l', ρ')) : l <+: l' := by
  obtain ⟨n, H⟩ := osch_lim_exec_pos _ _ _ H
  exact full_info_reachable_prefix osch n l ρ l' ρ' H

/-- Rocq: `is_frontier_n`. -/
def is_frontier_n (l : full_info_state) (n : ℕ) (initial_l : full_info_state)
    (osch : full_info_oscheduler) : Prop :=
  ∃ ρ ρ' : CPState, 0 < osch_exec osch.fi_osch n (initial_l, ρ) (l, ρ')

/-- Rocq: `is_frontier`. -/
def is_frontier (l : full_info_state) (initial_l : full_info_state)
    (osch : full_info_oscheduler) : Prop :=
  ∃ ρ ρ' : CPState, 0 < osch_lim_exec osch.fi_osch (initial_l, ρ) (l, ρ')

/-- Rocq: `is_frontier_None`. -/
theorem is_frontier_None (l initial_l : full_info_state) (osch : full_info_oscheduler)
    (ρ : CPState) (H : is_frontier l initial_l osch) : osch (l, ρ) = none := by
  obtain ⟨ρ0, ρ', H⟩ := H
  exact osch.fi_osch_consistent l ρ' (osch_lim_exec_pos_res _ _ _ H) ρ

/-- Rocq: `is_frontier_n_prefix_unique`. -/
theorem is_frontier_n_prefix_unique (n : ℕ) (initial_l l l' : full_info_state)
    (osch : full_info_oscheduler) (H1 : is_frontier_n l n initial_l osch)
    (H2 : is_frontier_n l' n initial_l osch) (Hp : l <+: l') : l = l' := by
  induction n generalizing l l' initial_l with
  | zero =>
    obtain ⟨ρ1, ρ1', H1⟩ := H1
    obtain ⟨ρ2, ρ2', H2⟩ := H2
    cases h : osch.fi_osch (initial_l, ρ2) with
    | some μ =>
      rw [osch_exec_0 _ _ ⟨μ, h⟩] at H2
      exact absurd H2 (dzero_supp_empty _)
    | none =>
      rw [osch_exec_is_none _ _ _ h] at H2
      rw [osch_exec_is_none _ _ _ (osch.fi_osch_consistent _ _ h ρ1)] at H1
      cases dret_pos _ _ H1
      cases dret_pos _ _ H2
      rfl
  | succ n ih =>
    obtain ⟨ρ1, ρ1', H1⟩ := H1
    obtain ⟨ρ2, ρ2', H2⟩ := H2
    cases h2 : osch.fi_osch (initial_l, ρ2) with
    | none =>
      rw [osch_exec_is_none _ _ _ h2] at H2
      rw [osch_exec_is_none _ _ _ (osch.fi_osch_consistent _ _ h2 ρ1)] at H1
      cases dret_pos _ _ H1
      cases dret_pos _ _ H2
      rfl
    | some μ2 =>
      cases h1 : osch.fi_osch (initial_l, ρ1) with
      | none => rw [osch.fi_osch_consistent _ _ h1 ρ2] at h2; cases h2
      | some μ1 =>
        simp only [osch_exec, h1] at H1
        simp only [osch_exec, h2] at H2
        obtain ⟨p1, H1a, H1b⟩ := (dbind_pos _ _ _).1 H1
        obtain ⟨σ1, H1c, -⟩ := (dbind_pos _ _ _).1 H1a
        obtain ⟨p2, H2a, H2b⟩ := (dbind_pos _ _ _).1 H2
        obtain ⟨σ2, H2c, -⟩ := (dbind_pos _ _ _).1 H2a
        have hv1 := osch.fi_osch_valid _ _ _ _ _ h1 H1b
        have hv2 := osch.fi_osch_valid _ _ _ _ _ h2 H2b
        have hpre1 := (full_info_reachable_prefix osch n _ _ _ _ H1c).trans Hp
        have hpre2 := full_info_reachable_prefix osch n _ _ _ _ H2c
        have heq : p1.1 = p2.1 :=
          (List.prefix_of_prefix_length_le hpre1 hpre2 (by simp [hv1, hv2])).eq_of_length
            (by simp [hv1, hv2])
        refine ih p2.1 l l' ⟨σ1, ρ1', ?_⟩ ⟨σ2, ρ2', H2c⟩ Hp
        rw [← heq]
        exact H1c

/-- Rocq: `is_frontier_prefix_unique`. -/
theorem is_frontier_prefix_unique (initial_l l l' : full_info_state)
    (osch : full_info_oscheduler) (H1 : is_frontier l initial_l osch)
    (H2 : is_frontier l' initial_l osch) (Hp : l <+: l') : l = l' := by
  obtain ⟨ρ1, ρ1', H1⟩ := H1
  obtain ⟨ρ2, ρ2', H2⟩ := H2
  obtain ⟨n, H1⟩ := osch_lim_exec_pos _ _ _ H1
  obtain ⟨m, H2⟩ := osch_lim_exec_pos _ _ _ H2
  rcases le_total n m with h | h
  · exact is_frontier_n_prefix_unique m initial_l l l' osch
      ⟨ρ1, ρ1', lt_of_lt_of_le H1 (osch_exec_mono' _ _ _ _ _ h)⟩ ⟨ρ2, ρ2', H2⟩ Hp
  · exact is_frontier_n_prefix_unique n initial_l l l' osch ⟨ρ1, ρ1', H1⟩
      ⟨ρ2, ρ2', lt_of_lt_of_le H2 (osch_exec_mono' _ _ _ _ _ h)⟩ Hp

/-! ### Do nothing oscheduler -/

/-- Rocq: `full_info_inhabitant`. -/
def full_info_inhabitant : full_info_oscheduler where
  fi_osch := ⟨fun _ => none⟩
  fi_osch_tape_oblivious := ⟨fun _ _ _ _ _ => rfl⟩
  fi_osch_valid := fun _ _ _ _ _ h _ => by cases h
  fi_osch_consistent := fun _ _ _ _ => rfl

/-- Rocq: `full_info_inhabitant_lim_exec`. -/
theorem full_info_inhabitant_lim_exec (x : full_info_state × CPState) :
    osch_lim_exec full_info_inhabitant.fi_osch x = dret x :=
  osch_lim_exec_None _ _ rfl

/-! ### Append a prefix list to every state -/

/-- Rocq: `full_info_lift_osch`. -/
def full_info_lift_osch (prel : full_info_state) (osch : full_info_oscheduler) :
    full_info_oscheduler where
  fi_osch := ⟨fun p =>
    if h : ∃ sufl, p.1 = prel ++ sufl then
      Option.map (dmap fun q : full_info_state × CPAct => (prel ++ q.1, q.2))
        (osch (Classical.choose h, p.2))
    else none⟩
  fi_osch_tape_oblivious := ⟨fun ζ ρ ρ' h1 h2 => by
    dsimp only
    split
    · rw [osch.fi_osch_tape_oblivious.otape_oblivious _ ρ ρ' h1 h2]
    · rfl⟩
  fi_osch_valid := fun l ρ j l' μ H Hpos => by
    dsimp only at H
    split at H
    · rename_i h
      obtain ⟨μ0, H0, rfl⟩ := Option.map_eq_some_iff.1 H
      obtain ⟨q, hq, hq'⟩ := (dmap_pos _ _ _).1 Hpos
      have hv := osch.fi_osch_valid _ _ _ _ _ H0 hq'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
      rw [hv, ← List.append_assoc, ← Classical.choose_spec h]
    · cases H
  fi_osch_consistent := fun l ρ H ρ' => by
    dsimp only at H ⊢
    split at H
    · rename_i h
      rw [dite_eq_left h, Option.map_eq_none_iff.2
        (osch.fi_osch_consistent _ _ (Option.map_eq_none_iff.1 H) ρ')]
    · rename_i h
      rw [dite_eq_right h]

/-- Rocq: `full_info_lift_osch_unfold`. -/
theorem full_info_lift_osch_unfold (prel : full_info_state) (osch : full_info_oscheduler)
    (l : full_info_state) (ρ : CPState) :
    full_info_lift_osch prel osch (prel ++ l, ρ) =
      Option.map (dmap fun q : full_info_state × CPAct => (prel ++ q.1, q.2)) (osch (l, ρ)) := by
  have h : ∃ sufl, prel ++ l = prel ++ sufl := ⟨l, rfl⟩
  have hc : Classical.choose h = l := (List.append_cancel_left (Classical.choose_spec h)).symm
  change (if h : ∃ sufl, prel ++ l = prel ++ sufl then
      Option.map (dmap fun q : full_info_state × CPAct => (prel ++ q.1, q.2))
        (osch (Classical.choose h, ρ)) else none) = _
  rw [dite_eq_left h, hc]

/-- Helper (not in Rocq): the lifted scheduler stops on histories not extending the prefix. -/
theorem full_info_lift_osch_none (prel : full_info_state) (osch : full_info_oscheduler)
    (l : full_info_state) (ρ : CPState) (h : ¬ ∃ sufl, l = prel ++ sufl) :
    full_info_lift_osch prel osch (l, ρ) = none := by
  change (if h : ∃ sufl, l = prel ++ sufl then _ else none) = none
  rw [dite_eq_right h]

/-- Rocq: `full_info_lift_osch_exec`. -/
theorem full_info_lift_osch_exec (prel : full_info_state) (osch : full_info_oscheduler) (n : ℕ)
    (l : full_info_state) (ρ : CPState) :
    osch_exec (full_info_lift_osch prel osch).fi_osch n (prel ++ l, ρ) =
      dmap (fun p : full_info_state × CPState => (prel ++ p.1, p.2))
        (osch_exec osch.fi_osch n (l, ρ)) := by
  induction n generalizing l ρ with
  | zero =>
    cases h : osch.fi_osch (l, ρ) with
    | none =>
      have h' : (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) = none := by
        rw [show (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) =
          full_info_lift_osch prel osch (prel ++ l, ρ) from rfl, full_info_lift_osch_unfold]
        exact Option.map_eq_none_iff.2 h
      rw [osch_exec_is_none _ _ _ h, osch_exec_is_none _ _ _ h', dmap_dret]
    | some μ =>
      have h' : (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) = some (dmap (fun q : full_info_state × CPAct => (prel ++ q.1, q.2)) μ) := by
        rw [show (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) =
          full_info_lift_osch prel osch (prel ++ l, ρ) from rfl, full_info_lift_osch_unfold]
        exact congrArg _ h
      rw [osch_exec_0 _ _ ⟨μ, h⟩, osch_exec_0 _ _ ⟨_, h'⟩, dmap_dzero]
  | succ n ih =>
    cases h : osch.fi_osch (l, ρ) with
    | none =>
      have h' : (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) = none := by
        rw [show (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) =
          full_info_lift_osch prel osch (prel ++ l, ρ) from rfl, full_info_lift_osch_unfold]
        exact Option.map_eq_none_iff.2 h
      rw [osch_exec_is_none _ _ _ h, osch_exec_is_none _ _ _ h', dmap_dret]
    | some μ =>
      have h' : (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) =
          some (dmap (fun q : full_info_state × CPAct => (prel ++ q.1, q.2)) μ) := by
        rw [show (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) =
          full_info_lift_osch prel osch (prel ++ l, ρ) from rfl, full_info_lift_osch_unfold]
        exact congrArg _ h
      simp only [osch_exec, h, h']
      rw [dmap, ← dbind_assoc, dmap_dbind]
      refine dbind_ext_right _ _ _ fun q => ?_
      rw [dret_id_left, dmap_dbind]
      exact dbind_ext_right _ _ _ fun σ' => ih q.1 σ'

/-- Rocq: `full_info_lift_osch_lim_exec`. -/
theorem full_info_lift_osch_lim_exec (prel : full_info_state) (osch : full_info_oscheduler)
    (l : full_info_state) (ρ : CPState) :
    osch_lim_exec (full_info_lift_osch prel osch).fi_osch (prel ++ l, ρ) =
      dmap (fun p : full_info_state × CPState => (prel ++ p.1, p.2))
        (osch_lim_exec osch.fi_osch (l, ρ)) := by
  ext x
  rw [osch_lim_exec_unfold]
  simp only [full_info_lift_osch_exec]
  unfold dmap osch_lim_exec
  rw [lim_distr_dbind_pmf]

/-- Helper (not in Rocq): two full-information schedulers that agree on every history
extending `P` have the same executions from such histories. -/
theorem full_info_osch_exec_prefix_congr (o1 o2 : full_info_oscheduler) (P : full_info_state)
    (H : ∀ l ρ, o1 (P ++ l, ρ) = o2 (P ++ l, ρ)) (n : ℕ) (l : full_info_state) (ρ : CPState) :
    osch_exec o1.fi_osch n (P ++ l, ρ) = osch_exec o2.fi_osch n (P ++ l, ρ) := by
  have H' : ∀ l ρ, o1.fi_osch (P ++ l, ρ) = o2.fi_osch (P ++ l, ρ) := H
  induction n generalizing l ρ with
  | zero =>
    cases h : o2.fi_osch (P ++ l, ρ) with
    | none =>
      rw [osch_exec_is_none _ _ _ h, osch_exec_is_none _ _ _ ((H' l ρ).trans h)]
    | some μ =>
      rw [osch_exec_0 _ _ ⟨μ, h⟩, osch_exec_0 _ _ ⟨μ, (H' l ρ).trans h⟩]
  | succ n ih =>
    cases h : o2.fi_osch (P ++ l, ρ) with
    | none =>
      rw [osch_exec_is_none _ _ _ h, osch_exec_is_none _ _ _ ((H' l ρ).trans h)]
    | some μ =>
      simp only [osch_exec, h, (H' l ρ).trans h]
      refine dbind_ext_right_strong _ _ _ fun q hq => ?_
      have hv := o2.fi_osch_valid _ _ _ _ _ h hq
      refine dbind_ext_right _ _ _ fun σ' => ?_
      obtain ⟨q1, q2⟩ := q
      dsimp only at hv ⊢
      subst hv
      rw [List.append_assoc]
      exact ih _ _

/-- Rocq: `full_info_cons_distr`. -/
def full_info_cons_distr (μ : cfg' → Distr ℕ) (l : full_info_state) (ρ : CPState) :
    Distr (full_info_state × CPAct) :=
  dmap (fun n : ℕ => ((l ++ [(cfg_to_cfg' ρ, n)], n) : full_info_state × CPAct))
    (μ (cfg_to_cfg' ρ))

/-- Rocq: `full_info_cons_distr_tape_oblivious`. -/
theorem full_info_cons_distr_tape_oblivious (μ : cfg' → Distr ℕ) (l : full_info_state)
    (ρ1 ρ2 : CPState) (h : cfg_to_cfg' ρ1 = cfg_to_cfg' ρ2) :
    full_info_cons_distr μ l ρ1 = full_info_cons_distr μ l ρ2 := by
  unfold full_info_cons_distr
  rw [h]

/-- Rocq: `full_info_cons_distr_valid`. -/
theorem full_info_cons_distr_valid (μ : cfg' → Distr ℕ) (l : full_info_state) (ρ : CPState)
    (l' : full_info_state) (j : ℕ) (Hpos : 0 < full_info_cons_distr μ l ρ (l', j)) :
    l' = l ++ [(cfg_to_cfg' ρ, j)] := by
  obtain ⟨n, hn, -⟩ := (dmap_pos _ _ _).1 Hpos
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hn
  rfl

/-- Rocq: `full_info_cons_osch`. A way of building a scheduler that conses one step into many
different states, each of which continues with a different scheduler. -/
def full_info_cons_osch (μ : cfg' → Distr ℕ) (f : ℕ → full_info_oscheduler) :
    full_info_oscheduler where
  fi_osch := ⟨fun p =>
    if h : ∃ hd, ∃ tl, p.1 = hd :: tl then
      full_info_lift_osch [Classical.choose h] (f (Classical.choose h).2) p
    else some (full_info_cons_distr μ [] p.2)⟩
  fi_osch_tape_oblivious := ⟨fun ζ ρ ρ' h1 h2 => by
    dsimp only
    split
    · exact (full_info_lift_osch _ _).fi_osch_tape_oblivious.otape_oblivious _ ρ ρ' h1 h2
    · rw [full_info_cons_distr_tape_oblivious μ [] ρ ρ' (Prod.ext h1 h2)]⟩
  fi_osch_valid := fun l ρ j l' μ' H Hpos => by
    dsimp only at H
    split at H
    · exact (full_info_lift_osch _ _).fi_osch_valid _ _ _ _ _ H Hpos
    · rename_i h
      have hl : l = [] := by
        rcases l with _ | ⟨hd, tl⟩
        · rfl
        · exact absurd ⟨hd, tl, rfl⟩ h
      cases H
      subst hl
      exact full_info_cons_distr_valid μ [] ρ l' j Hpos
  fi_osch_consistent := fun l ρ H ρ' => by
    dsimp only at H ⊢
    split at H
    · rename_i h
      rw [dite_eq_left h]
      exact (full_info_lift_osch _ _).fi_osch_consistent _ _ H ρ'
    · cases H

/-- Rocq: `full_info_cons_osch_unfold`. -/
theorem full_info_cons_osch_unfold (μ : cfg' → Distr ℕ) (f : ℕ → full_info_oscheduler)
    (x : cfg') (a : ℕ) (l : full_info_state) (ρ : CPState) :
    full_info_cons_osch μ f ([(x, a)] ++ l, ρ) =
      full_info_lift_osch [(x, a)] (f a) ([(x, a)] ++ l, ρ) := by
  have h : ∃ hd, ∃ tl, [(x, a)] ++ l = hd :: tl := ⟨(x, a), l, rfl⟩
  have hc : Classical.choose h = (x, a) := by
    obtain ⟨tl, htl⟩ := Classical.choose_spec h
    exact (List.cons.inj htl).1.symm
  change (if h : ∃ hd, ∃ tl, [(x, a)] ++ l = hd :: tl then
      full_info_lift_osch [Classical.choose h] (f (Classical.choose h).2) ([(x, a)] ++ l, ρ)
    else some (full_info_cons_distr μ [] ρ)) = _
  rw [dite_eq_left h, hc]

/-- Helper: the cons scheduler at the empty history. -/
theorem full_info_cons_osch_nil (μ : cfg' → Distr ℕ) (f : ℕ → full_info_oscheduler)
    (ρ : CPState) :
    full_info_cons_osch μ f ([], ρ) = some (full_info_cons_distr μ [] ρ) := by
  have h : ¬ ∃ hd, ∃ tl, ([] : full_info_state) = hd :: tl := by
    rintro ⟨_, _, h⟩; cases h
  change (if h : ∃ hd, ∃ tl, ([] : full_info_state) = hd :: tl then _ else _) = _
  rw [dite_eq_right h]

/-- Rocq: `full_info_cons_osch_exec_0`. -/
theorem full_info_cons_osch_exec_0 (μ : cfg' → Distr ℕ) (f : ℕ → full_info_oscheduler)
    (ρ : CPState) : osch_exec (full_info_cons_osch μ f).fi_osch 0 ([], ρ) = dzero :=
  osch_exec_0 _ _ ⟨_, full_info_cons_osch_nil μ f ρ⟩

/-- Rocq: `full_info_cons_osch_exec_n`. -/
theorem full_info_cons_osch_exec_n (μ : cfg' → Distr ℕ) (f : ℕ → full_info_oscheduler)
    (ρ : CPState) (a : ℕ) (x : cfg') (n : ℕ) (l : full_info_state) :
    osch_exec (full_info_cons_osch μ f).fi_osch n ([(x, a)] ++ l, ρ) =
      dmap (fun p : full_info_state × CPState => ([(x, a)] ++ p.1, p.2))
        (osch_exec (f a).fi_osch n (l, ρ)) := by
  rw [full_info_osch_exec_prefix_congr _ (full_info_lift_osch [(x, a)] (f a)) [(x, a)]
    (fun l ρ => full_info_cons_osch_unfold μ f x a l ρ), full_info_lift_osch_exec]

/-- Rocq: `full_info_cons_osch_exec_Sn`. -/
theorem full_info_cons_osch_exec_Sn (μ : cfg' → Distr ℕ) (f : ℕ → full_info_oscheduler) (n : ℕ)
    (ρ : CPState) :
    osch_exec (full_info_cons_osch μ f).fi_osch (n + 1) ([], ρ) =
      μ (cfg_to_cfg' ρ) ≫= fun x => step' x ρ ≫= fun ρ' =>
        osch_exec (full_info_lift_osch [(cfg_to_cfg' ρ, x)] (f x)).fi_osch n
          ([(cfg_to_cfg' ρ, x)], ρ') := by
  have h : (full_info_cons_osch μ f).fi_osch ([], ρ) = some (full_info_cons_distr μ [] ρ) :=
    full_info_cons_osch_nil μ f ρ
  simp only [osch_exec, h]
  unfold full_info_cons_distr
  rw [dmap, ← dbind_assoc]
  refine dbind_ext_right _ _ _ fun x => ?_
  rw [dret_id_left]
  refine dbind_ext_right _ _ _ fun σ' => ?_
  have := full_info_osch_exec_prefix_congr _ (full_info_lift_osch [(cfg_to_cfg' ρ, x)] (f x))
    [(cfg_to_cfg' ρ, x)] (fun l ρ' => full_info_cons_osch_unfold μ f _ x l ρ') n [] σ'
  simpa using this

/-- Rocq: `full_info_cons_osch_lim_exec`. -/
theorem full_info_cons_osch_lim_exec (μ : cfg' → Distr ℕ) (f : ℕ → full_info_oscheduler)
    (ρ : CPState) :
    osch_lim_exec (full_info_cons_osch μ f).fi_osch ([], ρ) =
      μ (cfg_to_cfg' ρ) ≫= fun x => step' x ρ ≫= fun ρ' =>
        osch_lim_exec (full_info_lift_osch [(cfg_to_cfg' ρ, x)] (f x)).fi_osch
          ([(cfg_to_cfg' ρ, x)], ρ') := by
  ext b
  rw [osch_lim_exec_unfold]
  rw [← Monotone.iSup_nat_add (monotone_nat_of_le_succ fun n =>
    osch_exec_mono (full_info_cons_osch μ f).fi_osch ([], ρ) n b) 1]
  simp only [full_info_cons_osch_exec_Sn]
  refine (dbind_Sup_seq (fun n x => step' x ρ ≫= fun ρ' =>
      osch_exec (full_info_lift_osch [(cfg_to_cfg' ρ, x)] (f x)).fi_osch n
        ([(cfg_to_cfg' ρ, x)], ρ')) _ _ b (fun x => ?_) (fun n x => ?_)).symm
  · exact dbind_Sup_seq _ _ _ b (fun _ => rfl) (fun n _ => osch_exec_mono _ _ n b)
  · exact dbind_pmf_le_strong _ _ _ b fun _ _ => osch_exec_mono _ _ n b

/-! ### Stutter steps -/

/-- Rocq: `full_info_stutter_osch`. This oscheduler performs a stutter step. -/
def full_info_stutter_osch (osch : full_info_oscheduler) : full_info_oscheduler :=
  full_info_cons_osch (fun ρ => dret ρ.1.length) (fun _ => osch)

/-- Rocq: `full_info_stutter_osch_lim_exec`. -/
theorem full_info_stutter_osch_lim_exec (ρ : CPState) (osch : full_info_oscheduler) :
    osch_lim_exec (full_info_stutter_osch osch).fi_osch ([], ρ) =
      dmap (fun p : full_info_state × CPState => ([(cfg_to_cfg' ρ, ρ.1.length)] ++ p.1, p.2))
        (osch_lim_exec osch.fi_osch ([], ρ)) := by
  unfold full_info_stutter_osch
  rw [full_info_cons_osch_lim_exec, dret_id_left]
  simp only [cfg_to_cfg'_fst]
  rw [out_of_bounds_step' _ _ le_rfl, dret_id_left]
  have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, ρ.1.length)] osch [] ρ
  simpa using this

/-- Rocq: `full_info_one_step_stutter_osch`. -/
def full_info_one_step_stutter_osch (j : ℕ) : full_info_oscheduler :=
  full_info_cons_osch (fun _ => dret j) (fun _ => full_info_stutter_osch full_info_inhabitant)

/-- Rocq: `full_info_one_step_stutter_osch_lim_exec`. -/
theorem full_info_one_step_stutter_osch_lim_exec (j : ℕ) (ρ : CPState) :
    osch_lim_exec (full_info_one_step_stutter_osch j).fi_osch ([], ρ) =
      dmap (fun ρ' : CPState =>
        (([(cfg_to_cfg' ρ, j), (cfg_to_cfg' ρ', ρ'.1.length)] : full_info_state), ρ'))
        (step' j ρ) := by
  unfold full_info_one_step_stutter_osch
  rw [full_info_cons_osch_lim_exec, dret_id_left, dmap]
  refine dbind_ext_right _ _ _ fun ρ' => ?_
  have := full_info_lift_osch_lim_exec [(cfg_to_cfg' ρ, j)]
    (full_info_stutter_osch full_info_inhabitant) [] ρ'
  simp only [List.append_nil] at this
  rw [this, full_info_stutter_osch_lim_exec, full_info_inhabitant_lim_exec, dmap_dret, dmap_dret]
  rfl

/-! ### Appending schedulers at the frontier of another -/

/-- Rocq: `full_info_append_osch`. A way of building a scheduler by appending schedulers at the
frontier of another. -/
def full_info_append_osch (osch : full_info_oscheduler)
    (f : full_info_state → full_info_oscheduler) : full_info_oscheduler where
  fi_osch := ⟨fun p =>
    if h : ∃ prel, prel <+: p.1 ∧ is_frontier prel [] osch then
      full_info_lift_osch (Classical.choose h) (f (Classical.choose h)) p
    else osch p⟩
  fi_osch_tape_oblivious := ⟨fun ζ ρ ρ' h1 h2 => by
    dsimp only
    split
    · exact (full_info_lift_osch _ _).fi_osch_tape_oblivious.otape_oblivious _ ρ ρ' h1 h2
    · exact osch.fi_osch_tape_oblivious.otape_oblivious _ ρ ρ' h1 h2⟩
  fi_osch_valid := fun l ρ j l' μ H Hpos => by
    dsimp only at H
    split at H
    · exact (full_info_lift_osch _ _).fi_osch_valid _ _ _ _ _ H Hpos
    · exact osch.fi_osch_valid _ _ _ _ _ H Hpos
  fi_osch_consistent := fun l ρ H ρ' => by
    dsimp only at H ⊢
    split at H
    · rename_i h
      rw [dite_eq_left h]
      exact (full_info_lift_osch _ _).fi_osch_consistent _ _ H ρ'
    · rename_i h
      rw [dite_eq_right h]
      exact osch.fi_osch_consistent _ _ H ρ'

/-- Rocq: `is_frontier_prefix_lemma`. -/
theorem is_frontier_prefix_lemma (prel prel' : full_info_state) (osch : full_info_oscheduler)
    (l : full_info_state) (H1 : prel <+: l) (H2 : is_frontier prel [] osch) (H3 : prel' <+: l)
    (H4 : is_frontier prel' [] osch) : prel = prel' := by
  rcases List.prefix_or_prefix_of_prefix H1 H3 with h | h
  · exact is_frontier_prefix_unique [] _ _ osch H2 H4 h
  · exact (is_frontier_prefix_unique [] _ _ osch H4 H2 h).symm

/-- Rocq: `full_info_append_osch_prefix`. -/
theorem full_info_append_osch_prefix (prel : full_info_state) (osch : full_info_oscheduler)
    (f : full_info_state → full_info_oscheduler) (l : full_info_state) (ρ : CPState)
    (Hf : is_frontier prel [] osch) :
    full_info_append_osch osch f (prel ++ l, ρ) =
      full_info_lift_osch prel (f prel) (prel ++ l, ρ) := by
  have h : ∃ p, p <+: prel ++ l ∧ is_frontier p [] osch := ⟨prel, List.prefix_append _ _, Hf⟩
  have hc : Classical.choose h = prel :=
    is_frontier_prefix_lemma _ _ osch (prel ++ l) (Classical.choose_spec h).1
      (Classical.choose_spec h).2 (List.prefix_append _ _) Hf
  change (if h : ∃ p, p <+: prel ++ l ∧ is_frontier p [] osch then
      full_info_lift_osch (Classical.choose h) (f (Classical.choose h)) (prel ++ l, ρ)
    else osch (prel ++ l, ρ)) = _
  rw [dite_eq_left h, hc]

/-- Rocq: `full_info_append_osch_not_prefix`. -/
theorem full_info_append_osch_not_prefix (osch : full_info_oscheduler)
    (f : full_info_state → full_info_oscheduler) (l : full_info_state) (ρ : CPState)
    (H : ¬ ∃ prel, prel <+: l ∧ is_frontier prel [] osch) :
    full_info_append_osch osch f (l, ρ) = osch (l, ρ) := by
  change (if h : ∃ p, p <+: l ∧ is_frontier p [] osch then _ else osch (l, ρ)) = _
  rw [dite_eq_right H]

/-- Rocq: `full_info_append_osch_exec_prefix`. -/
theorem full_info_append_osch_exec_prefix (prel l : full_info_state)
    (osch : full_info_oscheduler) (f : full_info_state → full_info_oscheduler) (n : ℕ)
    (ρ : CPState) (Hf : is_frontier prel [] osch) :
    osch_exec (full_info_append_osch osch f).fi_osch n (prel ++ l, ρ) =
      osch_exec (full_info_lift_osch prel (f prel)).fi_osch n (prel ++ l, ρ) :=
  full_info_osch_exec_prefix_congr _ _ prel
    (fun l ρ => full_info_append_osch_prefix prel osch f l ρ Hf) n l ρ

/-- Rocq: `full_info_append_osch_lim_exec_prefix`. -/
theorem full_info_append_osch_lim_exec_prefix (prel l : full_info_state)
    (osch : full_info_oscheduler) (f : full_info_state → full_info_oscheduler) (ρ : CPState)
    (Hf : is_frontier prel [] osch) :
    osch_lim_exec (full_info_append_osch osch f).fi_osch (prel ++ l, ρ) =
      osch_lim_exec (full_info_lift_osch prel (f prel)).fi_osch (prel ++ l, ρ) := by
  ext x
  simp only [osch_lim_exec_unfold, full_info_append_osch_exec_prefix prel l osch f _ ρ Hf]

/-- Rocq: `append_one_frontier`. -/
theorem append_one_frontier (l : full_info_state) (osch : full_info_oscheduler)
    (x : cfg' × ℕ) (l' : full_info_state)
    (Hneg : ¬ ∃ prel : full_info_state, prel <+: l ∧ is_frontier prel [] osch)
    (Hprefix : l' <+: l ++ [x]) (Hfrontier : is_frontier l' [] osch) : l' = l ++ [x] := by
  rcases List.prefix_concat_iff.1 Hprefix with h | h
  · exact h
  · exact absurd ⟨l', h, Hfrontier⟩ Hneg

/-- Rocq: `full_info_append_osch_exec_not_prefix`. -/
theorem full_info_append_osch_exec_not_prefix (l : full_info_state) (osch : full_info_oscheduler)
    (n : ℕ) (ρ : CPState) (f : full_info_state → full_info_oscheduler)
    (Hneg : ¬ ∃ prel, prel <+: l ∧ is_frontier prel [] osch) (x : full_info_state × CPState) :
    (osch_exec osch.fi_osch n (l, ρ) ≫= fun p =>
      if h : ∃ prel, prel <+: p.1 ∧ is_frontier prel [] osch then
        osch_lim_exec (full_info_lift_osch (Classical.choose h) (f (Classical.choose h))).fi_osch p
      else dzero) x ≤
      osch_lim_exec (full_info_append_osch osch f).fi_osch (l, ρ) x := by
  induction n generalizing l ρ with
  | zero =>
    cases h : osch.fi_osch (l, ρ) with
    | some μ => rw [osch_exec_0 _ _ ⟨μ, h⟩, dbind_dzero, dzero_0]; exact zero_le
    | none =>
      rw [osch_exec_is_none _ _ _ h, dret_id_left, dite_eq_right Hneg, dzero_0]; exact zero_le
  | succ n ih =>
    have happ : (full_info_append_osch osch f).fi_osch (l, ρ) = osch.fi_osch (l, ρ) :=
      full_info_append_osch_not_prefix osch f l ρ Hneg
    cases h : osch.fi_osch (l, ρ) with
    | none =>
      rw [osch_exec_is_none _ _ _ h, dret_id_left, dite_eq_right Hneg, dzero_0]; exact zero_le
    | some μ =>
      rw [osch_lim_exec_step]
      simp only [osch_exec, osch_step_or_none, osch_step, h, happ]
      rw [← dbind_assoc, ← dbind_assoc]
      refine dbind_pmf_le_strong _ _ _ x fun p hp => ?_
      have hv := osch.fi_osch_valid _ _ _ _ _ h hp
      rw [dmap, ← dbind_assoc, ← dbind_assoc]
      refine dbind_pmf_le_strong _ _ _ x fun σ' _ => ?_
      rw [dret_id_left]
      by_cases H' : ∃ prel, prel <+: p.1 ∧ is_frontier prel [] osch
      · obtain ⟨prel, Hprefix, Hfrontier⟩ := H'
        rw [hv] at Hprefix
        have hprel := append_one_frontier l osch _ prel Hneg Hprefix Hfrontier
        rw [← hv] at hprel
        subst hprel
        rw [osch_exec_is_none _ _ _ (is_frontier_None _ _ osch σ' Hfrontier), dret_id_left]
        have H'' : ∃ prel', prel' <+: p.1 ∧ is_frontier prel' [] osch :=
          ⟨p.1, List.prefix_refl _, Hfrontier⟩
        rw [dite_eq_left H'']
        have hc : Classical.choose H'' = p.1 :=
          is_frontier_prefix_lemma _ _ osch p.1 (Classical.choose_spec H'').1
            (Classical.choose_spec H'').2 (List.prefix_refl _) Hfrontier
        rw [hc]
        have := full_info_append_osch_lim_exec_prefix p.1 [] osch f σ' Hfrontier
        simp only [List.append_nil] at this
        rw [this]
      · exact ih p.1 σ' H'

/-- Rocq: `full_info_append_osch_lim_exec_not_prefix`. -/
theorem full_info_append_osch_lim_exec_not_prefix (l : full_info_state)
    (osch : full_info_oscheduler) (ρ : CPState) (f : full_info_state → full_info_oscheduler)
    (Hneg : ¬ ∃ prel, prel <+: l ∧ is_frontier prel [] osch) (x : full_info_state × CPState) :
    (osch_lim_exec osch.fi_osch (l, ρ) ≫= fun p =>
      if h : ∃ prel, prel <+: p.1 ∧ is_frontier prel [] osch then
        osch_lim_exec (full_info_lift_osch (Classical.choose h) (f (Classical.choose h))).fi_osch p
      else dzero) x ≤
      osch_lim_exec (full_info_append_osch osch f).fi_osch (l, ρ) x := by
  unfold osch_lim_exec
  rw [lim_distr_dbind_pmf]
  exact iSup_le fun n => full_info_append_osch_exec_not_prefix l osch n ρ f Hneg x

/-- Rocq: `full_info_append_osch_lim_exec`. -/
theorem full_info_append_osch_lim_exec (osch : full_info_oscheduler) (ρ : CPState)
    (f : full_info_state → full_info_oscheduler) (x : full_info_state × CPState) :
    (osch_lim_exec osch.fi_osch ([], ρ) ≫= fun p =>
      if h : ∃ prel, prel <+: p.1 ∧ is_frontier prel [] osch then
        osch_lim_exec (full_info_lift_osch (Classical.choose h) (f (Classical.choose h))).fi_osch p
      else dzero) x ≤
      osch_lim_exec (full_info_append_osch osch f).fi_osch ([], ρ) x := by
  by_cases H : ∃ prel, prel <+: [] ∧ is_frontier prel [] osch
  · obtain ⟨prel, Hprefix, Hfrontier⟩ := H
    obtain rfl := List.prefix_nil.1 Hprefix
    rw [osch_lim_exec_None _ _ (is_frontier_None _ _ osch ρ Hfrontier), dret_id_left]
    have H' : ∃ prel, prel <+: ([] : full_info_state) ∧ is_frontier prel [] osch :=
      ⟨[], Hprefix, Hfrontier⟩
    rw [dite_eq_left H']
    have hc : Classical.choose H' = [] := List.prefix_nil.1 (Classical.choose_spec H').1
    rw [hc]
    have := full_info_append_osch_lim_exec_prefix [] [] osch f ρ Hfrontier
    simp only [List.append_nil] at this
    rw [this]
  · exact full_info_append_osch_lim_exec_not_prefix [] osch ρ f H x

end full_info

end Foxtrot
