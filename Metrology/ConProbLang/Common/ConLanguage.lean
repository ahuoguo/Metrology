module

public import Metrology.Prob.MDP

/-!
# Concurrent probabilistic languages

Ported from clutch/theories/common/con_language.v

A `conLanguage` has expressions, values, states and state indices (tapes), a `Distr`-valued
primitive step `prim_step : expr → state → Distr (expr × state × List expr)` (the list collects
forked threads), a `Distr`-valued `state_step` (tape sampling) and the list of active state
indices `get_active`. Configurations `cfg Λ = List Λ.expr × Λ.state` form an `mdp`
(`con_lang_mdp`) whose actions are thread indices `ℕ`.

Compared with the Rocq development:
* `Structure conLanguage` is a bundled Lean `structure`; the `EqDecision`/`Countable` fields are
  `DecidableEq`/`Countable` instance fields (registered as instances). All carriers live in
  `Type`. The fields `of_val`, `to_val`, `prim_step`, `state_step`, `get_active` are exported
  into the `ConProbLang` namespace, taking `Λ` implicitly (as in Rocq).
* The Rocq triple `expr * state * list expr` (left-nested) is the Lean triple
  `expr × state × List expr` (right-nested); the anonymous-constructor notation `(e, σ, efs)`
  is the same.
* `ρ > 0` becomes `0 < ρ`; `SeriesC` becomes `∑'`; `is_Some x` becomes `∃ v, x = some v`.
* `Inj (=) (=) f` becomes `Function.Injective f`; `inj_fill_lift`, `inj_fill_lift'`,
  `of_val_inj` are theorems (not instances).
* `relations.nsteps` is ported as the inductive `ConProbLang.nsteps` (below), and `rtc` is
  Mathlib's `Relation.ReflTransGen`.
* `Class PureExec`: `φ`, `n` and `e2` are `outParam`s (Rocq: `Hint Mode PureExec + - - ! -`).
  `IntoVal e v` has `v` as an `outParam`.
* `Global Instance as_vals_of_val : TCForall AsVal (of_val <$> vs)` becomes the theorem
  `as_vals_of_val : ∀ e ∈ vs.map of_val, AsVal e`.
* `con_lang_mdp_step` uses `List.set` for `<[n := e]>` and `l[i]?` for `l !! i`.

Omitted: `Bind Scope`, `Arguments` declarations, the canonical OFEs `stateO`, `valO`, `exprO`,
`cfgO` (Lean uses discrete OFEs at use sites if needed).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

/-! ## `relations.nsteps` -/

/-- Rocq (stdpp): `relations.nsteps`. `nsteps R n x y`: `y` is reached from `x` in exactly `n`
`R`-steps. -/
inductive nsteps {α : Type*} (R : α → α → Prop) : ℕ → α → α → Prop where
  | nsteps_O (x : α) : nsteps R 0 x x
  | nsteps_l (n : ℕ) (x y z : α) : R x y → nsteps R n y z → nsteps R (n + 1) x z

/-- Rocq (stdpp): `nsteps_congruence`. -/
theorem nsteps_congruence {α β : Type*} {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → S (f x) (f y)) {n : ℕ} {x y : α} (h : nsteps R n x y) :
    nsteps S n (f x) (f y) := by
  induction h with
  | nsteps_O x => exact .nsteps_O _
  | nsteps_l n x y z hxy _ ih => exact .nsteps_l _ _ _ _ (hf _ _ hxy) ih

/-! ## The mixin -/

section con_language_mixin

variable {expr val state state_idx : Type} [Countable expr] [Countable state]

/-- Rocq: `ConLanguageMixin`. -/
structure ConLanguageMixin (of_val : val → expr) (to_val : expr → Option val)
    (prim_step : expr → state → Distr (expr × state × List expr))
    (state_step : state → state_idx → Distr state)
    (get_active : state → List state_idx) : Prop where
  mixin_to_of_val : ∀ v, to_val (of_val v) = some v
  mixin_of_to_val : ∀ e v, to_val e = some v → of_val v = e
  mixin_val_stuck : ∀ e σ ρ, 0 < prim_step e σ ρ → to_val e = none
  /-- `state_step` preserves reducibility -/
  mixin_state_step_not_stuck : ∀ e σ σ' α, 0 < state_step σ α σ' →
    ((∃ ρ, 0 < prim_step e σ ρ) ↔ (∃ ρ', 0 < prim_step e σ' ρ'))
  /-- The mass of active `state_step`s is 1 -/
  mixin_state_step_mass : ∀ σ α, α ∈ get_active σ → ∑' σ', state_step σ α σ' = 1
  /-- The mass of reducible `prim_step`s is 1 -/
  mixin_prim_step_mass : ∀ e σ, (∃ ρ, 0 < prim_step e σ ρ) → ∑' ρ, prim_step e σ ρ = 1

end con_language_mixin

/-- Rocq: `conLanguage`. -/
structure conLanguage where
  expr : Type
  val : Type
  state : Type
  state_idx : Type
  expr_eqdec : DecidableEq expr
  val_eqdec : DecidableEq val
  state_eqdec : DecidableEq state
  state_idx_eqdec : DecidableEq state_idx
  expr_countable : Countable expr
  val_countable : Countable val
  state_countable : Countable state
  state_idx_countable : Countable state_idx
  of_val : val → expr
  to_val : expr → Option val
  prim_step : expr → state → Distr (expr × state × List expr)
  state_step : state → state_idx → Distr state
  get_active : state → List state_idx
  con_language_mixin : ConLanguageMixin of_val to_val prim_step state_step get_active

attribute [instance] conLanguage.expr_eqdec conLanguage.val_eqdec conLanguage.state_eqdec
  conLanguage.state_idx_eqdec conLanguage.expr_countable conLanguage.val_countable
  conLanguage.state_countable conLanguage.state_idx_countable

/-! Projections with `Λ` implicit (Rocq: `Arguments of_val {_} _` etc.). -/

/-- Rocq: `of_val`. -/
abbrev of_val {Λ : conLanguage} : Λ.val → Λ.expr := Λ.of_val
/-- Rocq: `to_val`. -/
abbrev to_val {Λ : conLanguage} : Λ.expr → Option Λ.val := Λ.to_val
/-- Rocq: `prim_step`. -/
abbrev prim_step {Λ : conLanguage} : Λ.expr → Λ.state → Distr (Λ.expr × Λ.state × List Λ.expr) :=
  Λ.prim_step
/-- Rocq: `state_step`. -/
abbrev state_step {Λ : conLanguage} : Λ.state → Λ.state_idx → Distr Λ.state := Λ.state_step
/-- Rocq: `get_active`. -/
abbrev get_active {Λ : conLanguage} : Λ.state → List Λ.state_idx := Λ.get_active

/-- Rocq: `cfg`. -/
abbrev cfg (Λ : conLanguage) := List Λ.expr × Λ.state

/-- Rocq: `partial_cfg`. -/
abbrev partial_cfg (Λ : conLanguage) := Λ.expr × Λ.state

/-- Rocq: `fill_lift`. -/
def fill_lift {Λ : conLanguage} (K : Λ.expr → Λ.expr) : partial_cfg Λ → partial_cfg Λ :=
  fun ρ => (K ρ.1, ρ.2)

@[simp] theorem fill_lift_apply {Λ : conLanguage} (K : Λ.expr → Λ.expr) (e : Λ.expr)
    (σ : Λ.state) : fill_lift K (e, σ) = (K e, σ) := rfl

/-- Rocq: `inj_fill_lift`. -/
theorem inj_fill_lift {Λ : conLanguage} (K : Λ.expr → Λ.expr) (hK : Function.Injective K) :
    Function.Injective (fill_lift K) := by
  rintro ⟨e, σ⟩ ⟨e', σ'⟩ h
  simp only [fill_lift_apply, Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  rw [hK h1]

/-- Rocq: `fill_lift'`. -/
def fill_lift' {Λ : conLanguage} (K : Λ.expr → Λ.expr) :
    Λ.expr × Λ.state × List Λ.expr → Λ.expr × Λ.state × List Λ.expr :=
  fun ρ => (K ρ.1, ρ.2)

@[simp] theorem fill_lift'_apply {Λ : conLanguage} (K : Λ.expr → Λ.expr) (e : Λ.expr)
    (σ : Λ.state) (efs : List Λ.expr) : fill_lift' K (e, σ, efs) = (K e, σ, efs) := rfl

/-- Rocq: `inj_fill_lift'`. -/
theorem inj_fill_lift' {Λ : conLanguage} (K : Λ.expr → Λ.expr) (hK : Function.Injective K) :
    Function.Injective (fill_lift' K) := by
  rintro ⟨e, ρ⟩ ⟨e', ρ'⟩ h
  simp only [fill_lift', Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  rw [hK h1]

/-- Rocq: `ConLanguageCtx`. -/
class ConLanguageCtx {Λ : conLanguage} (K : Λ.expr → Λ.expr) : Prop where
  fill_not_val : ∀ e, to_val e = none → to_val (K e) = none
  fill_inj : Function.Injective K
  fill_dmap : ∀ e1 σ1, to_val e1 = none →
    prim_step (K e1) σ1 = dmap (fill_lift' K) (prim_step e1 σ1)

export ConLanguageCtx (fill_not_val fill_inj fill_dmap)

/-- Rocq: `atomicity`. -/
inductive atomicity where
  | StronglyAtomic
  | WeaklyAtomic
deriving DecidableEq, Inhabited, Repr

export atomicity (StronglyAtomic WeaklyAtomic)

section con_language

variable {Λ : conLanguage}

/-- Rocq: `to_of_val`. -/
@[simp] theorem to_of_val (v : Λ.val) : to_val (of_val v) = some v :=
  Λ.con_language_mixin.mixin_to_of_val v

/-- Rocq: `of_to_val`. -/
theorem of_to_val (e : Λ.expr) (v : Λ.val) (h : to_val e = some v) : of_val v = e :=
  Λ.con_language_mixin.mixin_of_to_val e v h

/-- Rocq: `val_stuck`. -/
theorem val_stuck (e : Λ.expr) (σ : Λ.state) (ρ : Λ.expr × Λ.state × List Λ.expr)
    (h : 0 < prim_step e σ ρ) : to_val e = none :=
  Λ.con_language_mixin.mixin_val_stuck e σ ρ h

/-- Rocq: `state_step_not_stuck`. -/
theorem state_step_not_stuck (e : Λ.expr) (σ σ' : Λ.state) (α : Λ.state_idx)
    (h : 0 < state_step σ α σ') :
    (∃ ρ, 0 < prim_step e σ ρ) ↔ (∃ ρ', 0 < prim_step e σ' ρ') :=
  Λ.con_language_mixin.mixin_state_step_not_stuck e σ σ' α h

/-- Rocq: `state_step_mass`. -/
theorem state_step_mass (σ : Λ.state) (α : Λ.state_idx) (h : α ∈ get_active σ) :
    ∑' σ', state_step σ α σ' = 1 :=
  Λ.con_language_mixin.mixin_state_step_mass σ α h

/-- Rocq: `prim_step_mass`. -/
theorem prim_step_mass (e : Λ.expr) (σ : Λ.state) (h : ∃ ρ, 0 < prim_step e σ ρ) :
    ∑' ρ, prim_step e σ ρ = 1 :=
  Λ.con_language_mixin.mixin_prim_step_mass e σ h

/-- Rocq: `reducible`. -/
def reducible (e : Λ.expr) (σ : Λ.state) : Prop := ∃ ρ, 0 < prim_step e σ ρ

/-- Rocq: `irreducible`. -/
def irreducible (e : Λ.expr) (σ : Λ.state) : Prop := ∀ ρ, prim_step e σ ρ = 0

/-- Rocq: `stuck`. -/
def stuck (e : Λ.expr) (σ : Λ.state) : Prop := to_val e = none ∧ irreducible e σ

/-- Rocq: `not_stuck`. -/
def not_stuck (e : Λ.expr) (σ : Λ.state) : Prop := (∃ v, to_val e = some v) ∨ reducible e σ

/-- Rocq: `not_reducible`. -/
theorem not_reducible (e : Λ.expr) (σ : Λ.state) : ¬ reducible e σ ↔ irreducible e σ := by
  unfold reducible irreducible
  simp only [not_exists, pos_iff_ne_zero, ne_eq, not_not]

/-- Rocq: `not_not_stuck`. -/
theorem not_not_stuck (e : Λ.expr) (σ : Λ.state) : ¬ not_stuck e σ ↔ stuck e σ := by
  unfold stuck not_stuck
  rw [← not_reducible]
  cases h : to_val e <;> simp

/-- Rocq: `Atomic`. -/
class Atomic (a : atomicity) (e : Λ.expr) : Prop where
  atomic : ∀ σ e' σ' efs, 0 < prim_step e σ (e', σ', efs) →
    match a with
    | .WeaklyAtomic => irreducible e' σ'
    | .StronglyAtomic => ∃ v, to_val e' = some v

/-- Rocq: `of_to_val_flip`. -/
theorem of_to_val_flip (v : Λ.val) (e : Λ.expr) (h : of_val v = e) : to_val e = some v := by
  subst h; exact to_of_val v

/-- Rocq: `of_val_inj`. -/
theorem of_val_inj : Function.Injective (of_val (Λ := Λ)) := by
  intro v v' h
  have := congrArg to_val h
  simpa using this

/-- Rocq: `strongly_atomic_atomic`. -/
theorem strongly_atomic_atomic (e : Λ.expr) (a : atomicity) [H : Atomic .StronglyAtomic e] :
    Atomic a e := by
  cases a with
  | StronglyAtomic => exact H
  | WeaklyAtomic =>
    constructor
    intro σ e' σ' efs h' ρ
    obtain ⟨v, hv⟩ := H.atomic σ e' σ' efs h'
    by_contra hne
    have := val_stuck e' σ' ρ (pos_iff_ne_zero.2 hne)
    rw [hv] at this
    cases this

variable {K : Λ.expr → Λ.expr}

/-- Rocq: `fill_step`. -/
theorem fill_step (e1 : Λ.expr) (σ1 : Λ.state) (e2 : Λ.expr) (σ2 : Λ.state)
    (efs : List Λ.expr) [ConLanguageCtx K] (hs : 0 < prim_step e1 σ1 (e2, σ2, efs)) :
    0 < prim_step (K e1) σ1 (K e2, σ2, efs) := by
  rw [fill_dmap e1 σ1 (val_stuck _ _ _ hs), dmap_pos]
  exact ⟨(e2, σ2, efs), rfl, hs⟩

/-- Rocq: `fill_step_inv`. -/
theorem fill_step_inv (e1' : Λ.expr) (σ1 : Λ.state) (e2 : Λ.expr) (σ2 : Λ.state)
    (efs : List Λ.expr) [ConLanguageCtx K] (hv : to_val e1' = none)
    (hs : 0 < prim_step (K e1') σ1 (e2, σ2, efs)) :
    ∃ e2', e2 = K e2' ∧ 0 < prim_step e1' σ1 (e2', σ2, efs) := by
  rw [fill_dmap e1' σ1 hv, dmap_pos] at hs
  obtain ⟨⟨e, σ, efs'⟩, heq, hpos⟩ := hs
  simp only [fill_lift'_apply, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨e, rfl, hpos⟩

/-- Rocq: `fill_step_prob`. -/
theorem fill_step_prob (e1 : Λ.expr) (σ1 : Λ.state) (e2 : Λ.expr) (σ2 : Λ.state)
    (efs : List Λ.expr) [ConLanguageCtx K] (hv : to_val e1 = none) :
    prim_step e1 σ1 (e2, σ2, efs) = prim_step (K e1) σ1 (K e2, σ2, efs) := by
  rw [fill_dmap e1 σ1 hv]
  exact (dmap_elem_eq _ (e2, σ2, efs) _ _ (inj_fill_lift' K fill_inj) rfl).symm

/-- Rocq: `reducible_fill`. -/
theorem reducible_fill [ConLanguageCtx K] (e : Λ.expr) (σ : Λ.state) (h : reducible e σ) :
    reducible (K e) σ := by
  obtain ⟨⟨e2, σ2, efs⟩, hs⟩ := h
  exact ⟨_, fill_step e σ e2 σ2 efs hs⟩

/-- Rocq: `reducible_fill_inv`. -/
theorem reducible_fill_inv [ConLanguageCtx K] (e : Λ.expr) (σ : Λ.state)
    (hv : to_val e = none) (h : reducible (K e) σ) : reducible e σ := by
  obtain ⟨⟨e2, σ2, efs⟩, hs⟩ := h
  obtain ⟨e2', -, hs'⟩ := fill_step_inv e σ e2 σ2 efs hv hs
  exact ⟨_, hs'⟩

/-- Rocq: `state_step_reducible`. -/
theorem state_step_reducible (e : Λ.expr) (σ σ' : Λ.state) (α : Λ.state_idx)
    (h : 0 < state_step σ α σ') : reducible e σ ↔ reducible e σ' :=
  state_step_not_stuck e σ σ' α h

/-- Rocq: `state_step_iterM_reducible`. -/
theorem state_step_iterM_reducible (e : Λ.expr) (σ σ' : Λ.state) (α : Λ.state_idx) (n : ℕ)
    (h : 0 < iterM n (fun σ => state_step σ α) σ σ') : reducible e σ ↔ reducible e σ' := by
  induction n generalizing σ σ' with
  | zero =>
    rw [iterM_O] at h
    rw [dret_pos _ _ h]
  | succ n ih =>
    rw [iterM_Sn, dbind_pos] at h
    obtain ⟨σ'', h1, h2⟩ := h
    exact (state_step_reducible e σ σ'' α h2).trans (ih σ'' σ' h1)

/-- Rocq: `irreducible_fill`. -/
theorem irreducible_fill [ConLanguageCtx K] (e : Λ.expr) (σ : Λ.state)
    (hv : to_val e = none) (h : irreducible e σ) : irreducible (K e) σ := by
  rw [← not_reducible] at h ⊢
  exact fun h' => h (reducible_fill_inv e σ hv h')

/-- Rocq: `irreducible_fill_inv`. -/
theorem irreducible_fill_inv [ConLanguageCtx K] (e : Λ.expr) (σ : Λ.state)
    (h : irreducible (K e) σ) : irreducible e σ := by
  rw [← not_reducible] at h ⊢
  exact fun h' => h (reducible_fill e σ h')

/-- Rocq: `not_stuck_fill_inv`. -/
theorem not_stuck_fill_inv (K : Λ.expr → Λ.expr) [ConLanguageCtx K] (e : Λ.expr) (σ : Λ.state)
    (h : not_stuck (K e) σ) : not_stuck e σ := by
  unfold not_stuck at h ⊢
  cases hv : to_val e with
  | some v => exact Or.inl ⟨v, rfl⟩
  | none =>
    right
    rcases h with ⟨v, hK⟩ | h
    · rw [fill_not_val e hv] at hK; cases hK
    · exact reducible_fill_inv e σ hv h

/-- Rocq: `stuck_fill`. -/
theorem stuck_fill [ConLanguageCtx K] (e : Λ.expr) (σ : Λ.state) (h : stuck e σ) :
    stuck (K e) σ := by
  rw [← not_not_stuck] at h ⊢
  exact fun h' => h (not_stuck_fill_inv K e σ h')

/-- Rocq: `pure_step`. -/
structure pure_step (e1 e2 : Λ.expr) : Prop where
  pure_step_safe : ∀ σ1, reducible e1 σ1
  pure_step_det : ∀ σ, prim_step e1 σ (e2, σ, []) = 1

/-- Rocq: `PureExec`. -/
class PureExec (φ : outParam Prop) (n : outParam ℕ) (e1 : Λ.expr) (e2 : outParam Λ.expr) :
    Prop where
  pure_exec : φ → nsteps pure_step n e1 e2

export PureExec (pure_exec)

/-- Rocq: `pure_step_ctx`. -/
theorem pure_step_ctx (K : Λ.expr → Λ.expr) [ConLanguageCtx K] (e1 e2 : Λ.expr)
    (h : pure_step e1 e2) : pure_step (K e1) (K e2) := by
  obtain ⟨hred, hstep⟩ := h
  refine ⟨fun σ1 => reducible_fill e1 σ1 (hred σ1), fun σ => ?_⟩
  have hv : to_val e1 = none := val_stuck e1 σ (e2, σ, []) (by rw [hstep σ]; exact one_pos)
  rw [← fill_step_prob e1 σ e2 σ [] hv]
  exact hstep σ

/-- Rocq: `pure_step_nsteps_ctx`. -/
theorem pure_step_nsteps_ctx (K : Λ.expr → Λ.expr) [ConLanguageCtx K] (n : ℕ) (e1 e2 : Λ.expr)
    (h : nsteps pure_step n e1 e2) : nsteps pure_step n (K e1) (K e2) :=
  nsteps_congruence K (pure_step_ctx K) h

/-- Rocq: `rtc_pure_step_ctx`. -/
theorem rtc_pure_step_ctx (K : Λ.expr → Λ.expr) [ConLanguageCtx K] (e1 e2 : Λ.expr)
    (h : Relation.ReflTransGen pure_step e1 e2) :
    Relation.ReflTransGen pure_step (K e1) (K e2) :=
  Relation.ReflTransGen.lift K (pure_step_ctx K) _ _ h

/-- Rocq: `pure_exec_ctx`. Not an instance, because it is awfully general. -/
theorem pure_exec_ctx (K : Λ.expr → Λ.expr) [ConLanguageCtx K] (φ : Prop) (n : ℕ)
    (e1 e2 : Λ.expr) (h : PureExec φ n e1 e2) : PureExec φ n (K e1) (K e2) :=
  ⟨fun hφ => pure_step_nsteps_ctx K n e1 e2 (h.pure_exec hφ)⟩

/-- Rocq: `PureExec_reducible`. -/
theorem PureExec_reducible (σ1 : Λ.state) (φ : Prop) (n : ℕ) (e1 e2 : Λ.expr) (hφ : φ)
    (h : PureExec φ (n + 1) e1 e2) : reducible e1 σ1 := by
  cases h.pure_exec hφ with
  | nsteps_l _ _ y _ hxy _ => exact hxy.pure_step_safe σ1

/-- Rocq: `PureExec_not_val`. -/
theorem PureExec_not_val [Inhabited Λ.state] (φ : Prop) (n : ℕ) (e1 e2 : Λ.expr) (hφ : φ)
    (h : PureExec φ (n + 1) e1 e2) : to_val e1 = none := by
  obtain ⟨ρ, hρ⟩ := PureExec_reducible default φ n e1 e2 hφ h
  exact val_stuck _ _ _ hρ

/-- Rocq: `IntoVal`. This is a family of frequent assumptions for `PureExec`. -/
class IntoVal (e : Λ.expr) (v : outParam Λ.val) : Prop where
  into_val : of_val v = e

export IntoVal (into_val)

/-- Rocq: `AsVal`. There is no instance `IntoVal → AsVal`, as often one can solve `AsVal`
more efficiently since no witness has to be computed. -/
class AsVal (e : Λ.expr) : Prop where
  as_val : ∃ v, of_val v = e

export AsVal (as_val)

instance (v : Λ.val) : AsVal (of_val v) := ⟨⟨v, rfl⟩⟩

/-- Rocq: `as_vals_of_val` (Rocq: a `TCForall AsVal (of_val <$> vs)` instance). -/
theorem as_vals_of_val (vs : List Λ.val) : ∀ e ∈ vs.map of_val, AsVal e := by
  intro e he
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 he
  exact ⟨⟨v, rfl⟩⟩

/-- Rocq: `as_val_is_Some`. -/
theorem as_val_is_Some (e : Λ.expr) (h : ∃ v, of_val v = e) : ∃ v, to_val e = some v := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨v, to_of_val v⟩

/-- Rocq: `fill_is_val`. -/
theorem fill_is_val (e : Λ.expr) (K : Λ.expr → Λ.expr) [ConLanguageCtx K]
    (h : ∃ v, to_val (K e) = some v) : ∃ v, to_val e = some v := by
  cases hv : to_val e with
  | some v => exact ⟨v, rfl⟩
  | none =>
    obtain ⟨v, hK⟩ := h
    rw [fill_not_val e hv] at hK
    cases hK

/-- Rocq: `rtc_pure_step_val`. -/
theorem rtc_pure_step_val [Inhabited Λ.state] (v : Λ.val) (e : Λ.expr)
    (h : Relation.ReflTransGen pure_step (of_val v) e) : to_val e = some v := by
  cases h.cases_head with
  | inl h => rw [← h]; exact to_of_val v
  | inr h =>
    obtain ⟨e', hstep, -⟩ := h
    obtain ⟨ρ, hρ⟩ := hstep.pure_step_safe default
    have := val_stuck _ _ _ hρ
    rw [to_of_val] at this
    cases this

end con_language

/-! ## `con_language` is an MDP -/

/-- Rocq: `con_lang_mdp_step`. The action `n` is the index of the thread to step. -/
def con_lang_mdp_step (Λ : conLanguage) (n : ℕ) (ρ : cfg Λ) : Distr (cfg Λ) :=
  match ρ.1[0]? >>= to_val with
  | some _ => dzero
  | none =>
    match ρ.1[n]? with
    | none => -- thread id exceeds the number of threads, so we stutter
      dret ρ
    | some e =>
      match to_val e with
      | some _ => -- `e` is a value, so we stutter
        dret ρ
      | none => dmap (fun p => (ρ.1.set n p.1 ++ p.2.2, p.2.1)) (prim_step e ρ.2)

/-- Rocq: `con_lang_mdp_to_final`. -/
def con_lang_mdp_to_final (Λ : conLanguage) (ρ : cfg Λ) : Option Λ.val :=
  match ρ.1[0]? with
  | some e => to_val e
  | none => none

/-- Rocq: `con_lang_mdp_mixin`. -/
theorem con_lang_mdp_mixin (Λ : conLanguage) :
    MdpMixin (con_lang_mdp_step Λ) (con_lang_mdp_to_final Λ) := by
  constructor
  rintro ⟨es, σ⟩ ⟨b, hb⟩ n a'
  unfold con_lang_mdp_to_final at hb
  unfold con_lang_mdp_step
  cases h0 : es[0]? with
  | none => rw [h0] at hb; cases hb
  | some e =>
    rw [h0] at hb
    simp only [Option.bind_eq_bind, Option.bind_some, hb, dzero_0]

/-- Rocq: `con_lang_mdp`. -/
def con_lang_mdp (Λ : conLanguage) : mdp where
  mdpstate := cfg Λ
  mdpstate_ret := Λ.val
  mdpaction := ℕ
  mdpstate_eqdec := inferInstance
  mdpstate_count := inferInstance
  mdpstate_ret_eqdec := inferInstance
  mdpstate_ret_count := inferInstance
  mdpaction_eqdec := inferInstance
  mdpaction_count := inferInstance
  step := con_lang_mdp_step Λ
  to_final := con_lang_mdp_to_final Λ
  mdp_mixin := con_lang_mdp_mixin Λ

@[simp] theorem con_lang_mdp_mdpstate (Λ : conLanguage) : (con_lang_mdp Λ).mdpstate = cfg Λ := rfl
@[simp] theorem con_lang_mdp_mdpstate_ret (Λ : conLanguage) :
    (con_lang_mdp Λ).mdpstate_ret = Λ.val := rfl
@[simp] theorem con_lang_mdp_mdpaction (Λ : conLanguage) : (con_lang_mdp Λ).mdpaction = ℕ := rfl
theorem con_lang_mdp_step_eq (Λ : conLanguage) :
    (con_lang_mdp Λ).step = con_lang_mdp_step Λ := rfl
theorem con_lang_mdp_to_final_eq (Λ : conLanguage) :
    (con_lang_mdp Λ).to_final = con_lang_mdp_to_final Λ := rfl

end ConProbLang
