module

public import Metrology.ConProbLang.Common.ConLanguage

/-!
# Evaluation-context based concurrent probabilistic languages

Ported from clutch/theories/common/con_ectx_language.v

An axiomatization of evaluation-context based CONCURRENT languages, including a proof that this
gives rise to a `conLanguage` (`con_ectx_lang`).

Compared with the Rocq development:
* `Structure conEctxLanguage` is a bundled Lean `structure` (field names as in Rocq); the
  `EqDecision`/`Countable` fields are registered as instances. The fields `of_val`, `to_val`,
  `empty_ectx`, `comp_ectx`, `fill`, `decomp`, `head_step`, `state_step`, `get_active` take `Λ`
  *explicitly* (use dot notation `Λ.fill K e`, `Λ.head_step e σ`, ...), since the implicit-`Λ`
  names `ConProbLang.of_val`, `ConProbLang.to_val`, ... are already taken by `conLanguage`.
* All derived definitions and lemmas live in the namespace `ConProbLang.conEctxLanguage`
  (Rocq names otherwise unchanged: `head_reducible`, `prim_step`, `fill_lift`, `head_prim_step`,
  `fill_not_val`, ...). Inside that namespace these shadow the `conLanguage` names
  `prim_step`, `fill_lift`, `fill_lift'`, `fill_not_val`, `fill_inj`. They take `Λ` implicitly.
* `prim_step e1 σ1` is defined with projections `(Λ.decomp e1).1`/`.2` instead of
  `let '(K, e1') := decomp e1`; `prim_step_of_decomp` is the unfolding lemma to use.
* `con_ectx_lang Λ : conLanguage` (Rocq: `Canonical Structure con_ectx_lang`, with
  `Arguments con_ectx_lang : clear implicits`) is an `abbrev` in namespace `ConProbLang`, and
  `Coercion con_ectx_lang` is a `Coe` instance. Generic `conLanguage` notions applied to `Λ` are
  written with `(Λ := con_ectx_lang Λ)`, e.g. `reducible (Λ := con_ectx_lang Λ) e σ`.
  `ConLanguageOfEctx` (a canonical-structure trick in Rocq) is simply `con_ectx_lang`.
* `Class head_reducible` is a plain `def` (it is a Prop-valued definition, not used for
  instance search). `Inj (=) (=) (fill K)` is `Function.Injective (Λ.fill K)`; the Rocq
  instances `fill_inj`, `inj_fill`, `inj_fill'` are theorems.
* `ρ > 0` is `0 < ρ`; `SeriesC` is `∑'`; `is_Some x` is `∃ v, x = some v`.

Omitted: `Bind Scope`, `Arguments` declarations.
Added: `prim_step_of_decomp`, `fill_lift_apply`, `fill_lift'_apply` (unfolding lemmas), and the
rfl lemmas `con_ectx_lang_*` describing the fields of `con_ectx_lang Λ`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

section con_ectx_language_mixin

variable {expr val ectx state state_idx : Type} [Countable expr] [Countable state]

/-- Rocq: `ConEctxLanguageMixin`. -/
structure ConEctxLanguageMixin (of_val : val → expr) (to_val : expr → Option val)
    (empty_ectx : ectx) (comp_ectx : ectx → ectx → ectx) (fill : ectx → expr → expr)
    (decomp : expr → ectx × expr)
    (head_step : expr → state → Distr (expr × state × List expr))
    (state_step : state → state_idx → Distr state)
    (get_active : state → List state_idx) : Prop where
  mixin_to_of_val : ∀ v, to_val (of_val v) = some v
  mixin_of_to_val : ∀ e v, to_val e = some v → of_val v = e
  mixin_val_head_stuck : ∀ e1 σ1 ρ, 0 < head_step e1 σ1 ρ → to_val e1 = none
  mixin_state_step_head_not_stuck : ∀ e σ σ' α, 0 < state_step σ α σ' →
    ((∃ ρ, 0 < head_step e σ ρ) ↔ (∃ ρ', 0 < head_step e σ' ρ'))
  mixin_state_step_mass : ∀ σ α, α ∈ get_active σ → ∑' σ', state_step σ α σ' = 1
  mixin_head_step_mass : ∀ e σ, (∃ ρ, 0 < head_step e σ ρ) → ∑' ρ, head_step e σ ρ = 1
  mixin_fill_empty : ∀ e, fill empty_ectx e = e
  mixin_fill_comp : ∀ K1 K2 e, fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e
  mixin_fill_inj : ∀ K, Function.Injective (fill K)
  mixin_fill_val : ∀ K e, (∃ v, to_val (fill K e) = some v) → ∃ v, to_val e = some v
  /-- `decomp` decomposes an expression into an evaluation context and its head redex -/
  mixin_decomp_fill : ∀ K e e', decomp e = (K, e') → fill K e' = e
  mixin_decomp_val_empty : ∀ K e e', decomp e = (K, e') → (∃ v, to_val e' = some v) →
    K = empty_ectx
  mixin_decomp_fill_comp : ∀ e e' K K', to_val e = none → decomp e = (K', e') →
    decomp (fill K e) = (comp_ectx K K', e')
  /-- Given a head redex `e1_redex` somewhere in a term, and another decomposition of the same
  term into `fill K' e1'` such that `e1'` is not a value, then the head redex context is
  `e1'`'s context `K'` filled with another context `K''`. In particular, this implies
  `e1 = fill K'' e1_redex` by `fill_inj`, i.e., `e1'` contains the head redex.

  This implies there can be only one head redex, see `head_redex_unique`. -/
  mixin_step_by_val : ∀ K' K_redex e1' e1_redex σ1 ρ,
    fill K' e1' = fill K_redex e1_redex → to_val e1' = none →
    0 < head_step e1_redex σ1 ρ → ∃ K'', K_redex = comp_ectx K' K''
  /-- If `fill K e` takes a head step, then either `e` is a value or `K` is the empty
  evaluation context. In other words, if `e` is not a value wrapping it in a context does not
  add new head redex positions. -/
  mixin_head_ctx_step_val : ∀ K e σ1 ρ, 0 < head_step (fill K e) σ1 ρ →
    (∃ v, to_val e = some v) ∨ K = empty_ectx

end con_ectx_language_mixin

/-- Rocq: `conEctxLanguage`. -/
structure conEctxLanguage where
  expr : Type
  val : Type
  ectx : Type
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
  empty_ectx : ectx
  comp_ectx : ectx → ectx → ectx
  fill : ectx → expr → expr
  decomp : expr → ectx × expr
  head_step : expr → state → Distr (expr × state × List expr)
  state_step : state → state_idx → Distr state
  get_active : state → List state_idx
  con_ectx_language_mixin :
    ConEctxLanguageMixin of_val to_val empty_ectx comp_ectx fill decomp
      head_step state_step get_active

attribute [instance] conEctxLanguage.expr_eqdec conEctxLanguage.val_eqdec
  conEctxLanguage.state_eqdec conEctxLanguage.state_idx_eqdec conEctxLanguage.expr_countable
  conEctxLanguage.val_countable conEctxLanguage.state_countable
  conEctxLanguage.state_idx_countable

namespace conEctxLanguage

variable {Λ : conEctxLanguage}

/-! Only project stuff out of the mixin that is not also in language. -/

/-- Rocq: `val_head_stuck`. -/
theorem val_head_stuck (e1 : Λ.expr) (σ1 : Λ.state) (ρ : Λ.expr × Λ.state × List Λ.expr)
    (h : 0 < Λ.head_step e1 σ1 ρ) : Λ.to_val e1 = none :=
  Λ.con_ectx_language_mixin.mixin_val_head_stuck e1 σ1 ρ h

/-- Rocq: `state_step_head_not_stuck`. -/
theorem state_step_head_not_stuck (e : Λ.expr) (σ σ' : Λ.state) (α : Λ.state_idx)
    (h : 0 < Λ.state_step σ α σ') :
    (∃ ρ, 0 < Λ.head_step e σ ρ) ↔ (∃ ρ', 0 < Λ.head_step e σ' ρ') :=
  Λ.con_ectx_language_mixin.mixin_state_step_head_not_stuck e σ σ' α h

/-- Rocq: `head_step_mass`. -/
theorem head_step_mass (e : Λ.expr) (σ : Λ.state) (h : ∃ ρ, 0 < Λ.head_step e σ ρ) :
    ∑' ρ, Λ.head_step e σ ρ = 1 :=
  Λ.con_ectx_language_mixin.mixin_head_step_mass e σ h

/-- Rocq: `fill_empty`. -/
theorem fill_empty (e : Λ.expr) : Λ.fill Λ.empty_ectx e = e :=
  Λ.con_ectx_language_mixin.mixin_fill_empty e

/-- Rocq: `fill_comp`. -/
theorem fill_comp (K1 K2 : Λ.ectx) (e : Λ.expr) :
    Λ.fill K1 (Λ.fill K2 e) = Λ.fill (Λ.comp_ectx K1 K2) e :=
  Λ.con_ectx_language_mixin.mixin_fill_comp K1 K2 e

/-- Rocq: `fill_inj` (an `Inj` instance in Rocq). -/
theorem fill_inj (K : Λ.ectx) : Function.Injective (Λ.fill K) :=
  Λ.con_ectx_language_mixin.mixin_fill_inj K

/-- Rocq: `fill_val`. -/
theorem fill_val (K : Λ.ectx) (e : Λ.expr) (h : ∃ v, Λ.to_val (Λ.fill K e) = some v) :
    ∃ v, Λ.to_val e = some v :=
  Λ.con_ectx_language_mixin.mixin_fill_val K e h

/-- Rocq: `decomp_fill`. -/
theorem decomp_fill (K : Λ.ectx) (e e' : Λ.expr) (h : Λ.decomp e = (K, e')) :
    Λ.fill K e' = e :=
  Λ.con_ectx_language_mixin.mixin_decomp_fill K e e' h

/-- Rocq: `decomp_val_empty`. -/
theorem decomp_val_empty (K : Λ.ectx) (e e' : Λ.expr) (h : Λ.decomp e = (K, e'))
    (hv : ∃ v, Λ.to_val e' = some v) : K = Λ.empty_ectx :=
  Λ.con_ectx_language_mixin.mixin_decomp_val_empty K e e' h hv

/-- Rocq: `decomp_fill_comp`. -/
theorem decomp_fill_comp (K K' : Λ.ectx) (e e' : Λ.expr) (hv : Λ.to_val e = none)
    (h : Λ.decomp e = (K', e')) : Λ.decomp (Λ.fill K e) = (Λ.comp_ectx K K', e') :=
  Λ.con_ectx_language_mixin.mixin_decomp_fill_comp e e' K K' hv h

/-- Rocq: `step_by_val`. -/
theorem step_by_val (K' K_redex : Λ.ectx) (e1' e1_redex : Λ.expr) (σ1 : Λ.state)
    (ρ : Λ.expr × Λ.state × List Λ.expr)
    (hfill : Λ.fill K' e1' = Λ.fill K_redex e1_redex) (hv : Λ.to_val e1' = none)
    (hs : 0 < Λ.head_step e1_redex σ1 ρ) : ∃ K'', K_redex = Λ.comp_ectx K' K'' :=
  Λ.con_ectx_language_mixin.mixin_step_by_val K' K_redex e1' e1_redex σ1 ρ hfill hv hs

/-- Rocq: `head_ctx_step_val`. -/
theorem head_ctx_step_val (K : Λ.ectx) (e : Λ.expr) (σ1 : Λ.state)
    (ρ : Λ.expr × Λ.state × List Λ.expr) (h : 0 < Λ.head_step (Λ.fill K e) σ1 ρ) :
    (∃ v, Λ.to_val e = some v) ∨ K = Λ.empty_ectx :=
  Λ.con_ectx_language_mixin.mixin_head_ctx_step_val K e σ1 ρ h

/-- Rocq: `head_reducible` (a `Class` in Rocq). -/
def head_reducible (e : Λ.expr) (σ : Λ.state) : Prop := ∃ ρ, 0 < Λ.head_step e σ ρ

/-- Rocq: `head_irreducible`. -/
def head_irreducible (e : Λ.expr) (σ : Λ.state) : Prop := ∀ ρ, Λ.head_step e σ ρ = 0

/-- Rocq: `head_stuck`. -/
def head_stuck (e : Λ.expr) (σ : Λ.state) : Prop := Λ.to_val e = none ∧ head_irreducible e σ

/-- Rocq: `sub_redexes_are_values`. All non-value redexes are at the root. In other words, all
sub-redexes are values. -/
def sub_redexes_are_values (e : Λ.expr) : Prop :=
  ∀ K e', e = Λ.fill K e' → Λ.to_val e' = none → K = Λ.empty_ectx

/-- Rocq: `fill_lift`. -/
def fill_lift (K : Λ.ectx) : Λ.expr × Λ.state → Λ.expr × Λ.state :=
  fun ρ => (Λ.fill K ρ.1, ρ.2)

@[simp] theorem fill_lift_apply (K : Λ.ectx) (e : Λ.expr) (σ : Λ.state) :
    fill_lift K (e, σ) = (Λ.fill K e, σ) := rfl

/-- Rocq: `fill_lift_comp`. -/
theorem fill_lift_comp (K1 K2 : Λ.ectx) :
    fill_lift (Λ.comp_ectx K1 K2) = fill_lift K1 ∘ fill_lift K2 := by
  funext ρ
  simp [fill_lift, fill_comp]

/-- Rocq: `fill_lift_empty`. -/
theorem fill_lift_empty : fill_lift (Λ := Λ) Λ.empty_ectx = (fun ρ => ρ) := by
  funext ρ
  simp [fill_lift, fill_empty]

/-- Rocq: `inj_fill` (an `Inj` instance in Rocq). -/
theorem inj_fill (K : Λ.ectx) : Function.Injective (fill_lift K) := by
  rintro ⟨e, σ⟩ ⟨e', σ'⟩ h
  simp only [fill_lift_apply, Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  rw [fill_inj K h1]

/-- Rocq: `fill_lift'`. -/
def fill_lift' (K : Λ.ectx) :
    Λ.expr × Λ.state × List Λ.expr → Λ.expr × Λ.state × List Λ.expr :=
  fun ρ => (Λ.fill K ρ.1, ρ.2)

@[simp] theorem fill_lift'_apply (K : Λ.ectx) (e : Λ.expr) (σ : Λ.state)
    (efs : List Λ.expr) : fill_lift' K (e, σ, efs) = (Λ.fill K e, σ, efs) := rfl

/-- Rocq: `fill_lift_comp'`. -/
theorem fill_lift_comp' (K1 K2 : Λ.ectx) :
    fill_lift' (Λ.comp_ectx K1 K2) = fill_lift' K1 ∘ fill_lift' K2 := by
  funext ρ
  simp [fill_lift', fill_comp]

/-- Rocq: `fill_lift_empty'`. -/
theorem fill_lift_empty' : fill_lift' (Λ := Λ) Λ.empty_ectx = (fun ρ => ρ) := by
  funext ρ
  simp [fill_lift', fill_empty]

/-- Rocq: `inj_fill'` (an `Inj` instance in Rocq). -/
theorem inj_fill' (K : Λ.ectx) : Function.Injective (fill_lift' K) := by
  rintro ⟨e, ρ⟩ ⟨e', ρ'⟩ h
  simp only [fill_lift', Prod.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  rw [fill_inj K h1]

/-- Rocq: `prim_step`. -/
def prim_step (e1 : Λ.expr) (σ1 : Λ.state) : Distr (Λ.expr × Λ.state × List Λ.expr) :=
  dmap (fill_lift' (Λ.decomp e1).1) (Λ.head_step (Λ.decomp e1).2 σ1)

/-- Unfolding lemma for `prim_step` (Rocq: `destruct (decomp e1) eqn:Heq; rewrite /prim_step`). -/
theorem prim_step_of_decomp {e1 e1' : Λ.expr} {K : Λ.ectx} (σ1 : Λ.state)
    (h : Λ.decomp e1 = (K, e1')) :
    prim_step e1 σ1 = dmap (fill_lift' K) (Λ.head_step e1' σ1) := by
  rw [prim_step, h]

/-- Rocq: `fill_not_val`. -/
theorem fill_not_val (K : Λ.ectx) (e : Λ.expr) (h : Λ.to_val e = none) :
    Λ.to_val (Λ.fill K e) = none := by
  cases hK : Λ.to_val (Λ.fill K e) with
  | none => rfl
  | some v =>
    obtain ⟨v', hv'⟩ := fill_val K e ⟨v, hK⟩
    rw [h] at hv'
    cases hv'

/-- Rocq: `con_ectx_lang_mixin`. -/
theorem con_ectx_lang_mixin :
    ConLanguageMixin Λ.of_val Λ.to_val prim_step Λ.state_step Λ.get_active := by
  constructor
  · exact Λ.con_ectx_language_mixin.mixin_to_of_val
  · exact Λ.con_ectx_language_mixin.mixin_of_to_val
  · intro e1 σ1 ρ hs
    rcases hd : Λ.decomp e1 with ⟨K, e1'⟩
    rw [prim_step_of_decomp σ1 hd, dmap_pos] at hs
    obtain ⟨_, _, hs⟩ := hs
    rw [← decomp_fill _ _ _ hd]
    exact fill_not_val _ _ (val_head_stuck _ _ _ hs)
  · intro e1 σ1 σ1' α hs
    rcases hd : Λ.decomp e1 with ⟨K, e1'⟩
    simp only [prim_step_of_decomp _ hd, dmap_pos]
    constructor
    · rintro ⟨_, a, -, ha⟩
      obtain ⟨ρ', hρ'⟩ := (state_step_head_not_stuck e1' σ1 σ1' α hs).1 ⟨a, ha⟩
      exact ⟨fill_lift' K ρ', ρ', rfl, hρ'⟩
    · rintro ⟨_, a, -, ha⟩
      obtain ⟨ρ', hρ'⟩ := (state_step_head_not_stuck e1' σ1 σ1' α hs).2 ⟨a, ha⟩
      exact ⟨fill_lift' K ρ', ρ', rfl, hρ'⟩
  · exact Λ.con_ectx_language_mixin.mixin_state_step_mass
  · rintro e σ ⟨ρ, hs⟩
    rcases hd : Λ.decomp e with ⟨K, e1'⟩
    rw [prim_step_of_decomp σ hd, dmap_pos] at hs
    obtain ⟨a, -, ha⟩ := hs
    rw [prim_step_of_decomp σ hd, dmap_mass]
    exact head_step_mass _ _ ⟨a, ha⟩

end conEctxLanguage

/-- Rocq: `con_ectx_lang` (a `Canonical Structure`; `Arguments con_ectx_lang : clear
implicits`). -/
abbrev con_ectx_lang (Λ : conEctxLanguage) : conLanguage where
  expr := Λ.expr
  val := Λ.val
  state := Λ.state
  state_idx := Λ.state_idx
  expr_eqdec := inferInstance
  val_eqdec := inferInstance
  state_eqdec := inferInstance
  state_idx_eqdec := inferInstance
  expr_countable := inferInstance
  val_countable := inferInstance
  state_countable := inferInstance
  state_idx_countable := inferInstance
  of_val := Λ.of_val
  to_val := Λ.to_val
  prim_step := conEctxLanguage.prim_step
  state_step := Λ.state_step
  get_active := Λ.get_active
  con_language_mixin := conEctxLanguage.con_ectx_lang_mixin

attribute [coe] con_ectx_lang

/-- Rocq: `Coercion con_ectx_lang : conEctxLanguage >-> conLanguage`. -/
instance : Coe conEctxLanguage conLanguage := ⟨con_ectx_lang⟩

section con_ectx_lang_fields

variable (Λ : conEctxLanguage)

theorem con_ectx_lang_expr : (con_ectx_lang Λ).expr = Λ.expr := rfl
theorem con_ectx_lang_val : (con_ectx_lang Λ).val = Λ.val := rfl
theorem con_ectx_lang_state : (con_ectx_lang Λ).state = Λ.state := rfl
theorem con_ectx_lang_state_idx : (con_ectx_lang Λ).state_idx = Λ.state_idx := rfl
@[simp] theorem con_ectx_lang_of_val (v : Λ.val) :
    of_val (Λ := con_ectx_lang Λ) v = Λ.of_val v := rfl
@[simp] theorem con_ectx_lang_to_val (e : Λ.expr) :
    to_val (Λ := con_ectx_lang Λ) e = Λ.to_val e := rfl
@[simp] theorem con_ectx_lang_prim_step (e : Λ.expr) (σ : Λ.state) :
    prim_step (Λ := con_ectx_lang Λ) e σ = conEctxLanguage.prim_step e σ := rfl
@[simp] theorem con_ectx_lang_state_step (σ : Λ.state) (α : Λ.state_idx) :
    state_step (Λ := con_ectx_lang Λ) σ α = Λ.state_step σ α := rfl
@[simp] theorem con_ectx_lang_get_active (σ : Λ.state) :
    get_active (Λ := con_ectx_lang Λ) σ = Λ.get_active σ := rfl

end con_ectx_lang_fields

namespace conEctxLanguage

variable {Λ : conEctxLanguage}

/-- Rocq: `head_atomic`. -/
def head_atomic (a : atomicity) (e : Λ.expr) : Prop :=
  ∀ σ e' σ' efs, 0 < Λ.head_step e σ (e', σ', efs) →
    match a with
    | .WeaklyAtomic => irreducible (Λ := con_ectx_lang Λ) e' σ'
    | .StronglyAtomic => ∃ v, Λ.to_val e' = some v

/-! ## Some lemmas about this language -/

/-- Rocq: `not_head_reducible`. -/
theorem not_head_reducible (e : Λ.expr) (σ : Λ.state) :
    ¬ head_reducible e σ ↔ head_irreducible e σ := by
  unfold head_reducible head_irreducible
  simp only [not_exists, pos_iff_ne_zero, ne_eq, not_not]

/-- Rocq: `head_redex_unique`. The decomposition into head redex and context is unique.
In all sensible instances, `comp_ectx K' empty_ectx` will be the same as `K'`, so the
conclusion is `K = K' ∧ e = e'`, but we do not require a law to actually prove that so we
cannot use that fact here. -/
theorem head_redex_unique (K K' : Λ.ectx) (e e' : Λ.expr) (σ : Λ.state)
    (heq : Λ.fill K e = Λ.fill K' e') (hred : head_reducible e σ)
    (hred' : head_reducible e' σ) : K = Λ.comp_ectx K' Λ.empty_ectx ∧ e = e' := by
  obtain ⟨ρ, hρ⟩ := hred
  obtain ⟨ρ', hρ'⟩ := hred'
  obtain ⟨K'', rfl⟩ := step_by_val K' K e' e σ ρ heq.symm (val_head_stuck _ _ _ hρ') hρ
  rw [← fill_comp] at heq
  obtain rfl := fill_inj K' heq
  rcases head_ctx_step_val _ _ _ _ hρ' with ⟨v, hv⟩ | rfl
  · rw [val_head_stuck _ _ _ hρ] at hv
    cases hv
  · exact ⟨rfl, (fill_empty e).symm⟩

/-- Rocq: `fill_prim_step_dbind`. -/
theorem fill_prim_step_dbind (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state)
    (hv : Λ.to_val e1 = none) :
    prim_step (Λ.fill K e1) σ1 = dmap (fill_lift' K) (prim_step e1 σ1) := by
  rcases hd : Λ.decomp e1 with ⟨K1, e1'⟩
  rw [prim_step_of_decomp σ1 (decomp_fill_comp K K1 e1 e1' hv hd),
    prim_step_of_decomp σ1 hd, dmap_comp, fill_lift_comp']

/-- Rocq: `fill_prim_step`. -/
theorem fill_prim_step (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state) (e2 : Λ.expr) (σ2 : Λ.state)
    (efs : List Λ.expr) (hv : Λ.to_val e1 = none) :
    prim_step e1 σ1 (e2, σ2, efs) = prim_step (Λ.fill K e1) σ1 (Λ.fill K e2, σ2, efs) := by
  rw [fill_prim_step_dbind K e1 σ1 hv]
  exact (dmap_elem_eq _ (e2, σ2, efs) _ _ (inj_fill' K) rfl).symm

/-- Rocq: `head_prim_step_pmf_eq`. -/
theorem head_prim_step_pmf_eq (e1 : Λ.expr) (σ1 : Λ.state)
    (ρ : Λ.expr × Λ.state × List Λ.expr) (hred : head_reducible e1 σ1) :
    prim_step e1 σ1 ρ = Λ.head_step e1 σ1 ρ := by
  rcases hd : Λ.decomp e1 with ⟨K, e1'⟩
  have hf := decomp_fill _ _ _ hd
  obtain ⟨ρ', hs⟩ := hred
  rw [← hf] at hs
  have hK : K = Λ.empty_ectx := by
    rcases head_ctx_step_val _ _ _ _ hs with hv | hK
    · exact decomp_val_empty K e1 e1' hd hv
    · exact hK
  subst hK
  rw [fill_empty] at hf
  subst hf
  rw [prim_step_of_decomp σ1 hd, fill_lift_empty', dmap_id]

/-- Rocq: `head_prim_step_eq`. -/
theorem head_prim_step_eq (e1 : Λ.expr) (σ1 : Λ.state) (hred : head_reducible e1 σ1) :
    prim_step e1 σ1 = Λ.head_step e1 σ1 :=
  distr_ext fun ρ => head_prim_step_pmf_eq e1 σ1 ρ hred

/-- Rocq: `head_prim_step`. -/
theorem head_prim_step (e1 : Λ.expr) (σ1 : Λ.state) (ρ : Λ.expr × Λ.state × List Λ.expr)
    (h : 0 < Λ.head_step e1 σ1 ρ) : 0 < prim_step e1 σ1 ρ := by
  rw [head_prim_step_eq e1 σ1 ⟨ρ, h⟩]
  exact h

/-- Rocq: `prim_step_iff`. -/
theorem prim_step_iff (e1 e2 : Λ.expr) (σ1 σ2 : Λ.state) (efs : List Λ.expr) :
    0 < prim_step e1 σ1 (e2, σ2, efs) ↔
      ∃ K e1' e2', Λ.fill K e1' = e1 ∧ Λ.fill K e2' = e2 ∧
        0 < Λ.head_step e1' σ1 (e2', σ2, efs) := by
  constructor
  · intro hs
    rcases hd : Λ.decomp e1 with ⟨K, e1'⟩
    rw [prim_step_of_decomp σ1 hd, dmap_pos] at hs
    obtain ⟨⟨e2', σ2', efs'⟩, heq, hpos⟩ := hs
    simp only [fill_lift'_apply, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨K, e1', e2', decomp_fill _ _ _ hd, rfl, hpos⟩
  · rintro ⟨K, e1', e2', rfl, rfl, hs⟩
    rw [← fill_prim_step K e1' σ1 e2' σ2 efs (val_head_stuck _ _ _ hs)]
    exact head_prim_step _ _ _ hs

/-- Rocq: `head_step_not_stuck`. -/
theorem head_step_not_stuck (e : Λ.expr) (σ : Λ.state) (ρ : Λ.expr × Λ.state × List Λ.expr)
    (h : 0 < Λ.head_step e σ ρ) : not_stuck (Λ := con_ectx_lang Λ) e σ :=
  Or.inr ⟨ρ, head_prim_step e σ ρ h⟩

/-- Rocq: `fill_reducible`. -/
theorem fill_reducible (K : Λ.ectx) (e : Λ.expr) (σ : Λ.state)
    (h : reducible (Λ := con_ectx_lang Λ) e σ) :
    reducible (Λ := con_ectx_lang Λ) (Λ.fill K e) σ := by
  obtain ⟨⟨e2, σ2, efs⟩, hs⟩ := h
  obtain ⟨K', e1', e2', rfl, rfl, hh⟩ := (prim_step_iff _ _ _ _ _).1 hs
  exact ⟨(Λ.fill (Λ.comp_ectx K K') e2', σ2, efs),
    (prim_step_iff _ _ _ _ _).2 ⟨Λ.comp_ectx K K', e1', e2', (fill_comp _ _ _).symm, rfl, hh⟩⟩

/-- Rocq: `head_prim_reducible`. -/
theorem head_prim_reducible (e : Λ.expr) (σ : Λ.state) (h : head_reducible e σ) :
    reducible (Λ := con_ectx_lang Λ) e σ := by
  obtain ⟨ρ, hs⟩ := h
  exact ⟨ρ, head_prim_step e σ ρ hs⟩

/-- Rocq: `head_prim_fill_reducible`. -/
theorem head_prim_fill_reducible (e : Λ.expr) (K : Λ.ectx) (σ : Λ.state)
    (h : head_reducible e σ) : reducible (Λ := con_ectx_lang Λ) (Λ.fill K e) σ :=
  fill_reducible K e σ (head_prim_reducible e σ h)

/-- Rocq: `state_step_head_reducible`. -/
theorem state_step_head_reducible (e : Λ.expr) (σ σ' : Λ.state) (α : Λ.state_idx)
    (h : 0 < Λ.state_step σ α σ') : head_reducible e σ ↔ head_reducible e σ' :=
  state_step_head_not_stuck e σ σ' α h

/-- Rocq: `head_prim_irreducible`. -/
theorem head_prim_irreducible (e : Λ.expr) (σ : Λ.state)
    (h : irreducible (Λ := con_ectx_lang Λ) e σ) : head_irreducible e σ := by
  rw [← not_reducible, ← not_head_reducible] at *
  exact fun h' => h (head_prim_reducible e σ h')

/-- Rocq: `prim_head_reducible`. -/
theorem prim_head_reducible (e : Λ.expr) (σ : Λ.state)
    (h : reducible (Λ := con_ectx_lang Λ) e σ) (hsub : sub_redexes_are_values e) :
    head_reducible e σ := by
  obtain ⟨⟨e2, σ2, efs⟩, hs⟩ := h
  obtain ⟨K, e1', e2', rfl, rfl, hh⟩ := (prim_step_iff _ _ _ _ _).1 hs
  obtain rfl := hsub K e1' rfl (val_head_stuck _ _ _ hh)
  rw [fill_empty]
  exact ⟨_, hh⟩

/-- Rocq: `prim_head_irreducible`. -/
theorem prim_head_irreducible (e : Λ.expr) (σ : Λ.state) (h : head_irreducible e σ)
    (hsub : sub_redexes_are_values e) : irreducible (Λ := con_ectx_lang Λ) e σ := by
  rw [← not_reducible, ← not_head_reducible] at *
  exact fun h' => h (prim_head_reducible e σ h' hsub)

/-- Rocq: `head_stuck_stuck`. -/
theorem head_stuck_stuck (e : Λ.expr) (σ : Λ.state) (h : head_stuck e σ)
    (hsub : sub_redexes_are_values e) : stuck (Λ := con_ectx_lang Λ) e σ :=
  ⟨h.1, prim_head_irreducible e σ h.2 hsub⟩

/-- Rocq: `ectx_language_atomic`. -/
theorem ectx_language_atomic (a : atomicity) (e : Λ.expr) (hatomic : head_atomic a e)
    (hsub : sub_redexes_are_values e) : Atomic (Λ := con_ectx_lang Λ) a e := by
  constructor
  intro σ e' σ' efs hs
  obtain ⟨K, e1', e2', rfl, rfl, hh⟩ := (prim_step_iff _ _ _ _ _).1 hs
  obtain rfl := hsub K e1' rfl (val_head_stuck _ _ _ hh)
  rw [fill_empty] at hatomic ⊢
  have := hatomic σ e2' σ' efs hh
  cases a <;> exact this

/-- Rocq: `head_reducible_prim_step_ctx`. -/
theorem head_reducible_prim_step_ctx (K : Λ.ectx) (e1 : Λ.expr) (σ1 : Λ.state) (e2 : Λ.expr)
    (σ2 : Λ.state) (efs : List Λ.expr) (hred : head_reducible e1 σ1)
    (hs : 0 < prim_step (Λ.fill K e1) σ1 (e2, σ2, efs)) :
    ∃ e2', e2 = Λ.fill K e2' ∧ 0 < Λ.head_step e1 σ1 (e2', σ2, efs) := by
  obtain ⟨ρ'', hK⟩ := hred
  obtain ⟨K', e1', e2', hKe1, hKe2, hh⟩ := (prim_step_iff _ _ _ _ _).1 hs
  obtain ⟨K'', rfl⟩ := step_by_val K K' e1 e1' σ1 _ hKe1.symm (val_head_stuck _ _ _ hK) hh
  rw [← fill_comp] at hKe1
  obtain rfl := fill_inj K hKe1
  refine ⟨Λ.fill K'' e2', by rw [← hKe2, fill_comp], ?_⟩
  rcases head_ctx_step_val _ _ _ _ hK with ⟨v, hv⟩ | rfl
  · rw [val_head_stuck _ _ _ hh] at hv
    cases hv
  · rw [fill_empty, fill_empty]
    exact hh

/-- Rocq: `head_reducible_prim_step`. -/
theorem head_reducible_prim_step (e1 : Λ.expr) (σ1 : Λ.state)
    (ρ : Λ.expr × Λ.state × List Λ.expr) (hred : head_reducible e1 σ1)
    (hs : 0 < prim_step e1 σ1 ρ) : 0 < Λ.head_step e1 σ1 ρ := by
  obtain ⟨e2, σ2, efs⟩ := ρ
  rw [← fill_empty e1] at hs
  obtain ⟨e2', rfl, h⟩ := head_reducible_prim_step_ctx Λ.empty_ectx e1 σ1 e2 σ2 efs hred hs
  rwa [fill_empty]

/-- Rocq: `not_head_reducible_dzero`. -/
theorem not_head_reducible_dzero (e : Λ.expr) (σ : Λ.state) (h : head_irreducible e σ) :
    Λ.head_step e σ = dzero :=
  dzero_ext _ h

/-- Rocq: `con_ectx_lang_ctx`. Every evaluation context is a context. -/
instance con_ectx_lang_ctx (K : Λ.ectx) : ConLanguageCtx (Λ := con_ectx_lang Λ) (Λ.fill K) where
  fill_not_val := fill_not_val K
  fill_inj := fill_inj K
  fill_dmap := fill_prim_step_dbind K

/-- Rocq: `pure_head_step`. -/
structure pure_head_step (e1 e2 : Λ.expr) : Prop where
  pure_head_step_safe : ∀ σ1, head_reducible e1 σ1
  pure_head_step_det : ∀ σ1, Λ.head_step e1 σ1 (e2, σ1, []) = 1

/-- Rocq: `pure_head_step_pure_step`. -/
theorem pure_head_step_pure_step (e1 e2 : Λ.expr) (h : pure_head_step e1 e2) :
    pure_step (Λ := con_ectx_lang Λ) e1 e2 := by
  obtain ⟨hp1, hp2⟩ := h
  refine ⟨fun σ => head_prim_reducible e1 σ (hp1 σ), fun σ1 => ?_⟩
  change prim_step e1 σ1 (e2, σ1, []) = 1
  rw [head_prim_step_eq e1 σ1 (hp1 σ1)]
  exact hp2 σ1

/-- Rocq: `pure_exec_fill`. This is not an instance because HeapLang's `wp_pure` tactic already
takes care of handling the evaluation context. So the instance is redundant. If you are
defining your own language and your `wp_pure` works differently, you might want to specialize
this lemma to your language and register that as an instance. -/
theorem pure_exec_fill (K : Λ.ectx) (φ : Prop) (n : ℕ) (e1 e2 : Λ.expr)
    (h : PureExec (Λ := con_ectx_lang Λ) φ n e1 e2) :
    PureExec (Λ := con_ectx_lang Λ) φ n (Λ.fill K e1) (Λ.fill K e2) :=
  pure_exec_ctx (Λ := con_ectx_lang Λ) (Λ.fill K) φ n e1 e2 h

end conEctxLanguage

/-- Rocq: `ConLanguageOfEctx`. In Rocq this re-packages the fields to help canonical-structure
search; in Lean it is just `con_ectx_lang`. -/
abbrev ConLanguageOfEctx (Λ : conEctxLanguage) : conLanguage := con_ectx_lang Λ

end ConProbLang
