module

public import Metrology.ConProbLang.Common.ConEctxLanguage

/-!
# Evaluation-context-item based concurrent probabilistic languages

Ported from clutch/theories/common/con_ectxi_language.v

An axiomatization of CONCURRENT languages based on evaluation context items, including a proof
that these are instances of general ectx-based CONCURRENT languages (`con_ectxi_lang_ectx`),
and hence of `conLanguage` (`con_ectxi_lang`).

Compared with the Rocq development:
* `Structure conEctxiLanguage` is a bundled Lean `structure`; its fields (`of_val`, `to_val`,
  `fill_item`, `decomp_item`, `expr_ord`, `head_step`, `state_step`, `get_active`) take `Λ`
  explicitly (dot notation `Λ.fill_item Ki e`). Derived definitions and lemmas live in the
  namespace `ConProbLang.conEctxiLanguage` and take `Λ` implicitly.
* `well_founded expr_ord` is `WellFounded expr_ord`; `decomp` (a `Program Fixpoint ... {wf}`
  in Rocq) is defined with `WellFounded.fix`, and `decomp_unfold` is proved from
  `WellFounded.fix_eq`. `decomp_unfold` uses `match decomp e' with | (K, e'') => ...` for Rocq's
  `let '(K, e'') := decomp e' in ...`.
* `fill K e := K.foldl (flip Λ.fill_item) e` (Rocq: `foldl (flip fill_item) e K`).
* The ectx `comp_ectx` is `flip (· ++ ·)` and `empty_ectx` is `[]`.
* `con_ectxi_lang_ectx Λ : conEctxLanguage` and `con_ectxi_lang Λ : conLanguage` (Rocq:
  canonical structures with `Arguments ... : clear implicits`) are `abbrev`s in namespace
  `ConProbLang`, with `Coe` instances for the Rocq `Coercion`s. `ConEctxLanguageOfEctxi` is
  `con_ectxi_lang_ectx`.
* The Rocq section proves `fill_val`/`fill_not_val` for `fill` inside
  `con_ectxi_lang_ectx_mixin` (as `assert`s) and later re-derives `fill_not_val`; here
  `fill_val` and `fill_not_val` are top-level lemmas stated before the mixin, and the later
  `fill_not_val` is that same lemma.
* `list_snoc_singleton_inv` is kept (proved via `List.append_inj'`).
* `Inj (=) (=) (fill_item Ki)` is `Function.Injective (Λ.fill_item Ki)`; the Rocq instance
  `fill_item_inj` is a theorem.

Omitted: `Bind Scope`, `Arguments` declarations.
Added: the instance `con_ectxi_lang_ctx` (`ConLanguageCtx (fill K)`), `fill_nil`, `fill_cons`, `fill_singleton` (simp, rfl) and `decomp_some`/`decomp_none`
helper equations, and rfl lemmas `con_ectxi_lang_ectx_*` for the fields.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

section con_ectxi_language_mixin

variable {expr val ectx_item state state_idx : Type} [Countable expr] [Countable state]

/-- Rocq: `ConEctxiLanguageMixin`. -/
structure ConEctxiLanguageMixin (of_val : val → expr) (to_val : expr → Option val)
    (fill_item : ectx_item → expr → expr) (decomp_item : expr → Option (ectx_item × expr))
    (expr_ord : expr → expr → Prop)
    (head_step : expr → state → Distr (expr × state × List expr))
    (state_step : state → state_idx → Distr state)
    (get_active : state → List state_idx) : Prop where
  mixin_to_of_val : ∀ v, to_val (of_val v) = some v
  mixin_of_to_val : ∀ e v, to_val e = some v → of_val v = e
  mixin_val_stuck : ∀ e1 σ1 ρ, 0 < head_step e1 σ1 ρ → to_val e1 = none
  mixin_state_step_head_not_stuck : ∀ e σ σ' α, 0 < state_step σ α σ' →
    ((∃ ρ, 0 < head_step e σ ρ) ↔ (∃ ρ', 0 < head_step e σ' ρ'))
  mixin_state_step_mass : ∀ σ α, α ∈ get_active σ → ∑' σ', state_step σ α σ' = 1
  mixin_head_step_mass : ∀ e σ, (∃ ρ, 0 < head_step e σ ρ) → ∑' ρ, head_step e σ ρ = 1
  mixin_fill_item_val : ∀ Ki e, (∃ v, to_val (fill_item Ki e) = some v) →
    ∃ v, to_val e = some v
  /-- `fill_item` is always injective on the expression for a fixed context. -/
  mixin_fill_item_inj : ∀ Ki, Function.Injective (fill_item Ki)
  /-- `fill_item` with (potentially different) non-value expressions is injective on the
  context. -/
  mixin_fill_item_no_val_inj : ∀ Ki1 Ki2 e1 e2, to_val e1 = none → to_val e2 = none →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2
  /-- a well-founded order on expressions -/
  mixin_expr_ord_wf : WellFounded expr_ord
  /-- `decomp_item` produces "smaller" expressions (typically it will be structurally
  decreasing) -/
  mixin_decomp_ord : ∀ Ki e e', decomp_item e = some (Ki, e') → expr_ord e' e
  mixin_decomp_fill_item : ∀ Ki e, to_val e = none →
    decomp_item (fill_item Ki e) = some (Ki, e)
  mixin_decomp_fill_item_2 : ∀ e e' Ki, decomp_item e = some (Ki, e') →
    fill_item Ki e' = e ∧ to_val e' = none
  /-- If `fill_item Ki e` takes a head step, then `e` is a value (unlike for `ectx_language`,
  an empty context is impossible here). In other words, if `e` is not a value then wrapping it
  in a context does not add new head redex positions. -/
  mixin_head_ctx_step_val : ∀ Ki e σ1 ρ, 0 < head_step (fill_item Ki e) σ1 ρ →
    ∃ v, to_val e = some v

end con_ectxi_language_mixin

/-- Rocq: `conEctxiLanguage`. -/
structure conEctxiLanguage where
  expr : Type
  val : Type
  ectx_item : Type
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
  fill_item : ectx_item → expr → expr
  decomp_item : expr → Option (ectx_item × expr)
  expr_ord : expr → expr → Prop
  head_step : expr → state → Distr (expr × state × List expr)
  state_step : state → state_idx → Distr state
  get_active : state → List state_idx
  con_ectxi_language_mixin :
    ConEctxiLanguageMixin of_val to_val fill_item decomp_item expr_ord
      head_step state_step get_active

attribute [instance] conEctxiLanguage.expr_eqdec conEctxiLanguage.val_eqdec
  conEctxiLanguage.state_eqdec conEctxiLanguage.state_idx_eqdec
  conEctxiLanguage.expr_countable conEctxiLanguage.val_countable
  conEctxiLanguage.state_countable conEctxiLanguage.state_idx_countable

namespace conEctxiLanguage

variable {Λ : conEctxiLanguage}

/-! Only project stuff out of the mixin that is not also in ectxLanguage. -/

/-- Rocq: `fill_item_inj` (an `Inj` instance in Rocq). -/
theorem fill_item_inj (Ki : Λ.ectx_item) : Function.Injective (Λ.fill_item Ki) :=
  Λ.con_ectxi_language_mixin.mixin_fill_item_inj Ki

/-- Rocq: `fill_item_val`. -/
theorem fill_item_val (Ki : Λ.ectx_item) (e : Λ.expr)
    (h : ∃ v, Λ.to_val (Λ.fill_item Ki e) = some v) : ∃ v, Λ.to_val e = some v :=
  Λ.con_ectxi_language_mixin.mixin_fill_item_val Ki e h

/-- Rocq: `fill_item_no_val_inj`. -/
theorem fill_item_no_val_inj (Ki1 Ki2 : Λ.ectx_item) (e1 e2 : Λ.expr)
    (h1 : Λ.to_val e1 = none) (h2 : Λ.to_val e2 = none)
    (h : Λ.fill_item Ki1 e1 = Λ.fill_item Ki2 e2) : Ki1 = Ki2 :=
  Λ.con_ectxi_language_mixin.mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 h1 h2 h

/-- Rocq: `expr_ord_wf`. -/
theorem expr_ord_wf : WellFounded Λ.expr_ord :=
  Λ.con_ectxi_language_mixin.mixin_expr_ord_wf

/-- Rocq: `decomp_ord`. -/
theorem decomp_ord (Ki : Λ.ectx_item) (e e' : Λ.expr) (h : Λ.decomp_item e = some (Ki, e')) :
    Λ.expr_ord e' e :=
  Λ.con_ectxi_language_mixin.mixin_decomp_ord Ki e e' h

/-- Rocq: `decomp_fill_item`. -/
theorem decomp_fill_item (e : Λ.expr) (Ki : Λ.ectx_item) (h : Λ.to_val e = none) :
    Λ.decomp_item (Λ.fill_item Ki e) = some (Ki, e) :=
  Λ.con_ectxi_language_mixin.mixin_decomp_fill_item Ki e h

/-- Rocq: `decomp_fill_item_2`. -/
theorem decomp_fill_item_2 (e e' : Λ.expr) (Ki : Λ.ectx_item)
    (h : Λ.decomp_item e = some (Ki, e')) : Λ.fill_item Ki e' = e ∧ Λ.to_val e' = none :=
  Λ.con_ectxi_language_mixin.mixin_decomp_fill_item_2 e e' Ki h

/-- Rocq: `head_ctx_step_val`. -/
theorem head_ctx_step_val (Ki : Λ.ectx_item) (e : Λ.expr) (σ1 : Λ.state)
    (ρ : Λ.expr × Λ.state × List Λ.expr) (h : 0 < Λ.head_step (Λ.fill_item Ki e) σ1 ρ) :
    ∃ v, Λ.to_val e = some v :=
  Λ.con_ectxi_language_mixin.mixin_head_ctx_step_val Ki e σ1 ρ h

/-- (Rocq: the `val_stuck` field of the mixin, used via `val_head_stuck`.) -/
theorem val_stuck (e1 : Λ.expr) (σ1 : Λ.state) (ρ : Λ.expr × Λ.state × List Λ.expr)
    (h : 0 < Λ.head_step e1 σ1 ρ) : Λ.to_val e1 = none :=
  Λ.con_ectxi_language_mixin.mixin_val_stuck e1 σ1 ρ h

/-- Rocq: `fill_item_not_val`. -/
theorem fill_item_not_val (K : Λ.ectx_item) (e : Λ.expr) (h : Λ.to_val e = none) :
    Λ.to_val (Λ.fill_item K e) = none := by
  cases hK : Λ.to_val (Λ.fill_item K e) with
  | none => rfl
  | some v =>
    obtain ⟨v', hv'⟩ := fill_item_val K e ⟨v, hK⟩
    rw [h] at hv'
    cases hv'

/-- Rocq: `fill`. -/
def fill (K : List Λ.ectx_item) (e : Λ.expr) : Λ.expr := K.foldl (flip Λ.fill_item) e

@[simp] theorem fill_nil (e : Λ.expr) : fill [] e = e := rfl

@[simp] theorem fill_cons (Ki : Λ.ectx_item) (K : List Λ.ectx_item) (e : Λ.expr) :
    fill (Ki :: K) e = fill K (Λ.fill_item Ki e) := rfl

@[simp] theorem fill_singleton (Ki : Λ.ectx_item) (e : Λ.expr) :
    fill [Ki] e = Λ.fill_item Ki e := rfl

/-- Rocq: `fill_app`. -/
theorem fill_app (K1 K2 : List Λ.ectx_item) (e : Λ.expr) :
    fill (K1 ++ K2) e = fill K2 (fill K1 e) :=
  List.foldl_append

/-- Rocq: `fill_val` (an `assert` inside `con_ectxi_lang_ectx_mixin` in Rocq). -/
theorem fill_val (K : List Λ.ectx_item) (e : Λ.expr)
    (h : ∃ v, Λ.to_val (fill K e) = some v) : ∃ v, Λ.to_val e = some v := by
  induction K generalizing e with
  | nil => exact h
  | cons Ki K ih => exact fill_item_val Ki e (ih _ h)

/-- Rocq: `fill_not_val`. -/
theorem fill_not_val (K : List Λ.ectx_item) (e : Λ.expr) (h : Λ.to_val e = none) :
    Λ.to_val (fill K e) = none := by
  cases hK : Λ.to_val (fill K e) with
  | none => rfl
  | some v =>
    obtain ⟨v', hv'⟩ := fill_val K e ⟨v, hK⟩
    rw [h] at hv'
    cases hv'

/-- Rocq: `decomp` (a `Program Fixpoint` by well-founded recursion on `expr_ord`). -/
def decomp : Λ.expr → List Λ.ectx_item × Λ.expr :=
  (expr_ord_wf (Λ := Λ)).fix fun e rec =>
    match h : Λ.decomp_item e with
    | some (Ki, e') =>
      let p := rec e' (decomp_ord Ki e e' h)
      (p.1 ++ [Ki], p.2)
    | none => ([], e)

theorem decomp_some {e e' : Λ.expr} {Ki : Λ.ectx_item} (h : Λ.decomp_item e = some (Ki, e')) :
    decomp e = ((decomp e').1 ++ [Ki], (decomp e').2) := by
  conv_lhs => rw [decomp, WellFounded.fix_eq]
  split
  · next Ki' e'' h' =>
    rw [h] at h'
    cases h'
    rfl
  · next h' =>
    rw [h] at h'
    cases h'

theorem decomp_none {e : Λ.expr} (h : Λ.decomp_item e = none) : decomp e = ([], e) := by
  conv_lhs => rw [decomp, WellFounded.fix_eq]
  split
  · next Ki' e'' h' =>
    rw [h] at h'
    cases h'
  · rfl

/-- Rocq: `decomp_unfold`. -/
theorem decomp_unfold (e : Λ.expr) :
    decomp e =
      match Λ.decomp_item e with
      | some (Ki, e') =>
        match decomp e' with
        | (K, e'') => (K ++ [Ki], e'')
      | none => ([], e) := by
  cases h : Λ.decomp_item e with
  | none => exact decomp_none h
  | some p =>
    obtain ⟨Ki, e'⟩ := p
    rw [decomp_some h]

/-- Rocq: `decomp_inv_nil`. -/
theorem decomp_inv_nil (e e' : Λ.expr) (h : decomp e = ([], e')) :
    Λ.decomp_item e = none ∧ e = e' := by
  cases hd : Λ.decomp_item e with
  | none =>
    rw [decomp_none hd] at h
    simp only [Prod.mk.injEq, true_and] at h
    exact ⟨rfl, h⟩
  | some p =>
    obtain ⟨Ki, e''⟩ := p
    rw [decomp_some hd] at h
    simp at h

/-- Rocq: `list_snoc_singleton_inv`. -/
theorem list_snoc_singleton_inv {A : Type*} (l1 l2 : List A) (a1 a2 : A)
    (h : l1 ++ [a1] = l2 ++ [a2]) : l1 = l2 ∧ a1 = a2 := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨h1, List.singleton_inj.1 h2⟩

/-- Rocq: `decomp_inv_cons`. -/
theorem decomp_inv_cons (Ki : Λ.ectx_item) (K : List Λ.ectx_item) (e e'' : Λ.expr)
    (h : decomp e = (K ++ [Ki], e'')) :
    ∃ e', Λ.decomp_item e = some (Ki, e') ∧ decomp e' = (K, e'') := by
  cases hd : Λ.decomp_item e with
  | none =>
    rw [decomp_none hd] at h
    simp at h
  | some p =>
    obtain ⟨Ki', e'⟩ := p
    rw [decomp_some hd, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, rfl⟩ := list_snoc_singleton_inv _ _ _ _ h1
    exact ⟨e', rfl, Prod.ext h3 h2⟩

/-- Rocq: `con_ectxi_lang_ectx_mixin`. -/
theorem con_ectxi_lang_ectx_mixin :
    ConEctxLanguageMixin Λ.of_val Λ.to_val [] (flip (· ++ ·)) fill decomp Λ.head_step
      Λ.state_step Λ.get_active := by
  constructor
  · exact Λ.con_ectxi_language_mixin.mixin_to_of_val
  · exact Λ.con_ectxi_language_mixin.mixin_of_to_val
  · exact Λ.con_ectxi_language_mixin.mixin_val_stuck
  · exact Λ.con_ectxi_language_mixin.mixin_state_step_head_not_stuck
  · exact Λ.con_ectxi_language_mixin.mixin_state_step_mass
  · exact Λ.con_ectxi_language_mixin.mixin_head_step_mass
  · -- fill_empty
    intro e; rfl
  · -- fill_comp
    intro K1 K2 e
    simp only [flip, fill_app]
  · -- fill_inj
    intro K
    induction K with
    | nil => exact fun _ _ h => h
    | cons Ki K ih => exact fun x y h => fill_item_inj Ki (ih h)
  · -- fill_val
    exact fill_val
  · -- decomp_fill
    intro K
    induction K using List.reverseRecOn with
    | nil =>
      intro e e' h
      exact ((decomp_inv_nil e e' h).2).symm
    | append_singleton K Ki ih =>
      intro e e' h
      obtain ⟨e'', hrei, hre⟩ := decomp_inv_cons Ki K e e' h
      rw [fill_app, ih e'' e' hre, fill_singleton]
      exact (decomp_fill_item_2 _ _ _ hrei).1
  · -- decomp_val_empty
    intro K
    induction K using List.reverseRecOn with
    | nil => intros; rfl
    | append_singleton K Ki ih =>
      intro e e' h hv
      obtain ⟨e'', hrei, hre⟩ := decomp_inv_cons Ki K e e' h
      obtain rfl := ih e'' e' hre hv
      obtain ⟨-, rfl⟩ := decomp_inv_nil _ _ hre
      obtain ⟨v, hv⟩ := hv
      rw [(decomp_fill_item_2 _ _ _ hrei).2] at hv
      cases hv
  · -- decomp_fill_comp
    intro e e' K K' hval hre
    simp only [flip]
    induction K using List.reverseRecOn with
    | nil => simpa using hre
    | append_singleton K Ki ih =>
      rw [fill_app, fill_singleton,
        decomp_some (decomp_fill_item _ _ (fill_not_val K e hval)), ih]
      simp
  · -- step_by_val
    intro K K' e1 e1' σ1 ρ hfill hred hstep
    induction K using List.reverseRecOn generalizing K' with
    | nil => exact ⟨K', by simp [flip]⟩
    | append_singleton K Ki ih =>
      cases K' using List.reverseRecOn with
      | nil =>
        exfalso
        simp only [fill_app, fill_singleton, fill_nil] at hfill
        rw [← hfill] at hstep
        obtain ⟨v, hv⟩ := fill_val K e1 (head_ctx_step_val _ _ _ _ hstep)
        rw [hred] at hv
        cases hv
      | append_singleton K' Ki' _ =>
        simp only [fill_app, fill_singleton] at hfill
        obtain rfl : Ki = Ki' :=
          fill_item_no_val_inj Ki Ki' _ _ (fill_not_val K e1 hred)
            (fill_not_val K' e1' (val_stuck _ _ _ hstep)) hfill
        obtain ⟨K'', rfl⟩ := ih K' (fill_item_inj Ki hfill)
        exact ⟨K'', by simp [flip]⟩
  · -- head_ctx_step_val
    intro K e σ1 ρ
    cases K using List.reverseRecOn with
    | nil => intro; exact Or.inr rfl
    | append_singleton K Ki _ =>
      rw [fill_app, fill_singleton]
      intro h
      exact Or.inl (fill_val K e (head_ctx_step_val _ _ _ _ h))

end conEctxiLanguage

/-- Rocq: `con_ectxi_lang_ectx` (a `Canonical Structure`; `Arguments con_ectxi_lang_ectx :
clear implicits`). -/
abbrev con_ectxi_lang_ectx (Λ : conEctxiLanguage) : conEctxLanguage where
  expr := Λ.expr
  val := Λ.val
  ectx := List Λ.ectx_item
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
  empty_ectx := []
  comp_ectx := flip (· ++ ·)
  fill := conEctxiLanguage.fill
  decomp := conEctxiLanguage.decomp
  head_step := Λ.head_step
  state_step := Λ.state_step
  get_active := Λ.get_active
  con_ectx_language_mixin := conEctxiLanguage.con_ectxi_lang_ectx_mixin

/-- Rocq: `con_ectxi_lang` (a `Canonical Structure`: `ConLanguageOfEctx con_ectxi_lang_ectx`;
`Arguments con_ectxi_lang : clear implicits`). -/
abbrev con_ectxi_lang (Λ : conEctxiLanguage) : conLanguage :=
  ConLanguageOfEctx (con_ectxi_lang_ectx Λ)

attribute [coe] con_ectxi_lang_ectx con_ectxi_lang

/-- Rocq: `Coercion con_ectxi_lang_ectx : conEctxiLanguage >-> conEctxLanguage`. -/
instance : Coe conEctxiLanguage conEctxLanguage := ⟨con_ectxi_lang_ectx⟩

/-- Rocq: `Coercion con_ectxi_lang : conEctxiLanguage >-> conLanguage`. -/
instance : Coe conEctxiLanguage conLanguage := ⟨con_ectxi_lang⟩

section con_ectxi_lang_fields

variable (Λ : conEctxiLanguage)

theorem con_ectxi_lang_ectx_ectx : (con_ectxi_lang_ectx Λ).ectx = List Λ.ectx_item := rfl
theorem con_ectxi_lang_ectx_fill :
    (con_ectxi_lang_ectx Λ).fill = conEctxiLanguage.fill (Λ := Λ) := rfl
theorem con_ectxi_lang_ectx_decomp :
    (con_ectxi_lang_ectx Λ).decomp = conEctxiLanguage.decomp (Λ := Λ) := rfl
theorem con_ectxi_lang_ectx_empty_ectx : (con_ectxi_lang_ectx Λ).empty_ectx = [] := rfl
theorem con_ectxi_lang_ectx_comp_ectx :
    (con_ectxi_lang_ectx Λ).comp_ectx = flip (· ++ ·) := rfl
theorem con_ectxi_lang_ectx_to_val : (con_ectxi_lang_ectx Λ).to_val = Λ.to_val := rfl
theorem con_ectxi_lang_ectx_of_val : (con_ectxi_lang_ectx Λ).of_val = Λ.of_val := rfl
theorem con_ectxi_lang_ectx_head_step :
    (con_ectxi_lang_ectx Λ).head_step = Λ.head_step := rfl

end con_ectxi_lang_fields

namespace conEctxiLanguage

variable {Λ : conEctxiLanguage}

/-- Rocq: `ectxi_language_sub_redexes_are_values`. -/
theorem ectxi_language_sub_redexes_are_values (e : Λ.expr)
    (hsub : ∀ Ki e', e = Λ.fill_item Ki e' → ∃ v, Λ.to_val e' = some v) :
    conEctxLanguage.sub_redexes_are_values (Λ := con_ectxi_lang_ectx Λ) e := by
  intro K e' he hv
  change List Λ.ectx_item at K
  change e = fill K e' at he
  subst he
  cases K using List.reverseRecOn with
  | nil => rfl
  | append_singleton K Ki _ =>
    exfalso
    rw [fill_app, fill_singleton] at hsub
    obtain ⟨v, hv'⟩ := fill_val K e' (hsub Ki (fill K e') rfl)
    change Λ.to_val e' = none at hv
    rw [hv] at hv'
    cases hv'

/-- Every list of context items is a context (Rocq: found through canonical structures as
`con_ectx_lang_ctx` for `con_ectxi_lang_ectx`; here stated for `conEctxiLanguage.fill` so that
instance search finds it). -/
instance con_ectxi_lang_ctx (K : List Λ.ectx_item) :
    ConLanguageCtx (Λ := con_ectxi_lang Λ) (fill K) :=
  conEctxLanguage.con_ectx_lang_ctx (Λ := con_ectxi_lang_ectx Λ) K

/-- Rocq: `ectxi_lang_ctx_item`. -/
instance ectxi_lang_ctx_item (Ki : Λ.ectx_item) :
    ConLanguageCtx (Λ := con_ectxi_lang Λ) (Λ.fill_item Ki) :=
  conEctxLanguage.con_ectx_lang_ctx (Λ := con_ectxi_lang_ectx Λ) [Ki]

end conEctxiLanguage

/-- Rocq: `ConEctxLanguageOfEctxi`. In Rocq this re-packages the fields to help
canonical-structure search; in Lean it is just `con_ectxi_lang_ectx`. -/
abbrev ConEctxLanguageOfEctxi (Λ : conEctxiLanguage) : conEctxLanguage := con_ectxi_lang_ectx Λ

end ConProbLang
