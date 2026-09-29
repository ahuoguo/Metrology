module

public import Metrology.Foxtrot.UnaryRel.UnaryAppRelRules

/-!
# Tactics for the unary logical relation of Foxtrot

Ported from clutch/theories/foxtrot/unary_rel/unary_rel_tactics.v

Symbolic execution tactics for goals `Δ ⊢ REL e : A` (`Foxtrot.UnaryRel.refines`), in the
style of `Metrology.Coneris.WpTactics` and `Metrology.ConProbLang.Spec.SpecTactics`: the
expression `e` is split into an opaque outer evaluation context `Kout` and an expression in
constructor form (derived forms and literal `fill`s are unfolded, Rocq: the `fill ?K ?e` branch
of `rel_reshape_cont_l`), the redex is located at the meta level (Rocq: `reshape_expr`), and the
goal is proved by a tactic lemma (Rocq: `tac_rel_*`).

## Rocq → Lean map
* Lemmas: `tac_rel_bind_l`, `tac_rel_pure_l`, `tac_rel_alloc_l_simpl`,
  `tac_rel_alloctape_l_simpl`: same names (namespace `Foxtrot.UnaryRel`).
* Tactics (Rocq `Tactic Notation`/`Ltac`; all work on a proof-mode goal `Δ ⊢ REL e : A`, and
  start the proof mode if needed, Rocq: `iStartProof`):
  - `rel_bind_l efoc`, `rel_bind_ctx_l K`, `tac_bind_helper efoc` (on a goal `e = fill ?K ?e'`),
    `rel_reshape_cont_l as K e' => tac` (Rocq: `rel_reshape_cont_l tac`, with the identifiers
    `K`, `e'` bound in `tac` as in `reshape_expr .. as K e' => tac`), `rel_finish`,
    `rel_values`, `rel_apply_l lem`;
  - `rel_pure_l efoc in Kf`, `rel_pure_l efoc`, `rel_pure_l`, `rel_pures_l`;
  - `rel_alloc_l l as H at efoc in Kf`, `rel_alloc_l l as H`;
  - `rel_alloctape_l l as H at efoc in Kf`, `rel_alloctape_l l as H`;
  - `rel_rec_l`, `rel_arrow_val`, `rel_arrow`.
  The focus `efoc` and the context `Kf` are terms with holes (of types `expr` and
  `List ectx_item`; Rocq: `open_constr`). `H` is an iris-lean intro pattern.

## Deviations
* Rocq's environment operations (`MaybeIntoLaterNEnvs m ℶ ℶ'`) are premises `Δ ⊢ ▷^[m] Δ'`
  (discharged by the proof mode's `iModAction` with `modality_laterN`); the premises
  `IntoVal e' v'`/`PureExec ..` are explicit hypotheses (as in Rocq, where they are premises).
  `TCEq N (Z.to_nat z)` is `N = z.toNat`.
* `rel_pure_l` always strips the `n` laters of the step (Rocq: the first alternative
  `left; reflexivity` of `(m = n) ∨ m = 0`, which always succeeds).
* `rel_finish` (Rocq: `pm_prettify; iSimpl`) simplifies the expression of the `REL` goal with
  the `wp_expr_simp` simp set of `Metrology.Coneris.WpTactics` (substitutions, derived forms,
  literal evaluation contexts); it does nothing on other goals.
* `rel_values` (Rocq: `iApply refines_ret; eauto with iFrame; rel_finish`) requires the
  expression to be syntactically a value (after unfolding), leaves the goal `|={⊤}=> A v`, and
  tries to close it after `imodintro` with `iassumption`/`itrivial`.
* `rel_apply_l lem` tries `iapply lem` on `REL fill K e' : A` for all decompositions
  `e = fill K e'` (outermost first); `lem` must be stated with `fill K ..` (as the rules of
  `UnaryAppRelRules`), with its arguments left to unification.
* `rel_pures_l` only takes steps whose side condition is solved automatically (Rocq: the `; []`
  of `repeat (rel_pure_l _ in _; [])`).
* `rel_rec_l` (Rocq: `assert (H := AsRecV_recv); rel_pure_l (App _ _)`) uses the `wp_rec`
  pure-step search `findRecPureExec` (a function value unfolding to a `RecV`).
* `rel_alloc_l`, `rel_alloctape_l` introduce the location with the user-given name directly.

## Omitted
* The commented-out Rocq code: `tac_rel_bind_r`, `rel_bind_r`, `rel_bind_ctx_r`,
  `rel_reshape_cont_r`, `rel_apply_r`, `rel_apply`, `tac_rel_pure_r`, `rel_pure_r`,
  `rel_pures_r`, `tac_rel_load_l_simp`, `tac_rel_load_r`, `rel_load_l`, `rel_load_r`,
  `tac_rel_store_l_simpl`, `tac_rel_store_r`, `rel_store_l`, `rel_store_r`, `tac_rel_alloc_r`,
  `rel_alloc_r`, `tac_rel_alloctape_r`, `rel_alloctape_r`, `tac_rel_rand_l`, `tac_rel_rand_r`,
  `rel_rand_l`, `rel_rand_r`, `rel_rec_r`, the backwards-compatibility `rel_*_l`/`rel_*_r`
  notations (`rel_seq_l`, `rel_let_l`, ...), and the `*_atomic` notations.

## Added
* `tac_rel_rewrite` (rewrite the expression of a `REL` goal), `tac_rel_values` (the lemma
  behind `rel_values`), the internal tactics `rel_pure_l_core`, `rel_pure_l_strict`,
  `rel_alloc_l_core`, `rel_alloctape_l_core`, `rel_apply_l_core`, and the meta-level machinery
  (`RelGoal`, `runTacticRel`, `relDecomps`, `quoteListTail`, `relFinishGoal`, ...). The generic
  helpers of `Metrology.Coneris.WpTactics` and `Metrology.ConProbLang.Spec.SpecTactics` are
  reused (`gwpExprSimp`, `findAnyPureExec`, `findRecPureExec`, `gwpSolveSide`,
  `gwpStripLaters`, `gwpFill`, `splitThreadExpr`, `mkAppNamed`, ...).
* Tests at the end of the file.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.UnaryRel

/-! ## General-purpose tactic lemmas -/

section lemmas

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `tac_rel_bind_l`. -/
theorem tac_rel_bind_l (e' : expr) (K : List ectx_item) (Δ : IProp GF) (e : expr) (A : lrel GF)
    (he : e = fill K e') (H : Δ ⊢ REL fill K e' : A) : Δ ⊢ REL e : A := by
  subst he
  exact H

/-- Added: rewrite the expression of a `REL` goal. -/
theorem tac_rel_rewrite {Δ : IProp GF} {e e' : expr} {A : lrel GF} (he : e = e')
    (H : Δ ⊢ REL e' : A) : Δ ⊢ REL e : A := by
  subst he
  exact H

/-- Added: the lemma behind `rel_values` (Rocq: `iApply refines_ret`). -/
theorem tac_rel_values (Δ : IProp GF) (e : expr) (v : val) (A : lrel GF)
    (hv : IntoVal (Λ := con_prob_lang) e v) (H : Δ ⊢ |={⊤}=> A v) : Δ ⊢ REL e : A :=
  H.trans (refines_ret e v A)

/-! ### Pure reductions -/

/-- Rocq: `tac_rel_pure_l`. -/
theorem tac_rel_pure_l (K : List ectx_item) (e1 : expr) (Δ Δ' : IProp GF) (e e2 eres : expr)
    (ϕ : Prop) (n m : ℕ) (A : lrel GF) (hfill : e = fill K e1)
    (hpure : PureExec (Λ := con_prob_lang) ϕ n e1 e2) (hϕ : ϕ) (hm : m = n ∨ m = 0)
    (hlater : Δ ⊢ ▷^[m] Δ') (hres : eres = fill K e2) (H : Δ' ⊢ REL eres : A) :
    Δ ⊢ REL e : A := by
  subst hfill hres
  rcases hm with rfl | rfl
  · exact hlater.trans ((laterN_mono _ H).trans (refines_pure m e1 e2 A ϕ K (Hpure := hpure) hϕ))
  · have := hpure
    exact hlater.trans (H.trans (refines_masked_l n K e1 e2 A ϕ hϕ))

/-! ### Alloc -/

/-- Rocq: `tac_rel_alloc_l_simpl`. -/
theorem tac_rel_alloc_l_simpl (K : List ectx_item) (Δ1 Δ2 : IProp GF) (e e' : expr) (v' : val)
    (A : lrel GF) (he : e = fill K (Alloc e')) (hv : IntoVal (Λ := con_prob_lang) e' v')
    (hlater : Δ1 ⊢ ▷^[1] Δ2)
    (H : Δ2 ⊢ ∀ l : Loc, l ↦ v' -∗ REL fill K (Val (LitV (LitLoc l))) : A) :
    Δ1 ⊢ REL e : A := by
  subst he
  exact hlater.trans ((later_mono H).trans (refines_alloc_l K e' v' A))

/-! ### AllocTape -/

/-- Rocq: `tac_rel_alloctape_l_simpl`. -/
theorem tac_rel_alloctape_l_simpl (K : List ectx_item) (Δ1 Δ2 : IProp GF) (e : expr) (N : ℕ)
    (z : ℤ) (A : lrel GF) (hN : N = z.toNat)
    (he : e = fill K (alloc (Val (LitV (LitInt z))))) (hlater : Δ1 ⊢ ▷^[1] Δ2)
    (H : Δ2 ⊢ ∀ α : Loc, α ↪N (N; []) -∗ REL fill K (Val (LitV (LitLbl α))) : A) :
    Δ1 ⊢ REL e : A := by
  subst he
  exact hlater.trans ((later_mono H).trans (refines_alloctape_l K N z A hN))

end lemmas

/-! ## Meta-level machinery -/

section meta_tactics

open Lean Meta Elab Tactic Qq Coneris

/-- A proof-mode goal `Δ ⊢ REL e : A`, with `e ≡ fill Kout e0` (`e0` in constructor form). -/
meta structure RelGoal where
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  GF : Lean.Expr
  inst : Lean.Expr
  e : Lean.Expr
  Kout? : Option Lean.Expr
  e0 : Lean.Expr
  A : Lean.Expr

/-- `REL e : A` (with the `GF`, instance and `A` of the goal). -/
meta def RelGoal.rel (g : RelGoal) (e : Lean.Expr) : Lean.Expr :=
  mkApp4 (mkConst ``Foxtrot.UnaryRel.refines) g.GF g.inst e g.A

/-- `fill Kout e0'` (or `e0'` if there is no outer context). -/
meta def RelGoal.full (g : RelGoal) (e0' : Lean.Expr) : Lean.Expr := mkThreadExpr g.Kout? e0'

/-- The list `x₁ :: ... :: xₙ :: tail` (`tail = []` if there is none), i.e. `K ++ tail`. -/
meta def quoteListTail (xs : List Lean.Expr) (tail : Option Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``ectx_item) x acc)
    (tail.getD nilEctx)

/-- `fill K e`. -/
meta def mkFillE (K e : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``con_prob_lang.fill) K e

/-- Parse a `REL` goal expression `refines e A`. -/
meta def parseRel? (goal : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let goalE := (← instantiateMVars goal).headBeta.consumeMData
  if goalE.isAppOfArity ``Foxtrot.UnaryRel.refines 4 then return some goalE.getAppArgs
  return none

/-- Split a proof-mode goal `Δ ⊢ REL e : A` into its components (starting the proof mode if
needed, Rocq: `iStartProof`). -/
meta def runTacticRel {α} (tacName : Name) (k : MVarId → RelGoal → ProofModeM α) :
    TacticM α :=
  ProofModeM.runTactic tacName fun mvar {hyps, goal, ..} => do
    let some args ← parseRel? goal
      | throwError "{tacName}: the goal {goal} is not of the form `REL e : A`"
    let (Kout?, e0) ← splitThreadExpr args[2]!
    k mvar { hyps, GF := args[0]!, inst := args[1]!, e := args[2]!, Kout?, e0, A := args[3]! }

/-- All decompositions `e0 = fill K e'` (outermost first, Rocq: `reshape_expr`). -/
meta partial def relDecomps (e0 : Lean.Expr) (K : List Lean.Expr := [])
    (acc : Array (List Lean.Expr × Lean.Expr) := #[]) : Array (List Lean.Expr × Lean.Expr) :=
  let acc := acc.push (K, e0)
  match extractEctxItem e0 with
  | some (Ki, e') => relDecomps e' (Ki :: K) acc
  | none => acc

/-- The expression of the (proof-mode) main goal `Δ ⊢ REL e : A`, if it is one. -/
meta def relMainGoalExpr? : TacticM (Option Lean.Expr) := withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let some ig := parseIrisGoal? ty | return none
  let some args ← parseRel? ig.goal | return none
  return some args[2]!

/-- Proof of `fill Kout e0' = fill Kout e0s` from a proof of `e0' = e0s`. -/
meta def relFullEq (g : RelGoal) (pfeq : Lean.Expr) : MetaM Lean.Expr :=
  match g.Kout? with
  | none => pure pfeq
  | some K => mkCongrArg (mkApp (mkConst ``con_prob_lang.fill) K) pfeq

/-- Rocq: `rel_finish`. Add the goal `Δ ⊢ REL fill Kout e0s : A`, where `e0s` is the
simplification of `e0'`, and return a proof of `Δ ⊢ REL fill Kout e0' : A`. -/
meta def relFinishGoal {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (g : RelGoal) (e0' : Lean.Expr) : ProofModeM Lean.Expr := do
  let (e0s, pfeq?) ← gwpExprSimp e0'
  let pf ← addBIGoal hyps (g.rel (g.full e0s) : Q($prop))
  match pfeq? with
  | none => return pf
  | some pfeq => mkAppNamed ``tac_rel_rewrite [(`he, ← relFullEq g pfeq), (`H, pf)]

/-- Elaborate an evaluation-context pattern (a term of type `List ectx_item` with holes). -/
meta def elabEctxPat (K : Syntax) : TacticM Lean.Expr := withMainContext do
  Tactic.elabTermEnsuringType K (some (← mkAppM ``List #[mkConst ``ectx_item]))
    (mayPostpone := true)

/-- Rocq: `rel_finish`. Simplify the expression of the goal `REL e : A` (no-op on other
goals). -/
elab "rel_finish" : tactic => do
  let some _ ← relMainGoalExpr? | return
  runTacticRel `rel_finish fun mvar g => do
    mvar.assign (← relFinishGoal g.hyps g g.e0)

/-- Rebind the goal `REL e : A` to `REL fill K e' : A` for the decomposition `(Ks, e')` of the
constructor form of `e`. -/
meta def relBindTo (mvar : MVarId) (g : RelGoal) (Ks : List Lean.Expr) (e1 : Lean.Expr) :
    ProofModeM Unit := do
  let Kfull := quoteListTail Ks g.Kout?
  let pf ← addBIGoal g.hyps (g.rel (mkFillE Kfull e1))
  mvar.assign (← mkAppNamed ``tac_rel_bind_l
    [(`e', e1), (`K, Kfull), (`e, g.e), (`A, g.A), (`he, ← mkEqRefl g.e), (`H, pf)])

/-- Rocq: `rel_bind_l efoc`. Rewrite the goal `REL e : A` to `REL fill K e' : A`, for the first
decomposition `e = fill K e'` (outermost first) such that `e'` unifies with `efoc`. -/
elab "rel_bind_l " f:term:max : tactic => do
  let focus ← elabFocus f
  runTacticRel `rel_bind_l fun mvar g => do
    for (Ks, e1) in relDecomps g.e0 do
      if let some _ ← observing? (do guard (← isDefEq e1 focus)) then
        relBindTo mvar g Ks e1
        return
    throwError "rel_bind_l: cannot find {focus} in {g.e}"

/-- Rocq: `rel_bind_ctx_l K`. Rewrite the goal `REL e : A` to `REL fill K e' : A` (for the
first decomposition of `e` with evaluation context `K`). -/
elab "rel_bind_ctx_l " K:term:max : tactic => do
  let KE ← elabEctxPat K
  runTacticRel `rel_bind_ctx_l fun mvar g => do
    for (Ks, e1) in relDecomps g.e0 do
      if let some _ ← observing? (do guard (← isDefEq (quoteListTail Ks g.Kout?) KE)) then
        relBindTo mvar g Ks e1
        return
    throwError "rel_bind_ctx_l: cannot decompose {g.e} with the evaluation context {KE}"

/-- Rocq: `tac_bind_helper efoc`. Solve a goal `e = fill ?K ?e'` (or `fill K0 e = fill ?K ?e'`)
by instantiating `?e'` with the first subexpression of `e` (outermost first) that unifies with
`efoc`, and `?K` with its evaluation context. -/
elab "tac_bind_helper " f:term:max : tactic => withMainContext do
  let focus ← elabFocus f
  let mvar ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← mvar.getType))
  let some (_, lhs, rhs) := ty.eq? | throwError "tac_bind_helper: the goal is not an equation"
  let rhs ← instantiateMVars rhs
  let (``con_prob_lang.fill, #[Km, em]) := rhs.consumeMData.getAppFnArgs
    | throwError "tac_bind_helper: the right-hand side {rhs} is not of the form `fill _ _`"
  let (Kout?, e0) ← splitThreadExpr lhs
  for (Ks, e1) in relDecomps e0 do
    let s ← saveState
    let ok ← observing? (do
      guard (← isDefEq e1 focus)
      guard (← isDefEq Km (quoteListTail Ks Kout?))
      guard (← isDefEq em e1)
      guard (← isDefEq lhs rhs))
    if ok.isSome then
      mvar.assign (← mkEqRefl lhs)
      replaceMainGoal []
      return
    s.restore
  throwError "tac_bind_helper: cannot find {focus} in {lhs}"

/-- Rocq: `rel_reshape_cont_l tac`. `rel_reshape_cont_l as K e' => tac` runs the tactic
sequence `tac`, in which the identifiers `K` and `e'` stand for the evaluation context and
subexpression of a decomposition `e = fill K e'` of the goal `REL e : A`, for every such
decomposition from the outermost inwards, until `tac` succeeds. -/
syntax (name := relReshapeContL) "rel_reshape_cont_l " " as " ident ppSpace ident " => "
  tacticSeq : tactic

@[tactic relReshapeContL] meta def evalRelReshapeContL : Tactic := fun stx => do
  let `(tactic| rel_reshape_cont_l as $K $e' => $tac) := stx | throwUnsupportedSyntax
  evalTactic (← `(tactic| istart))
  let some e ← relMainGoalExpr? | throwError "rel_reshape_cont_l: the goal is not a `REL`"
  let (Kout?, e0) ← splitThreadExpr e
  for (Ks, inner) in relDecomps e0 do
    let s ← saveState
    try
      let Kstx ← Term.exprToSyntax (quoteListTail Ks Kout?)
      let innerStx ← Term.exprToSyntax inner
      let tac' ← tac.raw.replaceM fun s => do
        if s.isIdent && s.getId == K.getId then return some Kstx.raw
        if s.isIdent && s.getId == e'.getId then return some innerStx.raw
        return none
      evalTactic tac'
      return
    catch _ => s.restore
  throwError "rel_reshape_cont_l: the tactic failed for all evaluation contexts of{indentExpr e}"

/-- Rocq: `rel_values`. Reduce `REL v : A` (for a value `v`) to `|={⊤}=> A v`. -/
elab "rel_values_core" : tactic =>
  runTacticRel `rel_values fun mvar g => do
    let some v := (if g.Kout?.isNone then isValExpr? g.e0 else none)
      | throwError "rel_values: {g.e} is not a value"
    let hv ← synthInstance (← mkAppOptM ``IntoVal #[mkConst ``con_prob_lang, g.e, v])
    let goal ← mkAppM ``FUpd.fupd #[← mkAppM ``CoPset.full #[], ← mkAppM ``CoPset.full #[],
      mkApp (← mkAppM ``lrel.lrel_car #[g.A]) v]
    let pf ← addBIGoal g.hyps goal
    mvar.assign (← mkAppNamed ``tac_rel_values
      [(`e, g.e), (`v, v), (`A, g.A), (`hv, hv), (`H, pf)])

/-- Rocq: `rel_values`. -/
macro "rel_values" : tactic =>
  `(tactic| (rel_values_core; try (imodintro; first | iassumption | itrivial)))

/-- The core of `rel_apply_l`: `iapply lem` on `REL fill K e' : A`, for the first
decomposition `e = fill K e'` (outermost first) for which it succeeds. -/
elab "rel_apply_l_core " pmt:pmTerm : tactic => do
  evalTactic (← `(tactic| istart))
  let some e ← relMainGoalExpr? | throwError "rel_apply_l: the goal is not a `REL`"
  let (_, e0) ← splitThreadExpr e
  let n := (relDecomps e0).size
  for i in [0:n] do
    let s ← saveState
    try
      runTacticRel `rel_apply_l fun mvar g => do
        let (Ks, e1) := (relDecomps g.e0)[i]!
        relBindTo mvar g Ks e1
      evalTactic (← `(tactic| iapply $pmt))
      return
    catch _ => s.restore
  throwError "rel_apply_l: cannot apply {pmt}"

/-- Rocq: `rel_apply_l lem`. -/
macro "rel_apply_l " pmt:pmTerm : tactic =>
  `(tactic| focus (rel_apply_l_core $pmt; all_goals try rel_finish))

/-- The core of `rel_pure_l`: find the first redex (outermost first) with context unifying with
`Kf` and redex unifying with `efoc` for which `find` finds a pure step, and take the step. -/
meta def relPureCore (tacName : Name) (focus Kf : Syntax) (strict : Bool)
    (find : Lean.Expr → ProofModeM PureStepRes) : TacticM Unit := do
  let focusE ← elabFocus focus
  let KfE ← elabEctxPat Kf
  runTacticRel tacName fun mvar g => do
    let some (res, K, e1) ← reshapeExpr g.e0 fun K e1 => do
        guard (← isDefEq (quoteListTail K g.Kout?) KfE)
        guard (← isDefEq e1 focusE)
        find e1
      | throwError "{tacName}: cannot find the reduct"
    let Kfull := quoteListTail K g.Kout?
    let hφ ← match res.hφ with
      | some hφ => pure hφ
      | none => gwpSolveSide res.φ strict
    let ⟨_, hyps', pfLater⟩ ← gwpStripLaters g.hyps res.n
    let e0' ← gwpFill K res.e2
    let (e0s, pfeq?) ← gwpExprSimp e0'
    let eres := g.full e0s
    let pfNext ← addBIGoal hyps' (g.rel eres)
    let hres ← match pfeq? with
      | none => mkEqRefl eres
      | some pfeq => mkEqSymm (← relFullEq g pfeq)
    let hm ← mkAppOptM ``Or.inl #[← mkEq res.n res.n, ← mkEq res.n (mkNatLit 0),
      ← mkEqRefl res.n]
    mvar.assign (← mkAppNamed ``tac_rel_pure_l
      [(`K, Kfull), (`e1, e1), (`e, g.e), (`e2, res.e2), (`eres, eres), (`ϕ, res.φ),
       (`n, res.n), (`m, res.n), (`A, g.A), (`hfill, ← mkEqRefl g.e), (`hpure, res.inst),
       (`hϕ, hφ), (`hm, hm), (`hlater, pfLater), (`hres, hres), (`H, pfNext)])

/-- The core of `rel_pure_l efoc in Kf`. -/
elab "rel_pure_l_core " f:term:max ppSpace K:term:max : tactic =>
  relPureCore `rel_pure_l f K false findAnyPureExec

/-- `rel_pure_l` failing if the side condition cannot be solved (used by `rel_pures_l`). -/
elab "rel_pure_l_strict" : tactic => do
  relPureCore `rel_pure_l (← `(_)) (← `(_)) true findAnyPureExec

/-- Rocq: `rel_pure_l efoc in Kf`. Take a pure step at the first redex (outermost first) which
unifies with `efoc` and whose evaluation context unifies with `Kf`. The side condition of the
step is discharged if possible, and otherwise left as a goal. -/
syntax "rel_pure_l" (ppSpace colGt term:max)? (" in " term:max)? : tactic

macro_rules
  | `(tactic| rel_pure_l $f in $K) => `(tactic| rel_pure_l_core $f $K)
  | `(tactic| rel_pure_l $f) => `(tactic| rel_pure_l_core $f _)
  | `(tactic| rel_pure_l in $K) => `(tactic| rel_pure_l_core _ $K)
  | `(tactic| rel_pure_l) => `(tactic| rel_pure_l_core _ _)

/-- Rocq: `rel_pures_l`. Take pure steps as long as possible (only steps whose side condition
is solved automatically). -/
macro "rel_pures_l" : tactic => `(tactic| (istart; repeat rel_pure_l_strict))

/-- Rocq: `rel_rec_l`. Beta-reduce the first application of a (possibly hidden behind a
definition) recursive function to a value. -/
elab "rel_rec_l" : tactic => do
  relPureCore `rel_rec_l (← `(_)) (← `(_)) false findRecPureExec

/-- Match `Alloc (Val v)` (i.e. `AllocN (Val #1) (Val v)`). -/
meta def matchAlloc? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let (``expr.AllocN, #[a1, a2]) := e.consumeMData.getAppFnArgs | return none
  let some n := matchIntVal? a1 | return none
  unless ← isDefEq n (toExpr (1 : Int)) do return none
  return isValExpr? a2

/-- The right-hand side `Q` of the premise `h : Δ ⊢ Q` of the constant `c`, applied to the
named arguments `args`. -/
meta def premiseGoal (c : Name) (args : List (Name × Lean.Expr)) (h : Name) :
    MetaM Lean.Expr := do
  let ty ← inferType (← mkConstWithFreshMVarLevels c)
  let names ← forallTelescope ty fun xs _ => xs.mapM fun x => x.fvarId!.getUserName
  let (mvs, bis, _) ← forallMetaTelescope ty
  for i in [0:mvs.size] do
    let some v := args.lookup names[i]! | continue
    unless ← isDefEq mvs[i]! v do throwError "premiseGoal: cannot assign {names[i]!} of {c}"
  for (mv, bi) in mvs.zip bis do
    if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
      mv.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType mv)))
  let some i := names.idxOf? h | throwError "premiseGoal: {c} has no argument {h}"
  let hty ← instantiateMVars (← inferType mvs[i]!)
  return hty.appArg!

/-- The core of `rel_alloc_l l as H at efoc in Kf` (Rocq: `tac_rel_alloc_l_simpl`): leaves the
goal `∀ l, l ↦ v -∗ REL fill K (Val #l) : A`. -/
elab "rel_alloc_l_core " f:term:max ppSpace Kf:term:max : tactic => do
  let focusE ← elabFocus f
  let KfE ← elabEctxPat Kf
  runTacticRel `rel_alloc_l fun mvar g => do
    let some (v, K, _e1) ← reshapeExpr g.e0 fun K e1 => do
        guard (← isDefEq (quoteListTail K g.Kout?) KfE)
        guard (← isDefEq e1 focusE)
        let some v ← matchAlloc? e1 | failure
        return v
      | throwError "rel_alloc_l: cannot find 'Alloc'"
    let Kfull := quoteListTail K g.Kout?
    let e' := mkValE v
    let hv ← synthInstance (← mkAppOptM ``IntoVal #[mkConst ``con_prob_lang, e', v])
    let ⟨_, hyps', pfLater⟩ ← gwpStripLaters g.hyps (mkNatLit 1)
    let args := [(`K, Kfull), (`e, g.e), (`e', e'), (`v', v), (`A, g.A)]
    let goal ← premiseGoal ``tac_rel_alloc_l_simpl args `H
    let pf ← addBIGoal hyps' goal
    mvar.assign (← mkAppNamed ``tac_rel_alloc_l_simpl
      (args ++ [(`he, ← mkEqRefl g.e), (`hv, hv), (`hlater, pfLater), (`H, pf)]))

/-- Rocq: `rel_alloc_l l as "H" at efoc in Kf` and `rel_alloc_l l as "H"` (which first takes
the pure steps, `rel_pures_l`). -/
syntax "rel_alloc_l " ident " as " introPat (" at " term:max " in " term:max)? : tactic

macro_rules
  | `(tactic| rel_alloc_l $l:ident as $H:introPat at $f in $K) =>
    `(tactic| focus
        rel_alloc_l_core $f $K
        iintro %$l:ident $H:introPat
        try rel_finish)
  | `(tactic| rel_alloc_l $l:ident as $H:introPat) =>
    `(tactic| focus
        rel_pures_l
        rel_alloc_l_core _ _
        iintro %$l:ident $H:introPat
        try rel_finish)

/-- The core of `rel_alloctape_l l as H at efoc in Kf` (Rocq: `tac_rel_alloctape_l_simpl`):
leaves the goal `∀ α, α ↪N (N; []) -∗ REL fill K (Val #lbl:α) : A`. -/
elab "rel_alloctape_l_core " f:term:max ppSpace Kf:term:max : tactic => do
  let focusE ← elabFocus f
  let KfE ← elabEctxPat Kf
  runTacticRel `rel_alloctape_l fun mvar g => do
    let some (z, K, _e1) ← reshapeExpr g.e0 fun K e1 => do
        guard (← isDefEq (quoteListTail K g.Kout?) KfE)
        guard (← isDefEq e1 focusE)
        let (``expr.AllocTape, #[a]) := e1.consumeMData.getAppFnArgs | failure
        let some z := matchIntVal? a | failure
        return z
      | throwError "rel_alloctape_l: cannot find 'AllocTape'"
    let Kfull := quoteListTail K g.Kout?
    let N ← gwpValSimpDefEq (← mkAppM ``Int.toNat #[z])
    let hN ← gwpSolveSide (← mkEq N (← mkAppM ``Int.toNat #[z])) false
    let ⟨_, hyps', pfLater⟩ ← gwpStripLaters g.hyps (mkNatLit 1)
    let args := [(`K, Kfull), (`e, g.e), (`N, N), (`z, z), (`A, g.A)]
    let goal ← premiseGoal ``tac_rel_alloctape_l_simpl args `H
    let pf ← addBIGoal hyps' goal
    mvar.assign (← mkAppNamed ``tac_rel_alloctape_l_simpl
      (args ++ [(`hN, hN), (`he, ← mkEqRefl g.e), (`hlater, pfLater), (`H, pf)]))

/-- Rocq: `rel_alloctape_l l as "H" at efoc in Kf` and `rel_alloctape_l l as "H"`. -/
syntax "rel_alloctape_l " ident " as " introPat (" at " term:max " in " term:max)? : tactic

macro_rules
  | `(tactic| rel_alloctape_l $l:ident as $H:introPat at $f in $K) =>
    `(tactic| focus
        rel_alloctape_l_core $f $K
        iintro %$l:ident $H:introPat
        try rel_finish)
  | `(tactic| rel_alloctape_l $l:ident as $H:introPat) =>
    `(tactic| focus
        rel_pures_l
        rel_alloctape_l_core _ _
        iintro %$l:ident $H:introPat
        try rel_finish)

/-- Rocq: `rel_arrow_val`. -/
macro "rel_arrow_val" : tactic =>
  `(tactic| (rel_pures_l
             first
               | iapply refines_arrow_val
               | fail "rel_arrow_val: cannot apply the closure rule"
             imodintro))

/-- Rocq: `rel_arrow`. -/
macro "rel_arrow" : tactic =>
  `(tactic| (rel_pures_l
             first
               | iapply refines_arrow
               | fail "rel_arrow: cannot apply the closure rule"
             imodintro))

end meta_tactics

/-! ## Tests (not in Rocq) -/

section tests

variable {GF : BundledGFunctors} [foxtrotGS GF]

example : ⊢@{IProp GF} REL cpl(#1 + #2) : lrel_int := by
  rel_pures_l
  rel_values
  unfold lrel_int
  iexists 3
  ipureintro
  rfl

example (A : lrel GF) :
    (∀ l : Loc, l ↦ LitV (LitInt 1) -∗ REL Val (LitV (LitLoc l)) : A) ⊢
      REL cpl(let x := #0 + #1; ref(x)) : A := by
  iintro H
  rel_alloc_l l as Hl
  iapply H $$ Hl

example (A : lrel GF) (K : List ectx_item) :
    (∀ l : Loc, l ↦ LitV (LitInt 1) -∗ REL fill K cpl(#l) : A) ⊢
      REL fill K cpl(ref(#1)) : A := by
  iintro H
  rel_alloc_l l as Hl at _ in _
  iapply H $$ Hl

example (A : lrel GF) :
    (∀ α : Loc, α ↪N (3; []) -∗ REL Val (LitV (LitLbl α)) : A) ⊢
      REL cpl(alloc(#3)) : A := by
  iintro H
  rel_alloctape_l α as Hα
  iapply H $$ Hα

example (K : List ectx_item) (A : lrel GF) :
    (REL fill K cpl(#3) : A) ⊢ REL fill K cpl(snd((#1 + #2, #3))) : A := by
  iintro H
  rel_pure_l (BinOp _ _ _)
  rel_pure_l
  rel_pure_l
  iexact H

example (A : lrel GF) :
    (REL Val (LitV (LitInt 2)) : A) ⊢
      REL App (Val (RecV .BAnon (.BNamed "x") (BinOp PlusOp (Var "x") (Val (LitV (LitInt 1))))))
        (Val (LitV (LitInt 1))) : A := by
  iintro H
  rel_rec_l
  rel_pures_l
  iexact H

example (A : lrel GF) :
    (∀ l : Loc, l ↦ LitV (LitInt 1) -∗ REL cpl(fst((#l, #1))) : A) ⊢
      REL cpl(fst((ref(#1), #1))) : A := by
  iintro H
  rel_apply_l refines_alloc_l
  inext
  iintro %l Hl
  rel_finish
  iapply H $$ Hl

example (A : lrel GF) :
    (REL cpl(#1 + #2) : A) ⊢ REL cpl(if #true then #1 + #2 else #0) : A := by
  iintro H
  rel_bind_l (If _ _ _)
  rel_pure_l
  iexact H

example (e : expr) (K : List ectx_item) :
    ∃ K', fill K (Fst (Pair e (Val (LitV (LitInt 1))))) = fill K' e :=
  ⟨_, by tac_bind_helper e⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example (A : lrel GF) (K : List ectx_item) :
    (REL fill K cpl(fst((#2, #1))) : A) ⊢ REL fill K cpl(fst((#1 + #1, #1))) : A := by
  iintro H
  rel_bind_ctx_l (PairLCtx (LitV (LitInt 1)) :: FstCtx :: K)
  rel_reshape_cont_l as K' e' => rel_pure_l e' in K'
  rel_finish
  iexact H

example : ⊢@{IProp GF} REL Val (RecV .BAnon (.BNamed "x") (Var "x")) :
    lrel_arr lrel_int lrel_int := by
  rel_arrow_val
  iintro %v Hv
  rel_rec_l
  rel_values

end tests

end Foxtrot.UnaryRel
