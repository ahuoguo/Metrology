module

public import Metrology.Foxtrot.BinaryRel.BinaryAppRelRules

/-!
# Tactics for Foxtrot's binary logical relation

Ported from clutch/theories/foxtrot/binary_rel/binary_rel_tactics.v

The tactics work on proof-mode goals `Δ ⊢ REL e << t : A` (`refines e t A`). As in
`Metrology.ConProbLang.Spec.SpecTactics` (the `tp_*` tactics) and
`Metrology.Coneris.WpTactics` (the `wp_*` tactics), they are elaborators in iris-lean's
`ProofModeM`: the expression of a side is split into an opaque outer evaluation context `Kout`
(if the side has the form `fill Kout e0`) and an expression `e0` in constructor form, whose
decompositions `e0 = fill K e1` are enumerated by `reshapeExpr` (Rocq: `reshape_expr`); the
full evaluation context is the list `K ++ Kout` (built as a literal `k1 :: .. :: kn :: Kout`).

## Rocq → Lean map
* Tactic lemmas (same names): `tac_rel_bind_l`, `tac_rel_bind_r`, `tac_rel_pure_l`,
  `tac_rel_pure_r`, `tac_rel_alloc_l_simpl`, `tac_rel_alloc_r`, `tac_rel_alloctape_l_simpl`,
  `tac_rel_alloctape_r`. Rocq's `envs_entails ℶ P` is `Δ ⊢ P`, and
  `MaybeIntoLaterNEnvs m ℶ ℶ'` is the premise `Δ ⊢ ▷^[m] Δ'` (the result of iris-lean's
  `iModAction` with `modality_laterN`). `PureExec` and `IntoVal` premises are
  instance-implicit, `TCEq N (Z.to_nat z)` is `hN : N = z.toNat`.
* Tactics (same names; the focus `ef` and the context `Kf` are Lean terms with holes, Rocq's
  `open_constr`):
  - `rel_bind_l ef`, `rel_bind_r ef`, `rel_bind_ctx_l K`, `rel_bind_ctx_r K`;
  - `rel_finish` (Rocq: `pm_prettify; iSimpl`; here: unfold literal evaluation contexts,
    derived forms and substitutions on both sides, the `wp_expr_simp` simp set);
  - `rel_values` (Rocq: `iApply refines_ret; eauto with iFrame; rel_finish`): leaves the goal
    `|={⊤}=> A v1 v2` (unless it is closed by `iassumption` after `imodintro`);
  - `rel_apply_l lem`, `rel_apply_r lem`, `rel_apply lem` (`lem` an iris-lean proof-mode term,
    as for `iapply`): try `iapply lem` on the decompositions of the LHS (resp. RHS, resp. both
    sides) in the order of `reshapeExpr`, then `rel_finish` on the resulting goals;
  - `rel_pure_l ef in Kf`, `rel_pure_l ef`, `rel_pure_l`, and the same for `rel_pure_r`;
    `rel_pures_l`, `rel_pures_r`;
  - `rel_alloc_l l as H at ef in Kf`, `rel_alloc_l l as H`, `rel_alloc_r l as H at ef in Kf`,
    `rel_alloc_r l as H`, `rel_alloctape_l α as H at ef in Kf`, `rel_alloctape_l α as H`,
    `rel_alloctape_r α as H at ef in Kf`, `rel_alloctape_r α as H` (`H` an iris-lean intro
    pattern, `l`/`α` an identifier);
  - `rel_rec_l`, `rel_rec_r`, `rel_arrow_val`, `rel_arrow`.

## Deviations
* `rel_pure_l` always strips `n` laters from the context (Rocq: the first branch `m = n` of
  `first [left; ..| right; ..]`, which always succeeds); the `m = 0` case of `tac_rel_pure_l`
  is kept in the lemma.
* `rel_pures_l`/`rel_pures_r` only take steps whose side condition is solved automatically
  (Rocq: `rel_pure_l _ in _; []`), with `wp_solve_side` (Rocq: `solve_vals_compare_safe`).
  `rel_pure_l`/`rel_pure_r` leave an unsolved side condition as a goal.
* The `IntoVal` premises: the tactics require the argument to be syntactically `Val v`.
* `rel_apply_r`/`rel_apply` do not try `solve_ndisj` (the relation has no mask).
* `rel_apply_*` first try `iapply lem` on the goal as it is, and only then on the
  decompositions `fill K e` (iris-lean's `iapply` does not unfold `fill [] e` to `e`).
* The tactics that leave side conditions put them after the main goal.
* Rocq's `rewrite ?Nat2Z.id` in `rel_alloctape_*` is the normalisation of `N = z.toNat`
  (`gwpValSimpDefEq`).
* Rocq has no `ElimModal (pupd ..)` instance for the `REL` judgement, but the Lean port adds
  `elim_pupd_refines` in `BinaryModel`, so the `tp_*` tactics also fire on `REL` goals. The
  `rel_*_r` tactics here still go through the `refines_*_r` rules.

## Omitted
* `tac_bind_helper` and `rel_reshape_cont_l`/`rel_reshape_cont_r` (Ltac helpers; replaced by
  the meta-level functions `relReshape` and `relBindNth`).
* All commented-out Rocq code: `tac_rel_load_l_simp`, `tac_rel_load_r`, `rel_load_l`,
  `rel_load_r`, `tac_rel_store_l_simpl`, `tac_rel_store_r`, `rel_store_l`, `rel_store_r`,
  `tac_rel_rand_l`, `tac_rel_rand_r`, `rel_rand_l`, `rel_rand_r`, the `*_atomic` variants and
  the backwards-compatibility tactics (`rel_seq_l`, `rel_let_l`, ...). In particular there are
  no `rel_load_*`/`rel_store_*` tactics (as in Rocq, there are no `refines_load_*` rules).

## Added
* `tac_rel_rewrite` (for `rel_finish`), `tac_rel_values` (for `rel_values`), the internal
  tactics `rel_pure_l_strict`, `rel_pure_r_strict`, `rel_alloc_l_core`, `rel_alloc_r_core`,
  `rel_alloctape_l_core`, `rel_alloctape_r_core`, `rel_apply_l_core`, `rel_apply_r_core`,
  `rel_apply_core`, and the meta-level machinery (`RelGoal`, `runTacticRel`, `relReshape`,
  `relApplyLemma`, `relSimpSide`, `relBindCore`, `relBindNth`, `relTryBindsFrom`, `relTryBinds`,
  `relPureCore`, `relFindRedex`, `relAllocCore`, `relSideMVar`, `relSolvePending`, `mkFullCtx`,
  `mkFillE`, `mkRflHint`, `elabCtx`). The generic helpers of `Metrology.Coneris.WpTactics` and
  `Metrology.ConProbLang.Spec.SpecTactics` are reused (`splitThreadExpr`, `reshapeExpr`,
  `gwpExprSimp`, `gwpStripLaters`, `gwpSolveSide`, `findAnyPureExec`, `findRecPureExec`,
  `matchAlloc?`, `matchAllocTape?`, `mkAppNamed`, ...).
* Tests at the end of the file.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

section lemmas

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-! ## General-purpose tactic lemmas -/

/-- Rocq: `tac_rel_bind_l`. -/
theorem tac_rel_bind_l (e' : expr) (K : List ectx_item) {Δ : IProp GF} (e t : expr)
    (A : lrel GF) (he : e = fill K e') (h : Δ ⊢ REL fill K e' << t : A) :
    Δ ⊢ REL e << t : A := by
  subst he; exact h

/-- Rocq: `tac_rel_bind_r`. -/
theorem tac_rel_bind_r (t' : expr) (K : List ectx_item) {Δ : IProp GF} (e t : expr)
    (A : lrel GF) (he : t = fill K t') (h : Δ ⊢ REL e << fill K t' : A) :
    Δ ⊢ REL e << t : A := by
  subst he; exact h

/-- Helper (for `rel_finish`): rewrite both sides. -/
theorem tac_rel_rewrite {Δ : IProp GF} (e e' t t' : expr) (A : lrel GF) (he : e = e')
    (ht : t = t') (h : Δ ⊢ REL e' << t' : A) : Δ ⊢ REL e << t : A := by
  subst he ht; exact h

/-- Helper (for `rel_values`). -/
theorem tac_rel_values {Δ : IProp GF} (v1 v2 : val) (A : lrel GF)
    (h : Δ ⊢ |={⊤}=> A v1 v2) : Δ ⊢ REL Val v1 << Val v2 : A :=
  h.trans (refines_ret (Val v1) (Val v2) v1 v2 A)

/-! ## Symbolic execution: pure reductions -/

/-- Rocq: `tac_rel_pure_l`. -/
theorem tac_rel_pure_l (K : List ectx_item) (e1 : expr) {Δ Δ' : IProp GF} (e e2 eres : expr)
    (ϕ : Prop) (n m : ℕ) (t : expr) (A : lrel GF) (hfill : e = fill K e1)
    [hpure : PureExec (Λ := con_prob_lang) ϕ n e1 e2] (hϕ : ϕ) (hm : m = n ∨ m = 0)
    (hlater : Δ ⊢ ▷^[m] Δ') (hres : eres = fill K e2) (hcont : Δ' ⊢ REL eres << t : A) :
    Δ ⊢ REL e << t : A := by
  subst hfill hres
  rcases hm with rfl | rfl
  · exact hlater.trans ((laterN_mono m hcont).trans (refines_pure_l m K e1 e2 t A ϕ hϕ))
  · exact hlater.trans (hcont.trans (refines_masked_l n K e1 e2 t A ϕ hϕ))

/-- Rocq: `tac_rel_pure_r`. -/
theorem tac_rel_pure_r (K : List ectx_item) (e1 : expr) {Δ : IProp GF} (e e2 eres : expr)
    (ϕ : Prop) (n : ℕ) (t : expr) (A : lrel GF) (hfill : e = fill K e1)
    [hpure : PureExec (Λ := con_prob_lang) ϕ n e1 e2] (hϕ : ϕ) (hres : eres = fill K e2)
    (hcont : Δ ⊢ REL t << eres : A) : Δ ⊢ REL t << e : A := by
  subst hfill hres
  exact hcont.trans (refines_pure_r K e1 e2 t A n ϕ hϕ)

/-! ## Symbolic execution: allocation -/

/-- Rocq: `tac_rel_alloc_l_simpl`. -/
theorem tac_rel_alloc_l_simpl (K : List ectx_item) {Δ1 Δ2 : IProp GF} (e t e' : expr) (v' : val)
    (A : lrel GF) (hfill : e = fill K (Alloc e')) [hv : IntoVal (Λ := con_prob_lang) e' v']
    (hlater : Δ1 ⊢ ▷^[1] Δ2)
    (hcont : Δ2 ⊢ ∀ l : Loc, l ↦ v' -∗ REL fill K (Val (LitV (LitLoc l))) << t : A) :
    Δ1 ⊢ REL e << t : A := by
  subst hfill
  exact hlater.trans ((laterN_mono 1 hcont).trans (refines_alloc_l K e' v' t A))

/-- Rocq: `tac_rel_alloc_r`. -/
theorem tac_rel_alloc_r (K' : List ectx_item) {Δ : IProp GF} (t' : expr) (v' : val) (e t : expr)
    (A : lrel GF) (hfill : t = fill K' (Alloc t')) [hv : IntoVal (Λ := con_prob_lang) t' v']
    (hcont : Δ ⊢ ∀ l : Loc, l ↦ₛ v' -∗ REL e << fill K' (Val (LitV (LitLoc l))) : A) :
    Δ ⊢ REL e << t : A := by
  subst hfill
  exact hcont.trans (refines_alloc_r K' t' v' e A)

/-- Rocq: `tac_rel_alloctape_l_simpl`. -/
theorem tac_rel_alloctape_l_simpl (K : List ectx_item) {Δ1 Δ2 : IProp GF} (e : expr) (N : ℕ)
    (z : ℤ) (t : expr) (A : lrel GF) (hN : N = z.toNat)
    (hfill : e = fill K (AllocTape (Val (LitV (LitInt z))))) (hlater : Δ1 ⊢ ▷^[1] Δ2)
    (hcont : Δ2 ⊢ ∀ α : Loc, α ↪N (N; []) -∗ REL fill K (Val (LitV (LitLbl α))) << t : A) :
    Δ1 ⊢ REL e << t : A := by
  subst hfill
  exact hlater.trans ((laterN_mono 1 hcont).trans (refines_alloctape_l K N z t A hN))

/-- Rocq: `tac_rel_alloctape_r`. -/
theorem tac_rel_alloctape_r (K' : List ectx_item) {Δ : IProp GF} (e : expr) (N : ℕ) (z : ℤ)
    (t : expr) (A : lrel GF) (hN : N = z.toNat)
    (hfill : t = fill K' (AllocTape (Val (LitV (LitInt z)))))
    (hcont : Δ ⊢ ∀ α : Loc, α ↪ₛN (N; []) -∗ REL e << fill K' (Val (LitV (LitLbl α))) : A) :
    Δ ⊢ REL e << t : A := by
  subst hfill
  exact hcont.trans (refines_alloctape_r K' N z e A hN)

end lemmas

/-! ## The tactics -/

section meta_tactics

open Lean Meta Elab Tactic Coneris Qq

/-- A proof-mode goal `Δ ⊢ REL e << t : A`. -/
public meta structure RelGoal where
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  GF : Lean.Expr
  inst : Lean.Expr
  e : Lean.Expr
  t : Lean.Expr
  A : Lean.Expr

/-- The LHS (`left = true`) or the RHS of the goal. -/
public meta def RelGoal.side (g : RelGoal) (left : Bool) : Lean.Expr :=
  if left then g.e else g.t

/-- Split a proof-mode goal `Δ ⊢ REL e << t : A` into its components. -/
public meta def runTacticRel {α} (tacName : Name) (k : MVarId → RelGoal → ProofModeM α) :
    TacticM α :=
  ProofModeM.runTactic tacName fun mvar {hyps, goal, ..} => do
    let goalE := (← instantiateMVars goal).headBeta.consumeMData
    unless goalE.isAppOfArity ``refines 5 do
      throwError "{tacName}: the goal {goal} is not of the form 'REL _ << _ : _'"
    let args := goalE.getAppArgs
    k mvar { hyps, GF := args[0]!, inst := args[1]!, e := args[2]!, t := args[3]!, A := args[4]! }

/-- The evaluation context `k1 :: .. :: kn :: Kout` (`Kout = []` if there is none), i.e. the
list `K ++ Kout` for the literal items `K` (innermost first). -/
public meta def mkFullCtx (items : List Lean.Expr) (Kout? : Option Lean.Expr) : Lean.Expr :=
  items.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``ectx_item) x acc)
    (Kout?.getD nilEctx)

/-- Rocq: `rel_reshape_cont_l`/`rel_reshape_cont_r`. Call `tac Kfull e1` on the decompositions
`e ≡ fill Kfull e1` of the LHS (resp. RHS), following the evaluation order, until it succeeds. -/
public meta def relReshape {α} (g : RelGoal) (left : Bool)
    (tac : Lean.Expr → Lean.Expr → ProofModeM α) :
    ProofModeM (Option (α × Lean.Expr × Lean.Expr)) := do
  let (Kout?, e0) ← splitThreadExpr (g.side left)
  let some (a, items, e1) ← reshapeExpr e0 fun items e1 => tac (mkFullCtx items Kout?) e1
    | return none
  return some (a, mkFullCtx items Kout?, ← instantiateMVars e1)

/-- `fill K e`. -/
public meta def mkFillE (K e : Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``con_prob_lang.fill) K e

/-- A proof of `a = b` by `rfl` (`a` and `b` definitionally equal). -/
public meta def mkRflHint (a b : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

/-- Apply the tactic lemma `c` with the arguments `args` (given by binder names; the remaining
instance-implicit arguments are synthesized). The argument named `cont` (an entailment
`Δ' ⊢ Q'`) becomes the new proof-mode goal with the hypotheses `hyps`. -/
public meta def relApplyLemma {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (c : Name) (args : List (Name × Lean.Expr)) (cont : Name) :
    ProofModeM Lean.Expr := do
  let cinfo ← getConstInfo c
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst c us
  let ty ← inferType f
  let names ← forallTelescope ty fun xs _ => xs.mapM fun x => x.fvarId!.getUserName
  let (mvs, bis, _) ← forallMetaTelescope ty
  -- the given arguments
  for i in [0:mvs.size] do
    let some v := args.lookup names[i]! | continue
    let mv := mvs[i]!
    unless ← isDefEq mv v do
      throwError "{c}: cannot assign argument {names[i]!} :={indentExpr v}\nof type\
        {indentExpr (← inferType v)}\nexpected type\
        {indentExpr (← instantiateMVars (← inferType mv))}"
  -- the instances
  for i in [0:mvs.size] do
    let mv := mvs[i]!
    if bis[i]!.isInstImplicit && !(← mv.mvarId!.isAssigned) then
      let inst ← synthInstance (← instantiateMVars (← inferType mv))
      mv.mvarId!.assign inst
  -- the continuation
  for i in [0:mvs.size] do
    let mv := mvs[i]!
    if names[i]! == cont then
      let contTy ← whnfR (← instantiateMVars (← inferType mv))
      let Q' := contTy.appArg!
      let pf ← addBIGoal hyps (Q' : Q($prop))
      unless ← isDefEq mv pf do throwError "{c}: cannot build the continuation"
  instantiateMVars (mkAppN f mvs)

/-- Simplify a side `e ≡ fill Kout e0` (Rocq: `pm_prettify; iSimpl`): returns the new side and a
proof of the equation. -/
public meta def relSimpSide (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (Kout?, e0) ← splitThreadExpr e
  let (e0s, pfeq?) ← gwpExprSimp e0
  let e' := mkThreadExpr Kout? e0s
  let heTy ← mkEq e e'
  match pfeq? with
  | none => return (e', ← mkExpectedTypeHint (← mkEqRefl e) heTy)
  | some pfeq =>
    let pf ← match Kout? with
      | none => pure pfeq
      | some K => mkCongrArg (mkApp (mkConst ``con_prob_lang.fill) K) pfeq
    return (e', ← mkExpectedTypeHint pf heTy)

/-- Rocq: `rel_finish`. Simplify both sides of the goal. -/
elab "rel_finish" : tactic =>
  runTacticRel `rel_finish fun mvar g => do
    let (e', he) ← relSimpSide g.e
    let (t', ht) ← relSimpSide g.t
    mvar.assign (← relApplyLemma g.hyps ``tac_rel_rewrite
      [(`Δ, g.ehyps), (`e, g.e), (`e', e'), (`t, g.t), (`t', t'), (`A, g.A), (`he, he),
       (`ht, ht)] `h)

/-- The common core of `rel_bind_l`/`rel_bind_r`/`rel_bind_ctx_l`/`rel_bind_ctx_r`: rewrite the
side to `fill Kfull e1` at the first decomposition accepted by `accept`. -/
public meta def relBindCore (tacName : Name) (left : Bool)
    (accept : Lean.Expr → Lean.Expr → ProofModeM Unit) : TacticM Unit :=
  runTacticRel tacName fun mvar g => do
    let some ((), Kfull, e1) ← relReshape g left accept
      | throwError "{tacName}: cannot find the subexpression in {g.side left}"
    let side := g.side left
    let he ← mkRflHint side (mkFillE Kfull e1)
    let (lem, arg) := if left then (``tac_rel_bind_l, `e') else (``tac_rel_bind_r, `t')
    mvar.assign (← relApplyLemma g.hyps lem
      [(arg, e1), (`K, Kfull), (`Δ, g.ehyps), (`e, g.e), (`t, g.t), (`A, g.A), (`he, he)] `h)

/-- Rocq: `rel_bind_l efoc`. Bind the first subexpression (following the evaluation order) of
the LHS that unifies with `efoc`: the LHS becomes `fill K efoc`. -/
elab "rel_bind_l " f:term:max : tactic => do
  let focus ← elabFocus f
  relBindCore `rel_bind_l true fun _ e1 => do guard (← isDefEq e1 focus)

/-- Rocq: `rel_bind_r efoc`. -/
elab "rel_bind_r " f:term:max : tactic => do
  let focus ← elabFocus f
  relBindCore `rel_bind_r false fun _ e1 => do guard (← isDefEq e1 focus)

/-- Elaborate an evaluation context (a term of type `List ectx_item`, possibly with holes). -/
public meta def elabCtx (K : Syntax) : TacticM Lean.Expr := withMainContext do
  Tactic.elabTermEnsuringType K (some (mkApp (mkConst ``List [0]) (mkConst ``ectx_item)))
    (mayPostpone := true)

/-- Rocq: `rel_bind_ctx_l K`. Rewrite the LHS to `fill K e'`. -/
elab "rel_bind_ctx_l " K:term:max : tactic => do
  let K ← elabCtx K
  relBindCore `rel_bind_ctx_l true fun Kfull _ => do guard (← isDefEq Kfull K)

/-- Rocq: `rel_bind_ctx_r K`. -/
elab "rel_bind_ctx_r " K:term:max : tactic => do
  let K ← elabCtx K
  relBindCore `rel_bind_ctx_r false fun Kfull _ => do guard (← isDefEq Kfull K)

/-- Rewrite the side of the main goal to its `i`-th decomposition `fill Kfull e1` (in the order
of `reshapeExpr`, starting with `0`); fails if there is none. -/
public meta def relBindNth (left : Bool) (i : Nat) : TacticM Unit := do
  let cnt ← IO.mkRef 0
  relBindCore `rel_apply left fun _ _ => do
    let c ← cnt.get
    cnt.set (c + 1)
    guard (c == i)

/-- Try `k` on each decomposition of the side of the goal (Rocq: `rel_reshape_cont_l tac` with
`tac := rel_bind_ctx_l K; k`), backtracking on failures. -/
public meta partial def relTryBindsFrom (tacName : Name) (left : Bool) (k : TacticM Unit)
    (i : Nat) : TacticM Unit := do
  let s ← saveState
  try relBindNth left i
  catch _ =>
    s.restore
    throwError "{tacName}: cannot apply the lemma"
  try k
  catch ex =>
    s.restore
    try relTryBindsFrom tacName left k (i + 1)
    catch _ => throw ex

/-- `relTryBindsFrom`, trying `k` on the goal as it is first (Lean's `iapply` does not unfold
`fill [] e` to `e`, unlike Rocq's unification). -/
public meta def relTryBinds (tacName : Name) (left : Bool) (k : TacticM Unit) : TacticM Unit := do
  let s ← saveState
  try k
  catch _ =>
    s.restore
    relTryBindsFrom tacName left k 0

/-- The core of `rel_apply_l lem`. -/
elab "rel_apply_l_core " pmt:pmTerm : tactic =>
  do relTryBinds `rel_apply_l true (evalTactic (← `(tactic| iapply $pmt)))

/-- The core of `rel_apply_r lem`. -/
elab "rel_apply_r_core " pmt:pmTerm : tactic =>
  do relTryBinds `rel_apply_r false (evalTactic (← `(tactic| iapply $pmt)))

/-- The core of `rel_apply lem`. -/
elab "rel_apply_core " pmt:pmTerm : tactic =>
  relTryBinds `rel_apply true do
    relTryBinds `rel_apply false do evalTactic (← `(tactic| iapply $pmt))

/-- Rocq: `rel_apply_l lem`. Apply `lem` (an iris-lean proof-mode term, as for `iapply`) at the
first decomposition `fill K e` of the LHS for which `iapply` succeeds. -/
macro "rel_apply_l " pmt:pmTerm : tactic =>
  `(tactic| focus (rel_apply_l_core $pmt; all_goals try rel_finish))

/-- Rocq: `rel_apply_r lem`. -/
macro "rel_apply_r " pmt:pmTerm : tactic =>
  `(tactic| focus (rel_apply_r_core $pmt; all_goals try rel_finish))

/-- Rocq: `rel_apply lem`. Apply `lem` at decompositions of both sides. -/
macro "rel_apply " pmt:pmTerm : tactic =>
  `(tactic| focus (rel_apply_core $pmt; all_goals try rel_finish))

/-- Rocq: `rel_values` (the `iApply refines_ret` part). -/
elab "rel_values_core" : tactic =>
  runTacticRel `rel_values fun mvar g => do
    let (e', he) ← relSimpSide g.e
    let (t', ht) ← relSimpSide g.t
    let some v1 := isValExpr? e' | throwError "rel_values: the LHS {e'} is not a value"
    let some v2 := isValExpr? t' | throwError "rel_values: the RHS {t'} is not a value"
    let pf ← relApplyLemma g.hyps ``tac_rel_values
      [(`Δ, g.ehyps), (`v1, v1), (`v2, v2), (`A, g.A)] `h
    mvar.assign (← mkAppNamed ``tac_rel_rewrite
      [(`Δ, g.ehyps), (`e, g.e), (`e', mkValE v1), (`t, g.t), (`t', mkValE v2), (`A, g.A),
       (`he, he), (`ht, ht), (`h, pf)])

/-- Rocq: `rel_values`. Leaves the goal `|={⊤}=> A v1 v2`, unless it can be closed by
`imodintro; iassumption` (Rocq: `eauto with iFrame`). -/
macro "rel_values" : tactic =>
  `(tactic| focus (rel_values_core; try (imodintro; iassumption; done)))

/-! ### Pure reductions -/

/-- A side condition `φ`: solved now with `wp_solve_side` if `failOnUnsolved`, and otherwise
returned as a pending metavariable (to be added as a goal after the main goal, see
`relSolvePending`). -/
public meta def relSideMVar (φ : Lean.Expr) (failOnUnsolved : Bool) :
    ProofModeM (Lean.Expr × Option Lean.Expr) := do
  if failOnUnsolved then return (← gwpSolveSide φ true, none)
  let pf ← mkFreshExprSyntheticOpaqueMVar φ
  return (pf, some pf)

/-- Try to solve a pending side condition with `wp_solve_side`; otherwise add it as a goal. -/
public meta def relSolvePending (pf? : Option Lean.Expr) : ProofModeM Unit := do
  let some pf := pf? | return
  let s ← saveState
  let solved ← observing? (evalTacticAt (← `(tactic| wp_solve_side)) pf.mvarId!)
  match solved with
  | some [] => return
  | _ =>
    s.restore
    addMVarGoal pf.mvarId!

/-- Rocq: `rel_pure_l ef in Kf` (with the pure-step search `find`). -/
public meta def relPureCore (tacName : Name) (left : Bool) (focus Kf : Option Syntax)
    (failOnUnsolved : Bool) (find : Lean.Expr → ProofModeM PureStepRes) : TacticM Unit := do
  let focusE ← focus.mapM elabFocus
  let KfE ← Kf.mapM elabCtx
  runTacticRel tacName fun mvar g => do
    let some (res, Kfull, e1) ← relReshape g left fun Kfull e1 => do
        if let some kf := KfE then guard (← isDefEq Kfull kf)
        if let some f := focusE then guard (← isDefEq e1 f)
        find e1
      | throwError "{tacName}: cannot find the reduct"
    let (hϕ, pending) ← match res.hφ with
      | some hφ => pure (hφ, none)
      | none => relSideMVar res.φ failOnUnsolved
    let side := g.side left
    let hfill ← mkRflHint side (mkFillE Kfull e1)
    let eres := mkFillE Kfull res.e2
    let hres ← mkEqRefl eres
    if left then
      let ⟨ehyps', hyps', pfLater⟩ ← gwpStripLaters g.hyps res.n
      let hm ← mkAppOptM ``Or.inl #[← mkEq res.n res.n, ← mkEq res.n (mkNatLit 0),
        ← mkEqRefl res.n]
      mvar.assign (← relApplyLemma hyps' ``tac_rel_pure_l
        [(`K, Kfull), (`e1, e1), (`Δ, g.ehyps), (`Δ', ehyps'), (`e, g.e), (`e2, res.e2),
         (`eres, eres), (`ϕ, res.φ), (`n, res.n), (`m, res.n), (`t, g.t), (`A, g.A),
         (`hfill, hfill), (`hpure, res.inst), (`hϕ, hϕ), (`hm, hm), (`hlater, pfLater),
         (`hres, hres)] `hcont)
      relSolvePending pending
    else
      mvar.assign (← relApplyLemma g.hyps ``tac_rel_pure_r
        [(`K, Kfull), (`e1, e1), (`Δ, g.ehyps), (`e, g.t), (`e2, res.e2), (`eres, eres),
         (`ϕ, res.φ), (`n, res.n), (`t, g.e), (`A, g.A), (`hfill, hfill), (`hpure, res.inst),
         (`hϕ, hϕ), (`hres, hres)] `hcont)
    relSolvePending pending

/-- Rocq: `rel_pure_l ef in Kf`, `rel_pure_l ef` and `rel_pure_l`. Take a pure step on the LHS
at the first redex (following the evaluation order) that unifies with `ef` and whose
evaluation context unifies with `Kf`; the side condition is left as a goal if it is not solved
automatically. -/
syntax "rel_pure_l" (ppSpace colGt term:max)? (" in " term:max)? : tactic

/-- Rocq: `rel_pure_r ef in Kf`, `rel_pure_r ef` and `rel_pure_r`. -/
syntax "rel_pure_r" (ppSpace colGt term:max)? (" in " term:max)? : tactic

elab_rules : tactic
  | `(tactic| rel_pure_l $[$f]? $[in $K]?) => do
    relPureCore `rel_pure_l true f K false findAnyPureExec
    evalTactic (← `(tactic| rel_finish))
  | `(tactic| rel_pure_r $[$f]? $[in $K]?) => do
    relPureCore `rel_pure_r false f K false findAnyPureExec
    evalTactic (← `(tactic| rel_finish))

/-- `rel_pure_l` failing on unsolved side conditions (Rocq: `rel_pure_l _ in _; []`). -/
elab "rel_pure_l_strict" : tactic => do
  relPureCore `rel_pure_l true none none true findAnyPureExec
  evalTactic (← `(tactic| rel_finish))

/-- `rel_pure_r` failing on unsolved side conditions. -/
elab "rel_pure_r_strict" : tactic => do
  relPureCore `rel_pure_r false none none true findAnyPureExec
  evalTactic (← `(tactic| rel_finish))

/-- Rocq: `rel_pures_l`. -/
macro "rel_pures_l" : tactic => `(tactic| repeat rel_pure_l_strict)

/-- Rocq: `rel_pures_r`. -/
macro "rel_pures_r" : tactic => `(tactic| repeat rel_pure_r_strict)

/-- Rocq: `rel_rec_l`. Beta-reduce the first application of a (possibly hidden behind a
definition) recursive function to a value on the LHS. -/
elab "rel_rec_l" : tactic => do
  relPureCore `rel_rec_l true none none false findRecPureExec
  evalTactic (← `(tactic| rel_finish))

/-- Rocq: `rel_rec_r`. -/
elab "rel_rec_r" : tactic => do
  relPureCore `rel_rec_r false none none false findRecPureExec
  evalTactic (← `(tactic| rel_finish))

/-- Rocq: `rel_arrow_val`. -/
macro "rel_arrow_val" : tactic =>
  `(tactic| (rel_pures_l; rel_pures_r; iapply refines_arrow_val; imodintro))

/-- Rocq: `rel_arrow`. -/
macro "rel_arrow" : tactic =>
  `(tactic| (rel_pures_l; rel_pures_r; iapply refines_arrow; imodintro))

/-! ### Allocation -/

/-- Find a redex matched by `m` on a side, whose decomposition matches the focus `ef` and the
context `Kf`. -/
public meta def relFindRedex {α} (tacName : Name) (what : String) (g : RelGoal) (left : Bool)
    (focus Kf : Option Lean.Expr) (m : Lean.Expr → Option α) :
    ProofModeM (α × Lean.Expr × Lean.Expr) := do
  let some r ← relReshape g left fun Kfull e1 => do
      if let some kf := Kf then guard (← isDefEq Kfull kf)
      if let some f := focus then guard (← isDefEq e1 f)
      let some r := m e1.consumeMData | failure
      return r
    | throwError "{tacName}: cannot find '{what}'"
  return r

/-- The core of `rel_alloc_l`/`rel_alloc_r`/`rel_alloctape_l`/`rel_alloctape_r`: leaves the
goal `∀ l, P l -∗ REL ..`. -/
public meta def relAllocCore (tacName : Name) (left tape : Bool) (focus Kf : Option Syntax) :
    TacticM Unit := do
  let focusE ← focus.mapM elabFocus
  let KfE ← Kf.mapM elabCtx
  runTacticRel tacName fun mvar g => do
    let side := g.side left
    if !tape then
      let (v, Kfull, e1) ← relFindRedex tacName "Alloc" g left focusE KfE matchAlloc?
      let hfill ← mkRflHint side (mkFillE Kfull e1)
      if left then
        let ⟨ehyps', hyps', pfLater⟩ ← gwpStripLaters g.hyps (mkNatLit 1)
        mvar.assign (← relApplyLemma hyps' ``tac_rel_alloc_l_simpl
          [(`K, Kfull), (`Δ1, g.ehyps), (`Δ2, ehyps'), (`e, g.e), (`t, g.t), (`e', mkValE v),
           (`v', v), (`A, g.A), (`hfill, hfill), (`hlater, pfLater)] `hcont)
      else
        mvar.assign (← relApplyLemma g.hyps ``tac_rel_alloc_r
          [(`K', Kfull), (`Δ, g.ehyps), (`t', mkValE v), (`v', v), (`e, g.e), (`t, g.t),
           (`A, g.A), (`hfill, hfill)] `hcont)
    else
      let (z, Kfull, e1) ← relFindRedex tacName "AllocTape" g left focusE KfE matchAllocTape?
      let hfill ← mkRflHint side (mkFillE Kfull e1)
      let N ← gwpValSimpDefEq (← mkAppM ``Int.toNat #[z])
      let hN ← mkFreshExprSyntheticOpaqueMVar (← mkEq N (← mkAppM ``Int.toNat #[z]))
      if left then
        let ⟨ehyps', hyps', pfLater⟩ ← gwpStripLaters g.hyps (mkNatLit 1)
        mvar.assign (← relApplyLemma hyps' ``tac_rel_alloctape_l_simpl
          [(`K, Kfull), (`Δ1, g.ehyps), (`Δ2, ehyps'), (`e, g.e), (`N, N), (`z, z), (`t, g.t),
           (`A, g.A), (`hN, hN), (`hfill, hfill), (`hlater, pfLater)] `hcont)
        relSolvePending (some hN)
      else
        mvar.assign (← relApplyLemma g.hyps ``tac_rel_alloctape_r
          [(`K', Kfull), (`Δ, g.ehyps), (`e, g.e), (`N, N), (`z, z), (`t, g.t), (`A, g.A),
           (`hN, hN), (`hfill, hfill)] `hcont)
        relSolvePending (some hN)

/-- The core of `rel_alloc_l l as H at ef in Kf` (Rocq: `tac_rel_alloc_l_simpl`). -/
elab "rel_alloc_l_core" f:(" at " term:max)? K:(" in " term:max)? : tactic =>
  relAllocCore `rel_alloc_l true false (f.map (·.raw[1])) (K.map (·.raw[1]))

/-- The core of `rel_alloc_r l as H at ef in Kf` (Rocq: `tac_rel_alloc_r`). -/
elab "rel_alloc_r_core" f:(" at " term:max)? K:(" in " term:max)? : tactic =>
  relAllocCore `rel_alloc_r false false (f.map (·.raw[1])) (K.map (·.raw[1]))

/-- The core of `rel_alloctape_l α as H at ef in Kf` (Rocq: `tac_rel_alloctape_l_simpl`). -/
elab "rel_alloctape_l_core" f:(" at " term:max)? K:(" in " term:max)? : tactic =>
  relAllocCore `rel_alloctape_l true true (f.map (·.raw[1])) (K.map (·.raw[1]))

/-- The core of `rel_alloctape_r α as H at ef in Kf` (Rocq: `tac_rel_alloctape_r`). -/
elab "rel_alloctape_r_core" f:(" at " term:max)? K:(" in " term:max)? : tactic =>
  relAllocCore `rel_alloctape_r false true (f.map (·.raw[1])) (K.map (·.raw[1]))

/-- Rocq: `rel_alloc_l l as "H" at ef in Kf` and `rel_alloc_l l as "H"` (the latter first takes
all pure steps on the LHS). -/
syntax "rel_alloc_l " ident " as " introPat (" at " term:max " in " term:max)? : tactic

/-- Rocq: `rel_alloc_r l as "H" at ef in Kf` and `rel_alloc_r l as "H"`. -/
syntax "rel_alloc_r " ident " as " introPat (" at " term:max " in " term:max)? : tactic

/-- Rocq: `rel_alloctape_l α as "H" at ef in Kf` and `rel_alloctape_l α as "H"`. -/
syntax "rel_alloctape_l " ident " as " introPat (" at " term:max " in " term:max)? : tactic

/-- Rocq: `rel_alloctape_r α as "H" at ef in Kf` and `rel_alloctape_r α as "H"`. -/
syntax "rel_alloctape_r " ident " as " introPat (" at " term:max " in " term:max)? : tactic

macro_rules
  | `(tactic| rel_alloc_l $l:ident as $pat:introPat at $f in $K) =>
    `(tactic| focus (rel_alloc_l_core at $f in $K; iintro %$l:ident $pat:introPat; rel_finish))
  | `(tactic| rel_alloc_l $l:ident as $pat:introPat) =>
    `(tactic| focus (rel_pures_l; rel_alloc_l_core; iintro %$l:ident $pat:introPat; rel_finish))
  | `(tactic| rel_alloc_r $l:ident as $pat:introPat at $f in $K) =>
    `(tactic| focus (rel_alloc_r_core at $f in $K; iintro %$l:ident $pat:introPat; rel_finish))
  | `(tactic| rel_alloc_r $l:ident as $pat:introPat) =>
    `(tactic| focus (rel_pures_r; rel_alloc_r_core; iintro %$l:ident $pat:introPat; rel_finish))
  | `(tactic| rel_alloctape_l $l:ident as $pat:introPat at $f in $K) =>
    `(tactic| focus (rel_alloctape_l_core at $f in $K; iintro %$l:ident $pat:introPat; rel_finish))
  | `(tactic| rel_alloctape_l $l:ident as $pat:introPat) =>
    `(tactic| focus (rel_pures_l; rel_alloctape_l_core; iintro %$l:ident $pat:introPat; rel_finish))
  | `(tactic| rel_alloctape_r $l:ident as $pat:introPat at $f in $K) =>
    `(tactic| focus (rel_alloctape_r_core at $f in $K; iintro %$l:ident $pat:introPat; rel_finish))
  | `(tactic| rel_alloctape_r $l:ident as $pat:introPat) =>
    `(tactic| focus (rel_pures_r; rel_alloctape_r_core; iintro %$l:ident $pat:introPat; rel_finish))

end meta_tactics

end Foxtrot.BinaryRel

/-! ## Tests -/

namespace Foxtrot.BinaryRel

section tests

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Pure steps on both sides, then `rel_values`. -/
example : ⊢ REL cpl(#1 + #1) << cpl(if #true then #2 else #3) : lrel_int (GF := GF) := by
  rel_pures_l
  rel_pures_r
  rel_values
  imodintro
  dsimp only [lrel_int]
  iexists 2
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Focused pure steps and `rel_rec_l`/`rel_rec_r`. -/
example : ⊢ REL cpl((λ x, x + #1) #1) << cpl(let y := #1 + #1 in y) :
    lrel_int (GF := GF) := by
  rel_pure_l (expr.Rec _ _ _)
  rel_rec_l
  rel_pure_r (BinOp _ _ _)
  rel_pure_r (expr.Rec _ _ _)
  rel_rec_r
  rel_pures_l
  rel_values
  imodintro
  dsimp only [lrel_int]
  iexists 2
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Pure steps under an opaque evaluation context, and `rel_bind_l`. -/
example (K : List ectx_item) (t : expr) (A : lrel GF) :
    (REL fill K cpl(#3) << t : A) ⊢ REL fill K cpl(fst((#1 + #2, #3))) << t : A := by
  iintro H
  rel_bind_l (Pair _ _)
  rel_pure_l
  rel_pure_l (Pair _ _)
  rel_pure_l in K
  iexact H

/-- Allocations on both sides. -/
example : ⊢ REL cpl(ref(#1); #()) << cpl(ref(#2); #()) : lrel_unit (GF := GF) := by
  rel_alloc_l l as Hl
  rel_alloc_r l' as Hl'
  rel_pures_l
  rel_pures_r
  rel_values
  imodintro
  dsimp only [lrel_unit]
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Tape allocations on both sides. -/
example : ⊢ REL cpl(alloc(#1); #()) << cpl(alloc(#1); #()) : lrel_unit (GF := GF) := by
  rel_alloctape_l α as Hα
  rel_alloctape_r β as Hβ
  rel_pures_l
  rel_pures_r
  rel_values
  imodintro
  dsimp only [lrel_unit]
  ipureintro
  exact ⟨rfl, rfl⟩

/-- `rel_apply_r` with a RHS rule. -/
example (l : Loc) :
    ⊢ l ↦ₛ LitV (LitInt 1) -∗
      REL cpl(#1) << cpl(#(); xchg(#l, #2)) : lrel_int (GF := GF) := by
  iintro Hl
  rel_pures_r
  rel_apply_r refines_xchg_r $$ Hl
  iintro Hl
  rel_values
  imodintro
  dsimp only [lrel_int]
  iexists 1
  ipureintro
  exact ⟨rfl, rfl⟩

/-- `rel_arrow_val`. -/
example : ⊢ REL cpl(λ x, x) << cpl(λ x, x) :
    lrel_arr (GF := GF) lrel_int lrel_int := by
  rel_arrow_val
  iintro %v1 %v2 #Hv
  rel_rec_l
  rel_rec_r
  rel_values

/-- `rel_apply_l` with a LHS rule. -/
example (l : Loc) :
    ⊢ l ↦ LitV (LitInt 1) -∗
      REL cpl(#(); faa(#l, #2)) << cpl(#1) : lrel_int (GF := GF) := by
  iintro Hl
  rel_pures_l
  rel_apply_l refines_faa_l
  iexists 1
  isplitl [Hl]
  · inext
    iexact Hl
  · inext
    iintro -
    rel_values
    imodintro
    dsimp only [lrel_int]
    iexists 1
    ipureintro
    exact ⟨rfl, rfl⟩

/-- `rel_apply` on both sides, `rel_bind_ctx_l` and `rel_alloc_l .. at .. in ..`. -/
example (e e' : expr) :
    (REL e << e' : lrel_unit (GF := GF)) ⊢
      REL cpl(fork(&e)) << cpl(fork(&e')) : lrel_unit (GF := GF) := by
  iintro H
  rel_apply refines_fork
  iexact H

example (K : List ectx_item) (t : expr) (A : lrel GF) :
    (∀ l : Loc, l ↦ LitV (LitInt 1) -∗ REL fill K (Val (LitV (LitLoc l))) << t : A) ⊢
      REL fill K cpl(ref(#1)) << t : A := by
  iintro H
  rel_bind_ctx_l K
  rel_alloc_l l as Hl at (AllocN _ _) in K
  iapply H $$ Hl

end tests

end Foxtrot.BinaryRel
