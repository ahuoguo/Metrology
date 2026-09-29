module

public import Metrology.ConProbLang.Typing.ContextualRefinement

/-!
# A simple syntax-directed type checker

Ported from clutch/theories/con_prob_lang/typing/tychk.v

A simple-minded syntax-directed type checker: it proves `typed Γ e τ` (`Γ ⊢ₜ e : τ`),
`val_typed v τ` (`⊢ᵥ v : τ`) and `typed_ctx K Γ τ Γ' τ'` goals by applying the typing
constructors selected by the head symbol of the expression / value / context, instead of
blindly trying all constructors (which can go wrong on the non-syntax-directed ones).
The types in the goal may contain metavariables; they are solved by unification.

## Rocq → Lean mapping
* Ltac `type_expr n` / `type_val n` / `type_ctx` / `tychk` are the tactics `type_expr n`,
  `type_val n`, `type_ctx`, `tychk`, implemented by the mutually recursive meta functions
  `Tychk.typeExpr`, `Tychk.typeVal`, `Tychk.typeCtx` (in `TacticM`, with the depth bound `n`
  decreased at each recursive call exactly as in Rocq; `Val` passes `n` unchanged to
  `type_val`, as in Rocq).
* The case analysis is the Rocq one: `Var` (`Var_typed`, lookup side condition), `Val`
  (`Val_typed` + `type_val`), `BinOp` (`BinOp_typed_int` if `binop_int_res_type op` is `some`,
  `BinOp_typed_bool` if `binop_bool_res_type op` is `some`, `UnboxedEq_typed` for `EqOp`),
  `UnOp` (likewise), `Pair`, `Fst`, `Snd`, `InjL`, `InjR`, `Case`, `If`, `Rec`, `App`,
  `AllocN` (`TAlloc`, Rocq `Alloc`), `Load`, `Store`, `AllocTape`, `Rand` (`TRand`, then
  `TRandU`), `Fork`, `CmpXchg`, `Xchg`, `FAA`. As in Rocq, `TLam_typed`, `TApp_typed`,
  `TFold`, `TUnfold`, `TPack`, `TUnpack` are never tried for expressions.
  Values: `LitUnit`, `TNat` literals (`Nat_val_typed`), `LitInt` (`Int_val_typed`),
  `LitBool`, `PairV`, `InjLV`, `InjRV`, `RecV` (`Rec_val_typed` + `type_expr`).
  Contexts: `[]` (`TPCTX_nil`) and `k :: K` (`TPCTX_cons`, typing `K` first, then choosing a
  constructor of `typed_ctx_item` for `k`; Rocq: `econstructor; last first; [type_ctx | econstructor]`).
* Rocq's side-condition solver `try by eauto` is `Tychk.sideCond`: `rfl` (for
  `binop_int_res_type op = some τ` etc.), the constructors of `UnboxedType`, `omega` (for
  `0 ≤ z`), and, for context lookups `Γ[x]? = some τ`, `Tychk.solveLookup` (which reads the
  type off a context built from `binder_insert` and `∅`, and falls back to
  `simp [lookup_binder_insert]`).

## Deviations
* Failure behaviour: the Rocq tactics never fail and leave the goals they cannot solve (e.g.
  when the depth bound is exhausted or no case applies, they are `idtac`). The Lean tactics are
  *complete-or-fail*: `type_expr n`, `type_val n`, `type_ctx` and `tychk` either close every
  `typed`/`val_typed`/`typed_ctx`/side-condition goal they generate or fail (restoring the
  state). The only goals they may leave are unconstrained type metavariables (e.g. the type
  of an unused variable). `try tychk` recovers the Rocq "best effort" usage.
* Because of that, alternatives are tried with backtracking (Rocq only backtracks between
  `TRand` and `TRandU`): for `BinOp`/`UnOp` all applicable rules are tried in the Rocq order
  (so `BinOp EqOp` falls back from `BinOp_typed_int` to `BinOp_typed_bool` and
  `UnboxedEq_typed`, which is unreachable in the Rocq version), and a `typed_ctx_item`
  constructor is accepted only if its premises can be type-checked.
* Added: when the syntax-directed rule fails on a goal of type `TInt`, `Subsume_int_nat` is
  tried (Rocq's `tychk` never uses it, so e.g. `rand(#N) ≤ #M` could not be checked).
* Added: `App e1 e2` whose function `e1` is a (syntactic) `Rec` expression, i.e. a `let`/`;`,
  checks the argument `e2` first so that the type of the bound variable is known when the body
  is checked. Otherwise `e1` is checked first (as the premise order in Rocq).
* Numeric literals whose expected type is still unknown are given type `TNat` if they are
  non-negative (and `TInt` otherwise); Rocq's `lazymatch` picks `TInt` for them. Together with
  the `Subsume_int_nat` fallback this types more programs (e.g. `ref(#0)` used by `faa`).
  `TNat` literals are typed by `Nat_val_typed` or, when the literal is not syntactically a cast
  `↑n`, by the new lemma `Nat_lit_val_typed` with side condition `0 ≤ z` (by `omega`).
* Added: `⊢ᵥ RecV BAnon BAnon e : TForall τ` is tried with `TLam_val_typed` (the Rocq case
  `(Λ: _) : (∀: _)` is `idtac`, with the rule commented out as a TODO).
* Expressions and values are put in weak-head normal form (default transparency) before the
  case analysis, so that `Let`, `Seq`, `Lam`, `Alloc`, ... and named program definitions are
  seen through.
* `tychk`: Rocq `try type_ctx ; try type_expr 100 ; try type_val 100`; here it dispatches on the
  goal (`typed_ctx`, `typed`, or `val_typed`) with depth 100.
-/

@[expose] public section

namespace ConProbLang

namespace con_prob_lang

/-- A `TNat` literal given as an integer (not in Rocq; used by `type_val` when the literal is
not syntactically of the form `↑n`). -/
theorem Nat_lit_val_typed (z : ℤ) (h : 0 ≤ z) : ⊢ᵥ LitV (LitInt z) : TNat := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  exact val_typed.Nat_val_typed n

namespace Tychk

open Lean Meta Elab Tactic

/-- Try the alternatives in order, restoring the state after each failure. -/
meta def firstB {α : Type} : List (TacticM α) → TacticM α
  | [] => throwError "tychk: no rule applies"
  | [x] => x
  | x :: xs => do
    let s ← saveState
    try x catch _ => s.restore; firstB xs

/-- Run a tactic on a single goal, requiring that it closes it. -/
meta def runTacOn (g : MVarId) (tac : TSyntax `tactic) : TacticM Unit := do
  let gs ← Tactic.run g (evalTactic tac)
  unless gs.isEmpty do throwError "tychk: side condition not solved"

/-- The type of `x` in a typing context built from `binder_insert` and `∅`. -/
meta partial def lookupCtx (Γ : Expr) (x : String) : MetaM (Option Expr) := do
  let Γ ← instantiateMVars Γ
  match Γ.getAppFnArgs with
  | (``binder_insert, #[_, b, v, Γ']) =>
    match (← whnfD b).getAppFnArgs with
    | (``binder.BAnon, _) => lookupCtx Γ' x
    | (``binder.BNamed, #[s]) =>
      match (← whnfD s) with
      | .lit (.strVal s') => if s' == x then return some v else lookupCtx Γ' x
      | _ => throwError "tychk: non-literal binder"
    | _ => throwError "tychk: unknown binder"
  | (``EmptyCollection.emptyCollection, _) => return none
  | _ => throwError "tychk: unsupported context{indentExpr Γ}"

/-- Rocq: `try by eauto` for the lookup side condition `Γ[x]? = some τ` of `Var_typed`. -/
meta def solveLookup (g : MVarId) : TacticM Unit := do
  let tgt ← instantiateMVars (← g.getType)
  let some (_, lhs, rhs) := tgt.eq? | throwError "tychk: not a lookup"
  -- `lhs = Γ[x]?`, `rhs = some τ`
  let args := lhs.getAppArgs
  let some (τ : Expr) := (match rhs.getAppFnArgs with
    | (``Option.some, #[_, τ]) => some τ
    | _ => none) | throwError "tychk: not a lookup"
  firstB
    [ do
        let Γ := args[args.size - 3]!
        let .lit (.strVal x) ← whnfD args[args.size - 2]! | throwError "tychk: variable"
        let some v ← lookupCtx Γ x | throwError "tychk: unbound variable {x}"
        unless ← isDefEq τ v do throwError "tychk: type mismatch for {x}"
        runTacOn g (← `(tactic| simp [lookup_binder_insert]))
    , runTacOn g (← `(tactic| (simp only [lookup_binder_insert]; rfl)))
    , runTacOn g (← `(tactic| rfl)) ]

/-- Rocq: `try by eauto` for the remaining side conditions. -/
meta def sideCond (g : MVarId) : TacticM Unit := do
  let tgt ← instantiateMVars (← g.getType)
  match tgt.getAppFnArgs with
  | (``UnboxedType, _) =>
    firstB ([``UnboxedType.UnboxedTUnit, ``UnboxedType.UnboxedTNat, ``UnboxedType.UnboxedTInt,
      ``UnboxedType.UnboxedTBool, ``UnboxedType.UnboxedTRef].map fun c => do
        let gs ← g.apply (← mkConstWithFreshMVarLevels c)
        unless gs.isEmpty do throwError "tychk")
  | _ => firstB [g.refl, runTacOn g (← `(tactic| omega))]

/-- Is `e` (after instantiation) the constant `c`? -/
meta def isConst (e : Expr) (c : Name) : MetaM Bool := do
  return (← whnfR (← instantiateMVars e)).isConstOf c

/-- Is `e` (after instantiation) an unassigned metavariable? -/
meta def isMVar (e : Expr) : MetaM Bool := do
  return (← instantiateMVars e).isMVar

/-- Does `f a` (with `f : _ → Option type`) compute to `some _`? -/
meta def resIsSome (f : Name) (a : Expr) : MetaM Bool := do
  return (← whnfD (mkApp (mkConst f) a)).isAppOf ``Option.some

mutual

/-- Dispatch a goal on its head symbol. -/
meta partial def solveGoal (n : Nat) (g : MVarId) : TacticM Unit := do
  if ← g.isAssigned then return
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  if tgt.isAppOf ``typed then typeExpr n g
  else if tgt.isAppOf ``val_typed then typeVal n g
  else if tgt.isAppOf ``typed_ctx then typeCtx n g
  else if ← isProp tgt then sideCond g
  else return -- a data goal (a type metavariable): left to unification

/-- Solve the goals produced by a rule: the typing goals first (in order), then the side
conditions. -/
meta partial def solveNew (n : Nat) (gs : List MVarId) : TacticM Unit := do
  for g in gs do
    let tgt ← whnfR (← instantiateMVars (← g.getType))
    if tgt.isAppOf ``typed || tgt.isAppOf ``val_typed || tgt.isAppOf ``typed_ctx then
      solveGoal n g
  for g in gs do
    solveGoal n g

/-- Apply the constant `c` to `g` and solve the new goals with depth `n`. -/
meta partial def byRule (n : Nat) (g : MVarId) (c : Name) : TacticM Unit := do
  let gs ← g.apply (← mkConstWithFreshMVarLevels c)
  solveNew n gs

/-- Rocq: `type_expr n`. -/
meta partial def typeExpr (n : Nat) (g : MVarId) : TacticM Unit := do
  if n == 0 then throwError "tychk: depth bound exhausted"
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let #[_, e, τ] := tgt.getAppArgs | throwError "tychk: not a typing goal"
  let e ← whnfD (← instantiateMVars e)
  let n' := n - 1
  let r := byRule n' g
  let direct : TacticM Unit :=
    match e.getAppFnArgs with
    | (``expr.Var, _) => do
      let gs ← g.apply (mkConst ``typed.Var_typed)
      for g' in gs do
        unless ← g'.isAssigned do solveLookup g'
    | (``expr.Val, _) => do
      let gs ← g.apply (mkConst ``typed.Val_typed)
      solveNew n gs
    | (``expr.BinOp, #[op, _, _]) => do
      let alts := (if ← resIsSome ``binop_int_res_type op then [r ``typed.BinOp_typed_int]
        else []) ++
        (if ← resIsSome ``binop_bool_res_type op then [r ``typed.BinOp_typed_bool] else []) ++
        (if (← whnfD op).isConstOf ``bin_op.EqOp then [r ``typed.UnboxedEq_typed] else [])
      firstB alts
    | (``expr.UnOp, #[op, _]) => do
      let alts := (if ← resIsSome ``unop_int_res_type op then [r ``typed.UnOp_typed_int]
        else []) ++
        (if ← resIsSome ``unop_bool_res_type op then [r ``typed.UnOp_typed_bool] else [])
      firstB alts
    | (``expr.Pair, _) => r ``typed.Pair_typed
    | (``expr.Fst, _) => r ``typed.Fst_typed
    | (``expr.Snd, _) => r ``typed.Snd_typed
    | (``expr.InjL, _) => r ``typed.InjL_typed
    | (``expr.InjR, _) => r ``typed.InjR_typed
    | (``expr.Case, _) => r ``typed.Case_typed
    | (``expr.If, _) => r ``typed.If_typed
    | (``expr.Rec, _) => r ``typed.Rec_typed
    | (``expr.App, #[e1, _]) => do
      let gs ← g.apply (mkConst ``typed.App_typed)
      let letLike := (← whnfR e1).isAppOf ``expr.Rec
      -- `gs = [⊢ e1 : τ1 → τ2, ⊢ e2 : τ1, τ1]`
      solveNew n' (if letLike then gs.reverse else gs)
    | (``expr.AllocN, _) => r ``typed.TAlloc
    | (``expr.Load, _) => r ``typed.TLoad
    | (``expr.Store, _) => r ``typed.TStore
    | (``expr.AllocTape, _) => r ``typed.TAllocTape
    | (``expr.Rand, _) => firstB [r ``typed.TRand, r ``typed.TRandU]
    | (``expr.Fork, _) => r ``typed.Fork_typed
    | (``expr.CmpXchg, _) => r ``typed.CmpXchg_typed
    | (``expr.Xchg, _) => r ``typed.Xchg_typed
    | (``expr.FAA, _) => r ``typed.Faa_typed
    | _ => throwError "tychk: no typing rule for{indentExpr e}"
  if ← isConst τ ``type.TInt then
    firstB [direct, r ``typed.Subsume_int_nat]
  else
    direct

/-- Rocq: `type_val n`. -/
meta partial def typeVal (n : Nat) (g : MVarId) : TacticM Unit := do
  if n == 0 then throwError "tychk: depth bound exhausted"
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let #[v, τ] := tgt.getAppArgs | throwError "tychk: not a value typing goal"
  let v ← whnfD (← instantiateMVars v)
  let n' := n - 1
  let r := byRule n' g
  let natLit : TacticM Unit := firstB [r ``val_typed.Nat_val_typed, r ``Nat_lit_val_typed]
  match v.getAppFnArgs with
  | (``val.LitV, #[l]) =>
    let l ← whnfD l
    match l.getAppFnArgs with
    | (``base_lit.LitUnit, _) => r ``val_typed.Unit_val_typed
    | (``base_lit.LitInt, _) =>
      if ← isConst τ ``type.TNat then natLit
      else if ← isMVar τ then firstB [natLit, r ``val_typed.Int_val_typed]
      else r ``val_typed.Int_val_typed
    | (``base_lit.LitBool, _) => r ``val_typed.Bool_val_typed
    | _ => throwError "tychk: no typing rule for{indentExpr v}"
  | (``val.PairV, _) => r ``val_typed.Pair_val_typed
  | (``val.InjLV, _) => r ``val_typed.InjL_val_typed
  | (``val.InjRV, _) => r ``val_typed.InjR_val_typed
  | (``val.RecV, _) =>
    if (← whnfR (← instantiateMVars τ)).isAppOf ``type.TForall then r ``val_typed.TLam_val_typed
    else r ``val_typed.Rec_val_typed
  | _ => throwError "tychk: no typing rule for{indentExpr v}"

/-- Rocq: `type_ctx`. -/
meta partial def typeCtx (n : Nat) (g : MVarId) : TacticM Unit := do
  if n == 0 then throwError "tychk: depth bound exhausted"
  let tgt ← whnfR (← instantiateMVars (← g.getType))
  let #[K, _, _, _, _] := tgt.getAppArgs | throwError "tychk: not a context typing goal"
  let K ← whnfD (← instantiateMVars K)
  if K.isAppOf ``List.nil then
    let gs ← g.apply (mkConst ``typed_ctx.TPCTX_nil)
    solveNew n gs
  else if K.isAppOf ``List.cons then
    let gs ← g.apply (mkConst ``typed_ctx.TPCTX_cons)
    -- `gs = [typed_ctx_item k .., typed_ctx K .., Γ2, τ2]`: the context `K` first
    let some gK ← gs.findM? fun g' => return (← g'.getType).isAppOf ``typed_ctx
      | throwError "tychk"
    let some gk ← gs.findM? fun g' => return (← g'.getType).isAppOf ``typed_ctx_item
      | throwError "tychk"
    typeCtx (n - 1) gK
    let ctors := (← getConstInfoInduct ``typed_ctx_item).ctors
    firstB (ctors.map fun c => byRule (n - 1) gk c)
  else throwError "tychk: not a context literal{indentExpr K}"

end

/-- Run `tac` on the main goal; the unassigned metavariables of the proof (type
metavariables left by unification) become the new goals. -/
meta def runMain (tac : MVarId → TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let s ← saveState
  try
    tac g
  catch ex =>
    s.restore
    throw ex
  let rest ← getMVarsNoDelayed (← instantiateMVars (.mvar g))
  let rest ← rest.toList.filterM fun m => return !(← m.isAssigned)
  replaceMainGoal rest

end Tychk

open Lean Elab Tactic in
/-- Rocq: `type_expr n`. Proves a goal `Γ ⊢ₜ e : τ` syntax-directedly, with depth bound `n`. -/
elab "type_expr " n:num : tactic => Tychk.runMain (Tychk.typeExpr n.getNat)

open Lean Elab Tactic in
/-- Rocq: `type_val n`. Proves a goal `⊢ᵥ v : τ` syntax-directedly, with depth bound `n`. -/
elab "type_val " n:num : tactic => Tychk.runMain (Tychk.typeVal n.getNat)

open Lean Elab Tactic in
/-- Rocq: `type_ctx`. Proves a goal `typed_ctx K Γ τ Γ' τ'` for a list literal `K`. -/
elab "type_ctx" : tactic => Tychk.runMain (Tychk.typeCtx 100)

open Lean Elab Tactic in
/-- Rocq: `tychk`. Proves a `typed_ctx`, `typed` or `val_typed` goal (depth bound 100). -/
elab "tychk" : tactic => Tychk.runMain (Tychk.solveGoal 100)

end con_prob_lang

end ConProbLang

/-! ## Tests

Closed programs of the Foxtrot examples and libraries (restated here, since
`Metrology.ConProbLang` does not depend on `Metrology.Foxtrot`), type-checked by `tychk`. -/

namespace ConProbLang.con_prob_lang.TychkTests

/-- `Foxtrot.Lib.Min.min_prog` (clutch/theories/foxtrot/lib/min.v). -/
def min_prog : val := cpl_val(
  λ x y,
    if x < y then x else y)

/-- `Foxtrot.Lib.Conversion.int_to_bool` (clutch/theories/foxtrot/lib/conversion.v). -/
def int_to_bool : val := cpl_val(
  λ z,
    if z = #0 then #false
    else #true)

/-- `flipL` of clutch/theories/foxtrot/examples/von_neumann.v. -/
def flipL : val := cpl_val(λ "e", &int_to_bool (rand("e") #((1 : ℕ))))

/-- `von_neumann_prog` of clutch/theories/foxtrot/examples/von_neumann.v. -/
def von_neumann_prog (N : ℕ) : val := cpl_val(
  λ "ad",
    let "l" := ref(#0) in
    fork("ad" "l");
    (rec "f" "_" :=
       let "bias" := &min_prog (!"l") #N in
       let "x" := (rand(#((N + 1 : ℕ)))) ≤ "bias" in
       let "y" := (rand(#((N + 1 : ℕ)))) ≤ "bias" in
       if "x" = "y" then "f" #() else "x"))

/-- `rand_prog'` of clutch/theories/foxtrot/examples/von_neumann.v. -/
def vn_rand_prog' : val := cpl_val(
  λ "_" "_", let "x" := alloc(#((1 : ℕ))) in &flipL "x")

/-- `rejection_sampler_prog` of clutch/theories/foxtrot/examples/rejection_samplers.v. -/
def rejection_sampler_prog (N M : ℕ) : val := cpl_val(
  rec "f" "_" :=
    let "x" := rand(#N) in
    if ("x" ≤ #M) then "x"
    else "f" #())

/-- `rand_prog'` of clutch/theories/foxtrot/examples/rejection_samplers.v. -/
def rs_rand_prog' (M : ℕ) : val := cpl_val(
  λ "_", let "x" := alloc(#M) in rand("x") #M)

/-- `rand_prog` of clutch/theories/foxtrot/examples/batch_sampling.v. -/
def batch_rand_prog (N M : ℕ) : val := cpl_val(λ "_", rand(#(((N + 1) * (M + 1) - 1 : ℕ))))

example : ⊢ᵥ min_prog : TArrow TInt (TArrow TInt TInt) := by tychk

example : ∅ ⊢ₜ Val int_to_bool : TArrow TInt TBool := by tychk

example : ∅ ⊢ₜ Val flipL : TArrow TTape TBool := by tychk

example (N : ℕ) :
    ∅ ⊢ₜ Val (von_neumann_prog N) : TArrow (TArrow (TRef TNat) TUnit) (TArrow TUnit TBool) := by
  tychk

example : ∅ ⊢ₜ Val vn_rand_prog' : TArrow (TArrow (TRef TNat) TUnit) (TArrow TUnit TBool) := by
  tychk

example (N M : ℕ) : ⊢ᵥ rejection_sampler_prog N M : TArrow TUnit TNat := by type_val 100

example (M : ℕ) : ∅ ⊢ₜ Val (rs_rand_prog' M) : TArrow TUnit TNat := by type_expr 100

example (N M : ℕ) : ∅ ⊢ₜ Val (batch_rand_prog N M) : TArrow TUnit TNat := by tychk

/-- The type can be inferred. -/
example : ∃ τ, ∅ ⊢ₜ cpl(&min_prog #3 #(-4)) : τ := ⟨_, by tychk⟩

/-- A `Store`/`Load` program with a subsumption `TNat ≤ TInt` and a boolean equality. -/
example : ∅ ⊢ₜ cpl(let "r" := ref(#1) in "r" ← #2; (!"r" - #3) = #(-1)) : TBool := by tychk

/-- Ill-typed programs are rejected. -/
example : True := by
  fail_if_success (have : ∅ ⊢ₜ cpl(#true + #1) : TInt := by tychk)
  fail_if_success (have : ∅ ⊢ₜ cpl(λ "x", "y") : TArrow TInt TInt := by tychk)
  trivial

/-- Contexts (Rocq: `type_ctx`): `fst ((min_prog [·]) (y + 1), #())` with `y : TInt`. -/
example : typed_ctx
    [ctx_item.CTX_Fst, ctx_item.CTX_PairL (Val (LitV LitUnit)),
      ctx_item.CTX_AppR (Val min_prog), ctx_item.CTX_BinOpL PlusOp cpl(#1)]
    (binder_insert (BNamed "y") TInt ∅) TInt
    (binder_insert (BNamed "y") TInt ∅) (TArrow TInt TInt) := by
  type_ctx

/-- A context under a binder: `λ "x", [·] "x"` (hole of type `TArrow TNat TBool` under
`"x" : TNat`). -/
example : typed_ctx [ctx_item.CTX_Rec BAnon (BNamed "x"), ctx_item.CTX_AppL (Var "x")]
    (binder_insert BAnon (TArrow TNat TBool) (binder_insert (BNamed "x") TNat ∅))
    (TArrow TNat TBool) ∅ (TArrow TNat TBool) := by
  tychk

end ConProbLang.con_prob_lang.TychkTests
