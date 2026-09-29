module

public import Metrology.ConProbLang.Notation

/-!
# Tactics for `con_prob_lang`

Ported from clutch/theories/con_prob_lang/tactics.v

## Rocq → Lean mapping
* `reshape_expr e tac` (Ltac): the meta-level function `reshapeExpr` (Rocq's `go`, trying the
  outermost decomposition first, as iris-lean's `findECtx`) together with the tactic
  `reshape_expr e as K e' => tac`. The latter runs `tac` with the identifiers `K` and `e'`
  replaced by the evaluation context (a `List ectx_item` literal) and the subexpression of each
  decomposition `e = fill K e'`, from the outermost one (`K = []`) inwards, until `tac`
  succeeds. The equation `fill K e' = e` always holds by `rfl`. Also provided (as in
  iris-lean's `HeapLang/Tactic.lean`): `extractEctxItem`, `extractAllEctxItems`,
  `fillItemMeta`, `fillMeta`, `findECtxRev` (innermost decomposition first) and `quoteList`.
* `head_step_support_eq`, `head_step_support_eq_1`: lemmas of the same names.
* `Hint Extern ... : head_step` (the `head_step` hint database for `head_reducible` and
  `head_step _ _ _ > 0`): the tactics `solve_head_step_rel` / `solve_head_step` / `solve_red`
  of `Metrology.ConProbLang.Lang`.
* `Hint Extern 2 (head_reducible _ _) => ... : typeclass_instances`: omitted; `head_reducible` is
  a `def` (not a class) in Lean. Use `solve_red`.
* `solve_step`: the tactic `solve_step` (goals `prim_step e σ ρ = 1`, `head_step e σ ρ = 1`,
  `0 < head_step e σ ρ`). Rocq's `simplify_map_eq` is replaced by `simp`.
* `solve_red`: defined in `Metrology.ConProbLang.Lang` (where it is used first), restricted to its
  non-Iris cases; the Iris proof-mode cases (`envs_entails _ (⌜_⌝ ∗ _)` and
  `envs_entails _ (_ ∗ ⌜_⌝)`) are added by `Metrology.ConProbLang.SolveRedIris` (extra
  `macro_rules` for `solve_red`, needing `Iris.ProofMode`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang
namespace con_prob_lang

/-- Rocq: `head_step_support_eq`. -/
theorem head_step_support_eq (e1 e2 : expr) (σ1 σ2 : state) (efs : List expr) (r : ℝ≥0∞)
    (hr : 0 < r) (h : head_step e1 σ1 (e2, σ2, efs) = r) : head_step_rel e1 σ1 e2 σ2 efs := by
  subst h
  exact (head_step_support_equiv_rel _ _ _ _ _).1 hr

/-- Rocq: `head_step_support_eq_1`. -/
theorem head_step_support_eq_1 (e1 e2 : expr) (σ1 σ2 : state) (efs : List expr)
    (h : head_step e1 σ1 (e2, σ2, efs) = 1) : head_step_rel e1 σ1 e2 σ2 efs :=
  head_step_support_eq e1 e2 σ1 σ2 efs 1 one_pos h

/-- Rocq: `solve_step`. Proves goals of the shape
* `prim_step e σ ρ = 1` (via `head_prim_step_eq`, which requires `solve_red` to prove
  head-reducibility, then `simp` and `solve_distr`),
* `head_step e σ ρ = 1` (via `simp` and `solve_distr`),
* `0 < head_step e σ ρ` (via `solve_head_step`). -/
syntax "solve_step" : tactic
macro_rules
  | `(tactic| solve_step) => `(tactic| first
    | solve_head_step
    | (change con_prob_lang.head_step _ _ _ = 1
       simp only [head_step] <;> (try simp) <;> solve_distr)
    | (rw [conEctxLanguage.head_prim_step_pmf_eq (Λ := con_prob_ectx_lang) _ _ _ (by solve_red),
         con_prob_ectx_lang_head_step]
       simp only [head_step] <;> (try simp) <;> solve_distr))

/-! ## `reshape_expr` -/

section reshape

open Lean Meta Elab Tactic

/-- Is `e` syntactically a value `Val v`? Returns `v`. -/
meta def isValExpr? (e : Expr) : Option Expr :=
  match e.consumeMData.getAppFnArgs with
  | (``expr.Val, #[v]) => some v
  | (``con_prob_lang.of_val, #[v]) => some v
  | _ => none

/-- One step of Rocq's `go` in `reshape_expr`: decompose `e = fill_item Ki e'`, following the
right-to-left evaluation order (the same cases, in the same order, as Rocq). -/
meta def extractEctxItem (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let c (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) args
  match e.getAppFnArgs with
  | (``expr.App, #[e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.AppLCtx #[v], e1)
    | none => some (c ``ectx_item.AppRCtx #[e1], e2)
  | (``expr.UnOp, #[op, e1]) => some (c ``ectx_item.UnOpCtx #[op], e1)
  | (``expr.BinOp, #[op, e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.BinOpLCtx #[op, v], e1)
    | none => some (c ``ectx_item.BinOpRCtx #[op, e1], e2)
  | (``expr.If, #[e0, e1, e2]) => some (c ``ectx_item.IfCtx #[e1, e2], e0)
  | (``expr.Pair, #[e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.PairLCtx #[v], e1)
    | none => some (c ``ectx_item.PairRCtx #[e1], e2)
  | (``expr.Fst, #[e1]) => some (c ``ectx_item.FstCtx #[], e1)
  | (``expr.Snd, #[e1]) => some (c ``ectx_item.SndCtx #[], e1)
  | (``expr.InjL, #[e1]) => some (c ``ectx_item.InjLCtx #[], e1)
  | (``expr.InjR, #[e1]) => some (c ``ectx_item.InjRCtx #[], e1)
  | (``expr.Case, #[e0, e1, e2]) => some (c ``ectx_item.CaseCtx #[e1, e2], e0)
  | (``expr.AllocN, #[e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.AllocNLCtx #[v], e1)
    | none => some (c ``ectx_item.AllocNRCtx #[e1], e2)
  | (``expr.Load, #[e1]) => some (c ``ectx_item.LoadCtx #[], e1)
  | (``expr.Store, #[e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.StoreLCtx #[v], e1)
    | none => some (c ``ectx_item.StoreRCtx #[e1], e2)
  | (``expr.AllocTape, #[e1]) => some (c ``ectx_item.AllocTapeCtx #[], e1)
  | (``expr.Rand, #[e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.RandLCtx #[v], e1)
    | none => some (c ``ectx_item.RandRCtx #[e1], e2)
  | (``expr.Tick, #[e1]) => some (c ``ectx_item.TickCtx #[], e1)
  | (``expr.CmpXchg, #[e0, e1, e2]) =>
    match isValExpr? e2 with
    | some v2 =>
      match isValExpr? e1 with
      | some v1 => some (c ``ectx_item.CmpXchgLCtx #[v1, v2], e0)
      | none => some (c ``ectx_item.CmpXchgMCtx #[e0, v2], e1)
    | none => some (c ``ectx_item.CmpXchgRCtx #[e0, e1], e2)
  | (``expr.Xchg, #[e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.XchgLCtx #[v], e1)
    | none => some (c ``ectx_item.XchgRCtx #[e1], e2)
  | (``expr.FAA, #[e1, e2]) =>
    match isValExpr? e2 with
    | some v => some (c ``ectx_item.FaaLCtx #[v], e1)
    | none => some (c ``ectx_item.FaaRCtx #[e1], e2)
  | _ => none

/-- Decompose `e` completely: returns `(K, e')` with `e = fill K e'` and `K` as large as
possible (`K` innermost item first, as in `fill`). -/
meta partial def extractAllEctxItems (e : Expr) (acc : List Expr := []) : List Expr × Expr :=
  match extractEctxItem e with
  | some (Ki, e') => extractAllEctxItems e' (Ki :: acc)
  | none => (acc, e)

/-- Meta-level `fill_item`: builds the expression `fill_item Ki e` in constructor form. -/
meta def fillItemMeta (Ki e : Expr) : Option Expr :=
  let c (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) args
  let V (v : Expr) : Expr := c ``expr.Val #[v]
  match Ki.consumeMData.getAppFnArgs with
  | (``ectx_item.AppLCtx, #[v2]) => some (c ``expr.App #[e, V v2])
  | (``ectx_item.AppRCtx, #[e1]) => some (c ``expr.App #[e1, e])
  | (``ectx_item.UnOpCtx, #[op]) => some (c ``expr.UnOp #[op, e])
  | (``ectx_item.BinOpLCtx, #[op, v2]) => some (c ``expr.BinOp #[op, e, V v2])
  | (``ectx_item.BinOpRCtx, #[op, e1]) => some (c ``expr.BinOp #[op, e1, e])
  | (``ectx_item.IfCtx, #[e1, e2]) => some (c ``expr.If #[e, e1, e2])
  | (``ectx_item.PairLCtx, #[v2]) => some (c ``expr.Pair #[e, V v2])
  | (``ectx_item.PairRCtx, #[e1]) => some (c ``expr.Pair #[e1, e])
  | (``ectx_item.FstCtx, #[]) => some (c ``expr.Fst #[e])
  | (``ectx_item.SndCtx, #[]) => some (c ``expr.Snd #[e])
  | (``ectx_item.InjLCtx, #[]) => some (c ``expr.InjL #[e])
  | (``ectx_item.InjRCtx, #[]) => some (c ``expr.InjR #[e])
  | (``ectx_item.CaseCtx, #[e1, e2]) => some (c ``expr.Case #[e, e1, e2])
  | (``ectx_item.AllocNLCtx, #[v2]) => some (c ``expr.AllocN #[e, V v2])
  | (``ectx_item.AllocNRCtx, #[e1]) => some (c ``expr.AllocN #[e1, e])
  | (``ectx_item.LoadCtx, #[]) => some (c ``expr.Load #[e])
  | (``ectx_item.StoreLCtx, #[v2]) => some (c ``expr.Store #[e, V v2])
  | (``ectx_item.StoreRCtx, #[e1]) => some (c ``expr.Store #[e1, e])
  | (``ectx_item.AllocTapeCtx, #[]) => some (c ``expr.AllocTape #[e])
  | (``ectx_item.RandLCtx, #[v2]) => some (c ``expr.Rand #[e, V v2])
  | (``ectx_item.RandRCtx, #[e1]) => some (c ``expr.Rand #[e1, e])
  | (``ectx_item.TickCtx, #[]) => some (c ``expr.Tick #[e])
  | (``ectx_item.XchgLCtx, #[v2]) => some (c ``expr.Xchg #[e, V v2])
  | (``ectx_item.XchgRCtx, #[e1]) => some (c ``expr.Xchg #[e1, e])
  | (``ectx_item.CmpXchgLCtx, #[v1, v2]) => some (c ``expr.CmpXchg #[e, V v1, V v2])
  | (``ectx_item.CmpXchgMCtx, #[e0, v2]) => some (c ``expr.CmpXchg #[e0, e, V v2])
  | (``ectx_item.CmpXchgRCtx, #[e0, e1]) => some (c ``expr.CmpXchg #[e0, e1, e])
  | (``ectx_item.FaaLCtx, #[v2]) => some (c ``expr.FAA #[e, V v2])
  | (``ectx_item.FaaRCtx, #[e1]) => some (c ``expr.FAA #[e1, e])
  | _ => none

/-- Meta-level `fill`: builds `fill K e` in constructor form (`K` innermost item first). -/
meta def fillMeta (K : List Expr) (e : Expr) : Option Expr :=
  K.foldlM (fun e Ki => fillItemMeta Ki e) e

/-- The list literal `[x₁, ..., xₙ] : List ectx_item`. -/
meta def quoteList (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``ectx_item) x acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``ectx_item))

/-- Rocq: `reshape_expr e tac`. Calls `tac K e'` on the decompositions `e = fill K e'` (where
`K : List ectx_item` is given as a list of items, innermost first), starting with the outermost
one (`K = []`) and descending along the evaluation order, until `tac` succeeds; returns its
result together with `K` and `e'`. Failures of `tac` are backtracked. -/
meta partial def reshapeExpr {m : Type → Type} {σ ε α : Type} [Monad m] [MonadBacktrack σ m]
    [MonadExcept ε m] (e : Expr) (tac : List Expr → Expr → m α) :
    m (Option (α × List Expr × Expr)) :=
  go e []
where
  go (e : Expr) (K : List Expr) : m (Option (α × List Expr × Expr)) := do
    if let some a ← observing? (tac K e) then
      return some (a, K, e)
    let some (Ki, e') := extractEctxItem e | return none
    go e' (Ki :: K)

/-- Like `reshapeExpr`, but starting from the innermost decomposition (iris-lean's
`findECtxRev`). -/
meta partial def findECtxRev {m : Type → Type} {σ ε α : Type} [Monad m] [MonadBacktrack σ m]
    [MonadExcept ε m] (e : Expr) (tac : List Expr → Expr → m α) :
    m (Option (α × List Expr × Expr)) := do
  let (K, e') := extractAllEctxItems e
  go e' K
where
  go (e' : Expr) (K : List Expr) : m (Option (α × List Expr × Expr)) := do
    if let some a ← observing? (tac K e') then
      return some (a, K, e')
    match K with
    | [] => return none
    | Ki :: K' =>
      let some e'' := fillItemMeta Ki e' | return none
      go e'' K'

/-- Rocq: `reshape_expr e tac`. `reshape_expr e as K e' => tac` runs the tactic sequence `tac`,
in which the identifiers `K` and `e'` stand for the evaluation context (a `List ectx_item`)
and subexpression of a decomposition `e = fill K e'` (which holds by `rfl`), for every such
decomposition from the outermost (`K = []`) inwards, until `tac` succeeds. -/
syntax (name := reshapeExprTac) "reshape_expr " term " as " ident ppSpace ident " => "
  tacticSeq : tactic

@[tactic reshapeExprTac] meta def evalReshapeExpr : Tactic := fun stx => withMainContext do
  let `(tactic| reshape_expr $e as $K $e' => $tac) := stx | throwUnsupportedSyntax
  let eE ← instantiateMVars (← Term.elabTerm e (some (mkConst ``expr)))
  let res ← reshapeExpr eE fun Ks inner => do
    let Kstx ← Term.exprToSyntax (quoteList Ks)
    let innerStx ← Term.exprToSyntax inner
    let tac' ← tac.raw.replaceM fun s => do
      if s.isIdent && s.getId == K.getId then return some Kstx.raw
      if s.isIdent && s.getId == e'.getId then return some innerStx.raw
      return none
    evalTactic tac'
  if res.isNone then
    throwError "reshape_expr: the tactic failed for all evaluation contexts of{indentExpr eE}"

end reshape

end con_prob_lang
end ConProbLang

end
