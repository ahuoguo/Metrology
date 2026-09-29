module

public import Metrology.ConProbLang.Metatheory

/-!
# Substitution in evaluation contexts

Ported from clutch/theories/con_prob_lang/ctx_subst.v

## Rocq → Lean mapping
* `subst_map_ctx_item`, `subst_map_ctx`, `subst_map_fill_item`, `subst_map_fill` keep their
  names and live in `ConProbLang.con_prob_lang`.
* `stringmap val` is `varmap val` (from `Metatheory.lean`); `map` on lists is `List.map`;
  `fill` is `con_prob_lang.fill` (a left fold of `fill_item`, as in Rocq).

## Deviations
None: Lean's `ectx_item` has exactly the constructors of Rocq's, and `subst_map_ctx_item`
matches all of them (in the Lean constructor order).
-/

@[expose] public section

namespace ConProbLang

namespace con_prob_lang

/-- Rocq: `subst_map_ctx_item`. Substitution in an evaluation-context item. -/
def subst_map_ctx_item (es : varmap val) (K : ectx_item) : ectx_item :=
  match K with
  | AppLCtx v2 => AppLCtx v2
  | AppRCtx e1 => AppRCtx (subst_map es e1)
  | UnOpCtx op => UnOpCtx op
  | BinOpLCtx op v2 => BinOpLCtx op v2
  | BinOpRCtx op e1 => BinOpRCtx op (subst_map es e1)
  | IfCtx e1 e2 => IfCtx (subst_map es e1) (subst_map es e2)
  | PairLCtx v2 => PairLCtx v2
  | PairRCtx e1 => PairRCtx (subst_map es e1)
  | FstCtx => FstCtx
  | SndCtx => SndCtx
  | InjLCtx => InjLCtx
  | InjRCtx => InjRCtx
  | CaseCtx e1 e2 => CaseCtx (subst_map es e1) (subst_map es e2)
  | AllocNLCtx v2 => AllocNLCtx v2
  | AllocNRCtx e1 => AllocNRCtx (subst_map es e1)
  | LoadCtx => LoadCtx
  | StoreLCtx v2 => StoreLCtx v2
  | StoreRCtx e1 => StoreRCtx (subst_map es e1)
  | AllocTapeCtx => AllocTapeCtx
  | RandLCtx v2 => RandLCtx v2
  | RandRCtx e1 => RandRCtx (subst_map es e1)
  | TickCtx => TickCtx
  | XchgLCtx v2 => XchgLCtx v2
  | XchgRCtx e1 => XchgRCtx (subst_map es e1)
  | CmpXchgLCtx v1 v2 => CmpXchgLCtx v1 v2
  | CmpXchgMCtx e0 v2 => CmpXchgMCtx (subst_map es e0) v2
  | CmpXchgRCtx e0 e1 => CmpXchgRCtx (subst_map es e0) (subst_map es e1)
  | FaaLCtx v2 => FaaLCtx v2
  | FaaRCtx e1 => FaaRCtx (subst_map es e1)

/-- Rocq: `subst_map_ctx`. Substitution in an evaluation context. -/
def subst_map_ctx (es : varmap val) (K : List ectx_item) : List ectx_item :=
  K.map (subst_map_ctx_item es)

/-- Rocq: `subst_map_fill_item`. -/
theorem subst_map_fill_item (vs : varmap val) (Ki : ectx_item) (e : expr) :
    subst_map vs (fill_item Ki e) =
      fill_item (subst_map_ctx_item vs Ki) (subst_map vs e) := by
  cases Ki <;> simp [fill_item, subst_map_ctx_item, subst_map]

/-- Rocq: `subst_map_fill`. -/
theorem subst_map_fill (vs : varmap val) (K : List ectx_item) (e : expr) :
    subst_map vs (fill K e) = fill (subst_map_ctx vs K) (subst_map vs e) := by
  induction K generalizing e with
  | nil => rfl
  | cons Ki K ih =>
    change subst_map vs (fill K (fill_item Ki e)) =
      fill (subst_map_ctx vs K) (fill_item (subst_map_ctx_item vs Ki) (subst_map vs e))
    rw [ih, subst_map_fill_item]

end con_prob_lang

end ConProbLang
