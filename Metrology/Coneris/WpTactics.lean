module

public import Metrology.ConProbLang.ClassInstances
public import Iris.ProofMode
public import Iris.BI.WeakestPre
public import Iris.BI.Lib.Atomic
public import Iris.Instances.IProp
public import Lean
public import Qq

/-!
# Generic `wp_*` tactics for `con_prob_lang`

Ported from clutch/theories/con_prob_lang/wp_tactics.v

As in Rocq, the tactics are generic in the weakest precondition: a WP is any function
`gwp : A → CoPset → expr → (val → IProp GF) → IProp GF` (Rocq: `gwp : A → coPset → expr →
(val → iProp Σ) → iProp Σ`), and the requirements of each group of tactics are bundled in a
class (`GwpTacticsBase`, `GwpTacticsBind`, `GwpTacticsPure`, `GwpTacticsFrameWand`,
`GwpTacticsHeap`, `GwpTacticsTapes`, `GwpTacticsAtomicConcurrency`). A program logic makes the
tactics available by instantiating these classes (for Coneris: `Metrology.Coneris.ProofMode`).
The tactics recognise a goal `Δ ⊢ gwp a E e Φ` by splitting off the last four arguments of the
goal (`a`, `E`, `e : expr`, `Φ`) and searching for the class instances for the remaining
function `gwp`; e.g. for iris-lean's `WP e @ s; E {{ Φ }}` (`Wp.wp s E e Φ`) the function is
`Wp.wp` (with its `Wp` instance) and `a = s`.

The implementation of the tactics follows iris-lean's `Iris/HeapLang/ProofMode.lean`
(proof-mode elaborators in `ProofModeM`), with the evaluation-context search of
`Metrology.ConProbLang.Tactics` (`reshapeExpr`, Rocq's `reshape_expr`).

## Rocq → Lean mapping

* Classes: same names and fields (`wptac_wp_value`, `wptac_wp_fupd`, `wptac_wp_bind`,
  `wptac_wp_pure_step`, `wptac_wp_frame_wand`, `wptac_mapsto`, `wptac_mapsto_array`,
  `wptac_wp_alloc`, `wptac_wp_allocN`, `wptac_wp_load`, `wptac_wp_store`, `wptac_mapsto_tape`,
  `wptac_wp_alloctape`, `wptac_wp_rand_tape`, `wptac_mapsto_conc`, `wptac_wp_cmpxchg_fail`,
  `wptac_wp_cmpxchg_suc`, `wptac_wp_xchg`, `wptac_wp_faa`).
  - `Σ` is `GF`. The `invGS_gen hlc Σ` parameter of `GwpTacticsBase` (only used for the fancy
    update in `wptac_wp_fupd`) is `[BIFUpdate (IProp GF)]`; it is dropped from
    `GwpTacticsBind` (where Rocq has it without using it).
  - `laters : bool` is an `outParam` (Rocq finds it by unification when applying the tactic
    lemmas); `▷?laters` is iris-lean's `▷?laters` (`▷^[Bool.toNat laters]`), and Rocq's
    `▷^(if laters then n else 0)` is `▷^[bif laters then n else 0]`.
  - The `TCEq N (Z.to_nat z)` premises are plain equalities `N = z.toNat`.
  - `of_val v` is `Val v`; `(0 < n)%Z` is `0 < n`; `replicate (Z.to_nat n) v` is
    `List.replicate n.toNat v`; `#n` for `n : nat` is `LitV (LitInt (n : ℤ))`.
* Tactic lemmas (`tac_wp_expr_eval`, `tac_wp_pure_later`, `tac_wp_value_nofupd`,
  `tac_wp_value'`, `tac_wp_bind`, `tac_wp_alloc`, `tac_wp_allocN`, `tac_wp_load`,
  `tac_wp_store`, `tac_wp_alloctape`, `tac_wp_rand_tape`, `tac_wp_cmpxchg`,
  `tac_wp_cmpxchg_fail`, `tac_wp_cmpxchg_suc`, `tac_wp_xchg`, `tac_wp_faa`): same names. Rocq's
  environment manipulations (`MaybeIntoLaterNEnvs`, `envs_lookup`, `envs_simple_replace`,
  `envs_app`) are replaced, as in iris-lean's `HeapLang/ProofMode.lean`, by the premises
  `Δ ⊢ ▷?laters Δ'` (the result of iris-lean's `iModAction` with `modality_laterN`),
  `Δ' ⊣⊢ Δ'' ∗ □?p P` (the result of iris-lean's `Hyps.removeG`), and a continuation
  entailment. The continuations of the allocation lemmas are `Δ' ⊢ ∀ l, P l -∗ WP ..`, which
  the tactics introduce with `iintro`; the continuations of the updating lemmas are
  `Δ'' ∗ P' ⊢ WP ..` (the updated points-to keeps its name). The helper `lookup_split` (Rocq:
  `envs_lookup_split`) is a local copy of iris-lean's (private) lemma.
* Tactics (all work on a goal `Δ ⊢ gwp a E e Φ` in the Iris proof mode):
  - `wp_expr_simp` (Rocq: `wp_expr_simpl`, `wp_expr_eval simpl`): simplifies the expression
    (substitutions, derived forms `Let`/`Seq`/`Lam`/..., decidable string comparisons), using
    `simp` with a fixed set of lemmas (Rocq: `simpl`).
  - `wp_value_head`, `wp_finish`: as in Rocq; `wp_value_head` adds `|={E}=>` in front of the
    postcondition unless the postcondition can eliminate it (iris-lean's criterion: an
    `ElimModal` instance whose side condition is solved).
  - `wp_pure e`, `wp_pure`, `wp_pures`, `wp_rec`, `wp_lam`, `wp_if`, `wp_if_true`,
    `wp_if_false`, `wp_unop`, `wp_binop`, `wp_op`, `wp_let`, `wp_seq`, `wp_proj`, `wp_case`,
    `wp_match`, `wp_inj`, `wp_pair`, `wp_closure`: as in Rocq. The focus `e` is a Lean term of
    type `expr` whose holes `_` are unified with the candidate redex (Rocq: `open_constr`),
    e.g. `wp_pure (If _ _ _)` or `wp_pure cpl(if _ then _ else _)`.
    - The reducts of unary and binary operators are evaluated by `simp` (unfolding
      `un_op_eval`/`bin_op_eval`, deciding `decide (v1 = v2)`), since the Lean instances
      `pure_unop_eval`/`pure_binop_eval`/`pure_eqop` leave the result unevaluated (see
      `Metrology.ConProbLang.ClassInstances`); the instance is transported along the
      equation (`pure_exec_eq`).
    - `wp_rec` reduces `App (Val f) (Val v)` where `f` unfolds (by `whnf`) to a `RecV`
      (Rocq: `assert (H := AsRecV_recv)`); the folded `f` is substituted for the recursive
      binder.
    - `wp_pures` only takes steps whose side condition is solved automatically (Rocq:
      `wp_pure _; []`).
  - `wp_bind e`: as in Rocq.
  - `wp_apply t`, `wp_smart_apply t` (with iris-lean's proof-mode terms `t`, e.g.
    `wp_apply lem $$ H1 H2`): as in Rocq; Rocq's `wp_apply lem as (x1 .. xn) "pat"` is
    `wp_apply lem with %x1 .. %xn pat` (iris-lean's syntax).
  - `awp_apply t` and `awp_apply t without H1 .. Hn` (Rocq: `awp_apply lem` and
    `awp_apply lem without "H1 .. Hn"`): as in Rocq, `iAuIntro` is iris-lean's `iauintro`. The
    `without` variant binds an evaluation context `K`, frames `H1 .. Hn` with
    `wptac_wp_frame_wand` (the framed proposition is found with iris-lean's `iaccu`, Rocq:
    `iAccu`) and applies `t`, trying the evaluation contexts in the order of `reshape_expr`.
  - `wp_alloc l as pat`, `wp_alloc l`, `wp_load`, `wp_store`, `wp_alloctape l as pat`,
    `wp_alloctape l`, `wp_randtape as pat`, `wp_randtape`, `wp_cmpxchg as h1 | h2`,
    `wp_cmpxchg_fail`, `wp_cmpxchg_suc`, `wp_xchg`, `wp_faa`: as in Rocq, with iris-lean intro
    patterns `pat` (Rocq: `"H"`) and binder identifiers `h1 h2` (Rocq: simple intro
    patterns). The points-to hypotheses are found in the spatial or intuitionistic context
    (Rocq: `iAssumptionCore`). Side conditions (`vals_compare_safe`, `v = v1`, `v ≠ v1`,
    `0 < n`, `N = z.toNat`) are discharged automatically when possible, and are otherwise left
    as goals.

## Name clash with iris-lean
iris-lean's `Iris.HeapLang.ProofMode` (which is in the import closure) declares tactics with the
same names (`wp_pure`, `wp_pures`, `wp_bind`, `wp_apply`, `wp_load`, ...) for HeapLang. The
tactics here are declared with `priority := high`, so that they take precedence; they fail on
goals that are not a `gwp` of a `con_prob_lang` expression.

## Omitted
* `solve_vals_compare_safe` is part of the side-condition tactic `wp_solve_side` (below).
* The `twp` branches of the tactics (there is no total WP for `con_prob_lang` here).
* The ten-fold `wp_apply ... as (x1 .. xn) pat` notations (subsumed by `with`).
* `pm_prettify`/`pm_reduce` (no counterpart needed: the proof-mode contexts built by the
  tactics are already in normal form).

## Added
* `lookup_split` (local copy of iris-lean's lemma, which is private there).
* `laterIf_later`, `tac_wp_later_op` (the common shape of the heap tactic lemmas),
  `pure_exec_eq`, `dfrac_own_one`, `bientails_trans`: helper lemmas for the tactics.
* `wp_solve_side`: the side-condition tactic of the `wp_*` tactics.
* Internal tactics: `wp_pure_strict` (Rocq: `wp_pure _; []`), `wp_alloc_core`,
  `wp_alloctape_core`, `wp_randtape_core`, `gwp_apply_raw`, `gwp_smart_apply_raw`,
  `gwp_apply_post`, `gwp_frame_wand` (Rocq: `iApply (wptac_wp_frame_wand with [Hs]);
  [iAccu|..]`).
* The meta-level machinery (`runTacticGwp`, `gwpFinish`, `gwpValueHead`, `gwpBindCore`,
  `gwpPure`, `gwpApplyLoop`, `runTacticHeapGwp`, `lookupHyp`, ...), modelled on iris-lean's
  `HeapLang/ProofMode.lean`.
-/

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang Qq

namespace Coneris

/-! ## The classes -/

/-- Rocq: `GwpTacticsBase`. A basic set of requirements for a weakest precondition. -/
public class GwpTacticsBase (GF : BundledGFunctors) (A : Type) [BIFUpdate (IProp GF)]
    (gwp : A → CoPset → expr → (val → IProp GF) → IProp GF) : Prop where
  wptac_wp_value (E : CoPset) (Φ : val → IProp GF) (v : val) (a : A) :
    Φ v ⊢ gwp a E (Val v) Φ
  wptac_wp_fupd (E : CoPset) (Φ : val → IProp GF) (e : expr) (a : A) :
    gwp a E e (fun v => iprop(|={E}=> Φ v)) ⊢ gwp a E e Φ

/-- Rocq: `GwpTacticsBind`. -/
public class GwpTacticsBind (GF : BundledGFunctors) (A : Type)
    (gwp : A → CoPset → expr → (val → IProp GF) → IProp GF) : Prop where
  wptac_wp_bind (K : expr → expr) [ConLanguageCtx (Λ := con_prob_lang) K] (E : CoPset)
    (e : expr) (Φ : val → IProp GF) (a : A) :
    gwp a E e (fun v => gwp a E (K (Val v)) Φ) ⊢ gwp a E (K e) Φ

/-- Rocq: `GwpTacticsPure`. -/
public class GwpTacticsPure (GF : BundledGFunctors) (A : Type) (laters : outParam Bool)
    (gwp : A → CoPset → expr → (val → IProp GF) → IProp GF) : Prop where
  wptac_wp_pure_step (E : CoPset) (e1 e2 : expr) (φ : Prop) (n : ℕ) (Φ : val → IProp GF)
    (a : A) : PureExec (Λ := con_prob_lang) φ n e1 e2 → φ →
    ▷^[bif laters then n else 0] gwp a E e2 Φ ⊢ gwp a E e1 Φ

/-- Rocq: `GwpTacticsFrameWand`. -/
public class GwpTacticsFrameWand (GF : BundledGFunctors) (A : Type) (laters : outParam Bool)
    (gwp : A → CoPset → expr → (val → IProp GF) → IProp GF) : Prop where
  wptac_wp_frame_wand (E : CoPset) (e : expr) (Φ : val → IProp GF) (a : A) (R : IProp GF) :
    ⊢ R -∗ gwp a E e (fun v => iprop(R -∗ Φ v)) -∗ gwp a E e Φ

/-- Rocq: `GwpTacticsHeap`. -/
public class GwpTacticsHeap (GF : BundledGFunctors) (A : Type) (laters : outParam Bool)
    (gwp : A → CoPset → expr → (val → IProp GF) → IProp GF) where
  wptac_mapsto : Loc → DFrac → val → IProp GF
  wptac_mapsto_array : Loc → DFrac → List val → IProp GF
  wptac_wp_alloc (E : CoPset) (v : val) (a : A) (Φ : val → IProp GF) :
    ⊢ True -∗
      ▷?laters (∀ l, wptac_mapsto l (DFrac.own 1) v -∗ Φ (LitV (LitLoc l))) -∗
      gwp a E (Alloc (Val v)) Φ
  wptac_wp_allocN (E : CoPset) (v : val) (n : ℤ) (a : A) (Φ : val → IProp GF) :
    0 < n →
    ⊢ True -∗
      ▷?laters (∀ l, wptac_mapsto_array l (DFrac.own 1) (List.replicate n.toNat v) -∗
        Φ (LitV (LitLoc l))) -∗
      gwp a E (AllocN (Val (LitV (LitInt n))) (Val v)) Φ
  wptac_wp_load (E : CoPset) (v : val) (l : Loc) (dq : DFrac) (a : A) (Φ : val → IProp GF) :
    ⊢ ▷ wptac_mapsto l dq v -∗
      ▷?laters (wptac_mapsto l dq v -∗ Φ v) -∗
      gwp a E (Load (Val (LitV (LitLoc l)))) Φ
  wptac_wp_store (E : CoPset) (v v' : val) (l : Loc) (a : A) (Φ : val → IProp GF) :
    ⊢ ▷ wptac_mapsto l (DFrac.own 1) v' -∗
      ▷?laters (wptac_mapsto l (DFrac.own 1) v -∗ Φ (LitV LitUnit)) -∗
      gwp a E (Store (Val (LitV (LitLoc l))) (Val v)) Φ

/-- Rocq: `GwpTacticsTapes`. -/
public class GwpTacticsTapes (GF : BundledGFunctors) (A : Type) (laters : outParam Bool)
    (gwp : A → CoPset → expr → (val → IProp GF) → IProp GF) where
  wptac_mapsto_tape : Loc → DFrac → ℕ → List ℕ → IProp GF
  wptac_wp_alloctape (E : CoPset) (N : ℕ) (z : ℤ) (a : A) (Φ : val → IProp GF) :
    N = z.toNat →
    ⊢ True -∗
      ▷?laters (∀ l, wptac_mapsto_tape l (DFrac.own 1) N [] -∗ Φ (LitV (LitLbl l))) -∗
      gwp a E (AllocTape (Val (LitV (LitInt z)))) Φ
  wptac_wp_rand_tape (E : CoPset) (N n : ℕ) (z : ℤ) (ns : List ℕ) (l : Loc) (dq : DFrac)
    (a : A) (Φ : val → IProp GF) :
    N = z.toNat →
    ⊢ ▷ wptac_mapsto_tape l dq N (n :: ns) -∗
      ▷?laters (wptac_mapsto_tape l dq N ns -∗ ⌜n ≤ N⌝ -∗ Φ (LitV (LitInt (n : ℤ)))) -∗
      gwp a E (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) Φ

/-- Rocq: `GwpTacticsAtomicConcurrency`. -/
public class GwpTacticsAtomicConcurrency (GF : BundledGFunctors) (A : Type)
    (laters : outParam Bool) (gwp : A → CoPset → expr → (val → IProp GF) → IProp GF) where
  wptac_mapsto_conc : Loc → DFrac → val → IProp GF
  wptac_wp_cmpxchg_fail (E : CoPset) (Φ : val → IProp GF) (l : Loc) (dq : DFrac)
    (v v1 v2 : val) (a : A) :
    v ≠ v1 → vals_compare_safe v v1 →
    ⊢ ▷ wptac_mapsto_conc l dq v -∗
      ▷?laters (wptac_mapsto_conc l dq v -∗ Φ (PairV v (LitV (LitBool false)))) -∗
      gwp a E (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) Φ
  wptac_wp_cmpxchg_suc (E : CoPset) (Φ : val → IProp GF) (l : Loc) (v v1 v2 : val) (a : A) :
    v = v1 → vals_compare_safe v v1 →
    ⊢ ▷ wptac_mapsto_conc l (DFrac.own 1) v -∗
      ▷?laters (wptac_mapsto_conc l (DFrac.own 1) v2 -∗ Φ (PairV v (LitV (LitBool true)))) -∗
      gwp a E (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) Φ
  wptac_wp_xchg (E : CoPset) (Φ : val → IProp GF) (l : Loc) (v1 v2 : val) (a : A) :
    ⊢ ▷ wptac_mapsto_conc l (DFrac.own 1) v1 -∗
      ▷?laters (wptac_mapsto_conc l (DFrac.own 1) v2 -∗ Φ v1) -∗
      gwp a E (Xchg (Val (LitV (LitLoc l))) (Val v2)) Φ
  wptac_wp_faa (E : CoPset) (Φ : val → IProp GF) (l : Loc) (i1 i2 : ℤ) (a : A) :
    ⊢ ▷ wptac_mapsto_conc l (DFrac.own 1) (LitV (LitInt i1)) -∗
      ▷?laters (wptac_mapsto_conc l (DFrac.own 1) (LitV (LitInt (i1 + i2))) -∗
        Φ (LitV (LitInt i1))) -∗
      gwp a E (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) Φ

export GwpTacticsBase (wptac_wp_value wptac_wp_fupd)
export GwpTacticsBind (wptac_wp_bind)
export GwpTacticsPure (wptac_wp_pure_step)
export GwpTacticsFrameWand (wptac_wp_frame_wand)
export GwpTacticsHeap (wptac_mapsto wptac_mapsto_array wptac_wp_alloc wptac_wp_allocN
  wptac_wp_load wptac_wp_store)
export GwpTacticsTapes (wptac_mapsto_tape wptac_wp_alloctape wptac_wp_rand_tape)
export GwpTacticsAtomicConcurrency (wptac_mapsto_conc wptac_wp_cmpxchg_fail
  wptac_wp_cmpxchg_suc wptac_wp_xchg wptac_wp_faa)

/-! ## Tactic lemmas -/

/-- Hand out a looked-up hypothesis and a wand that restores the context (Rocq:
`envs_lookup_split`; a local copy of iris-lean's private `lookup_split`). -/
public theorem lookup_split {PROP : Type _} [BI PROP] {Δ' Δ'' P : PROP} [Affine P] {p : Bool}
    (hsplit : Δ' ⊣⊢ Δ'' ∗ □?p P) : Δ' ⊢ P ∗ (P -∗ Δ') := by
  match p with
  | false => exact hsplit.1.trans (sep_comm.1.trans (sep_mono .rfl (wand_intro hsplit.2)))
  | true =>
    refine hsplit.1.trans ?_
    refine (sep_mono .rfl intuitionistically_sep_dup.1).trans ?_
    refine sep_left_comm.1.trans ?_
    exact sep_mono intuitionistically_elim (wand_intro (sep_elim_left.trans hsplit.2))

section wp_tactics

variable {GF : BundledGFunctors} {A : Type} {gwp : A → CoPset → expr → (val → IProp GF) → IProp GF}

/-- Rocq: `tac_wp_expr_eval`. -/
public theorem tac_wp_expr_eval {Δ : IProp GF} {a : A} {E : CoPset} {Φ : val → IProp GF}
    {e e' : expr} (h : e = e') (H : Δ ⊢ gwp a E e' Φ) : Δ ⊢ gwp a E e Φ :=
  h ▸ H

/-- Rocq: `tac_wp_pure_later`. -/
public theorem tac_wp_pure_later (laters : Bool) [GwpTacticsPure GF A laters gwp]
    {Δ Δ' : IProp GF} {E : CoPset} (K : List ectx_item) {e1 e2 : expr} {φ : Prop} {n : ℕ}
    {Φ : val → IProp GF} {a : A}
    (hexec : PureExec (Λ := con_prob_lang) φ n e1 e2) (hφ : φ)
    (hlater : Δ ⊢ ▷^[bif laters then n else 0] Δ') (H : Δ' ⊢ gwp a E (fill K e2) Φ) :
    Δ ⊢ gwp a E (fill K e1) Φ :=
  hlater.trans <| (laterN_mono _ H).trans <|
    wptac_wp_pure_step E _ _ φ n Φ a (pure_exec_ctx (Λ := con_prob_lang) (fill K) φ n e1 e2 hexec)
      hφ

variable [BIFUpdate (IProp GF)]

/-- Rocq: `tac_wp_value_nofupd`. -/
public theorem tac_wp_value_nofupd [GwpTacticsBase GF A gwp] {Δ : IProp GF} {E : CoPset}
    {Φ : val → IProp GF} {v : val} {a : A} (H : Δ ⊢ Φ v) : Δ ⊢ gwp a E (Val v) Φ :=
  H.trans (wptac_wp_value E Φ v a)

/-- Rocq: `tac_wp_value'`. -/
public theorem tac_wp_value' [GwpTacticsBase GF A gwp] {Δ : IProp GF} {E : CoPset}
    {Φ : val → IProp GF} {v : val} {a : A} (H : Δ ⊢ |={E}=> Φ v) : Δ ⊢ gwp a E (Val v) Φ :=
  H.trans <| (wptac_wp_value E (fun v => iprop(|={E}=> Φ v)) v a).trans (wptac_wp_fupd E Φ _ a)

end wp_tactics

section wp_bind_tactics

variable {GF : BundledGFunctors} {A : Type} {gwp : A → CoPset → expr → (val → IProp GF) → IProp GF}

/-- Rocq: `tac_wp_bind`. (Rocq's premise `f = λ e, fill K e`, which only serves to `simpl` the
context, is not needed: the tactics build the filled context at the meta level.) -/
public theorem tac_wp_bind [GwpTacticsBind GF A gwp] (K : List ectx_item) {Δ : IProp GF}
    {E : CoPset} {Φ : val → IProp GF} {e : expr} {a : A}
    (H : Δ ⊢ gwp a E e (fun v => gwp a E (fill K (Val v)) Φ)) : Δ ⊢ gwp a E (fill K e) Φ :=
  H.trans (wptac_wp_bind (fill K) E e Φ a)

end wp_bind_tactics

/-- Helper: `▷?laters P ⊢ ▷ P`. -/
public theorem laterIf_later {PROP : Type _} [BI PROP] (laters : Bool) {P : PROP} :
    ▷?laters P ⊢ ▷ P := by
  cases laters
  · exact later_intro
  · exact .rfl

/-- Helper: the common shape of the heap/tape/concurrency tactic lemmas: a lemma
`⊢ ▷ P -∗ ▷?laters (P' -∗ Φ r) -∗ gwp a E e Φ` applied in an evaluation context, where `P` is
split off the context `Δ'` and `P'` is added back. -/
public theorem tac_wp_later_op {GF : BundledGFunctors} {A : Type}
    {gwp : A → CoPset → expr → (val → IProp GF) → IProp GF} [GwpTacticsBind GF A gwp]
    (laters : Bool) {Δ Δ' Δ'' P P' : IProp GF} {E : CoPset} {K : List ectx_item} {e : expr}
    {r : val} {Φ : val → IProp GF} {a : A}
    (hwp : ∀ Ψ : val → IProp GF, ⊢ ▷ P -∗ ▷?laters (P' -∗ Ψ r) -∗ gwp a E e Ψ)
    (hlater : Δ ⊢ ▷?laters Δ') (hsplit : Δ' ⊢ P ∗ Δ'')
    (hcont : Δ'' ∗ P' ⊢ gwp a E (fill K (Val r)) Φ) :
    Δ ⊢ gwp a E (fill K e) Φ := by
  refine hlater.trans ?_
  refine .trans ?_ (wptac_wp_bind (fill K) E e Φ a)
  refine wand_apply (wand_entails (hwp _)) ?_
  refine (laterN_mono _ hsplit).trans ?_
  refine (laterN_sep _).1.trans (sep_mono (laterIf_later laters) (laterN_mono _ ?_))
  exact wand_intro hcont

section heap_tactics

variable {GF : BundledGFunctors} {A : Type} {gwp : A → CoPset → expr → (val → IProp GF) → IProp GF}
variable {laters : Bool} [GwpTacticsBind GF A gwp] [GwpTacticsHeap GF A laters gwp]

/-- Rocq: `tac_wp_alloc`. -/
public theorem tac_wp_alloc {Δ Δ' : IProp GF} {E : CoPset} (K : List ectx_item) {v : val}
    {Φ : val → IProp GF} {a : A} (hlater : Δ ⊢ ▷?laters Δ')
    (hcont : Δ' ⊢ ∀ l, wptac_mapsto (gwp := gwp) l (DFrac.own 1) v -∗
      gwp a E (fill K (Val (LitV (LitLoc l)))) Φ) :
    Δ ⊢ gwp a E (fill K (Alloc (Val v))) Φ := by
  refine hlater.trans ?_
  refine .trans ?_ (wptac_wp_bind (fill K) E _ Φ a)
  refine wand_apply (wand_entails (wptac_wp_alloc E v a _)) ?_
  exact emp_sep.2.trans (sep_mono true_intro (laterN_mono _ hcont))

/-- Rocq: `tac_wp_allocN`. -/
public theorem tac_wp_allocN {Δ Δ' : IProp GF} {E : CoPset} (K : List ectx_item) {v : val}
    {n : ℤ} {Φ : val → IProp GF} {a : A} (hn : 0 < n) (hlater : Δ ⊢ ▷?laters Δ')
    (hcont : Δ' ⊢ ∀ l, wptac_mapsto_array (gwp := gwp) l (DFrac.own 1)
      (List.replicate n.toNat v) -∗ gwp a E (fill K (Val (LitV (LitLoc l)))) Φ) :
    Δ ⊢ gwp a E (fill K (AllocN (Val (LitV (LitInt n))) (Val v))) Φ := by
  refine hlater.trans ?_
  refine .trans ?_ (wptac_wp_bind (fill K) E _ Φ a)
  refine wand_apply (wand_entails (wptac_wp_allocN E v n a _ hn)) ?_
  exact emp_sep.2.trans (sep_mono true_intro (laterN_mono _ hcont))

/-- Rocq: `tac_wp_load`. -/
public theorem tac_wp_load {Δ Δ' Δ'' : IProp GF} {p : Bool} {E : CoPset} (K : List ectx_item)
    {l : Loc} {dq : DFrac} {v : val} {Φ : val → IProp GF} {a : A}
    (hlater : Δ ⊢ ▷?laters Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ □?p wptac_mapsto (gwp := gwp) l dq v)
    (hcont : Δ' ⊢ gwp a E (fill K (Val v)) Φ) :
    Δ ⊢ gwp a E (fill K (Load (Val (LitV (LitLoc l))))) Φ :=
  tac_wp_later_op laters (fun Ψ => wptac_wp_load E v l dq a Ψ) hlater
    (lookup_split hsplit) (wand_elim_left.trans hcont)

/-- Rocq: `tac_wp_store`. -/
public theorem tac_wp_store {Δ Δ' Δ'' : IProp GF} {E : CoPset} (K : List ectx_item)
    {l : Loc} {v v' : val} {Φ : val → IProp GF} {a : A}
    (hlater : Δ ⊢ ▷?laters Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ wptac_mapsto (gwp := gwp) l (DFrac.own 1) v)
    (hcont : Δ'' ∗ wptac_mapsto (gwp := gwp) l (DFrac.own 1) v' ⊢
      gwp a E (fill K (Val (LitV LitUnit))) Φ) :
    Δ ⊢ gwp a E (fill K (Store (Val (LitV (LitLoc l))) (Val v'))) Φ :=
  tac_wp_later_op laters (fun Ψ => wptac_wp_store E v' v l a Ψ) hlater
    (hsplit.1.trans sep_comm.1) hcont

end heap_tactics

section tape_tactics

variable {GF : BundledGFunctors} {A : Type} {gwp : A → CoPset → expr → (val → IProp GF) → IProp GF}
variable {laters : Bool} [GwpTacticsBind GF A gwp] [GwpTacticsTapes GF A laters gwp]

/-- Rocq: `tac_wp_alloctape`. -/
public theorem tac_wp_alloctape {Δ Δ' : IProp GF} {E : CoPset} (K : List ectx_item) {N : ℕ}
    {z : ℤ} {Φ : val → IProp GF} {a : A} (hN : N = z.toNat) (hlater : Δ ⊢ ▷?laters Δ')
    (hcont : Δ' ⊢ ∀ l, wptac_mapsto_tape (gwp := gwp) l (DFrac.own 1) N [] -∗
      gwp a E (fill K (Val (LitV (LitLbl l)))) Φ) :
    Δ ⊢ gwp a E (fill K (AllocTape (Val (LitV (LitInt z))))) Φ := by
  refine hlater.trans ?_
  refine .trans ?_ (wptac_wp_bind (fill K) E _ Φ a)
  refine wand_apply (wand_entails (wptac_wp_alloctape E N z a _ hN)) ?_
  exact emp_sep.2.trans (sep_mono true_intro (laterN_mono _ hcont))

/-- Rocq: `tac_wp_rand_tape`. -/
public theorem tac_wp_rand_tape {Δ1 Δ2 Δ3 : IProp GF} {E : CoPset} (K : List ectx_item)
    {l : Loc} {N : ℕ} {z : ℤ} {n : ℕ} {ns : List ℕ} {Φ : val → IProp GF} {a : A}
    (hN : N = z.toNat) (hlater : Δ1 ⊢ ▷?laters Δ2)
    (hsplit : Δ2 ⊣⊢ Δ3 ∗ wptac_mapsto_tape (gwp := gwp) l (DFrac.own 1) N (n :: ns))
    (hcont : Δ3 ∗ wptac_mapsto_tape (gwp := gwp) l (DFrac.own 1) N ns ⊢
      ⌜n ≤ N⌝ -∗ gwp a E (fill K (Val (LitV (LitInt (n : ℤ))))) Φ) :
    Δ1 ⊢ gwp a E (fill K (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l))))) Φ := by
  refine tac_wp_later_op (P' := iprop(wptac_mapsto_tape (gwp := gwp) l (DFrac.own 1) N ns ∗ ⌜n ≤ N⌝))
    (r := LitV (LitInt (n : ℤ))) laters (fun Ψ => ?_) hlater (hsplit.1.trans sep_comm.1) ?_
  · iintro Hl HΨ
    iapply wptac_wp_rand_tape E N n z ns l (DFrac.own 1) a Ψ hN $$ Hl
    refine laterN_mono _ ?_
    iintro HΨ Ht %Hn
    iapply HΨ
    isplitl [Ht]
    · iexact Ht
    · ipureintro; exact Hn
  · iintro ⟨HΔ, Ht, %Hn⟩
    iapply hcont $$ [HΔ Ht]
    · isplitl [HΔ]
      · iexact HΔ
      · iexact Ht
    · ipureintro; exact Hn

end tape_tactics

section concurrency_tactics

variable {GF : BundledGFunctors} {A : Type} {gwp : A → CoPset → expr → (val → IProp GF) → IProp GF}
variable {laters : Bool} [GwpTacticsBind GF A gwp] [GwpTacticsAtomicConcurrency GF A laters gwp]

/-- Rocq: `tac_wp_cmpxchg_fail`. -/
public theorem tac_wp_cmpxchg_fail {Δ Δ' Δ'' : IProp GF} {p : Bool} {E : CoPset}
    (K : List ectx_item) {l : Loc} {dq : DFrac} {v v1 v2 : val} {Φ : val → IProp GF} {a : A}
    (hlater : Δ ⊢ ▷?laters Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ □?p wptac_mapsto_conc (gwp := gwp) l dq v)
    (hne : v ≠ v1) (hsafe : vals_compare_safe v v1)
    (hcont : Δ' ⊢ gwp a E (fill K (Val (PairV v (LitV (LitBool false))))) Φ) :
    Δ ⊢ gwp a E (fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2))) Φ :=
  tac_wp_later_op laters (fun Ψ => wptac_wp_cmpxchg_fail E Ψ l dq v v1 v2 a hne hsafe) hlater
    (lookup_split hsplit) (wand_elim_left.trans hcont)

/-- Rocq: `tac_wp_cmpxchg_suc`. -/
public theorem tac_wp_cmpxchg_suc {Δ Δ' Δ'' : IProp GF} {E : CoPset} (K : List ectx_item)
    {l : Loc} {v v1 v2 : val} {Φ : val → IProp GF} {a : A}
    (hlater : Δ ⊢ ▷?laters Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) v)
    (heq : v = v1) (hsafe : vals_compare_safe v v1)
    (hcont : Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) v2 ⊢
      gwp a E (fill K (Val (PairV v (LitV (LitBool true))))) Φ) :
    Δ ⊢ gwp a E (fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2))) Φ :=
  tac_wp_later_op laters (fun Ψ => wptac_wp_cmpxchg_suc E Ψ l v v1 v2 a heq hsafe) hlater
    (hsplit.1.trans sep_comm.1) hcont

/-- Rocq: `tac_wp_cmpxchg`. -/
public theorem tac_wp_cmpxchg {Δ Δ' Δ'' : IProp GF} {E : CoPset} (K : List ectx_item)
    {l : Loc} {v v1 v2 : val} {Φ : val → IProp GF} {a : A}
    (hlater : Δ ⊢ ▷?laters Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) v)
    (hsafe : vals_compare_safe v v1)
    (hsuc : v = v1 → Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) v2 ⊢
      gwp a E (fill K (Val (PairV v (LitV (LitBool true))))) Φ)
    (hfail : v ≠ v1 → Δ' ⊢ gwp a E (fill K (Val (PairV v (LitV (LitBool false))))) Φ) :
    Δ ⊢ gwp a E (fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2))) Φ :=
  if heq : v = v1 then tac_wp_cmpxchg_suc K hlater hsplit heq hsafe (hsuc heq)
  else tac_wp_cmpxchg_fail (p := false) K hlater hsplit heq hsafe (hfail heq)

/-- Rocq: `tac_wp_xchg`. -/
public theorem tac_wp_xchg {Δ Δ' Δ'' : IProp GF} {E : CoPset} (K : List ectx_item)
    {l : Loc} {v v' : val} {Φ : val → IProp GF} {a : A}
    (hlater : Δ ⊢ ▷?laters Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) v)
    (hcont : Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) v' ⊢
      gwp a E (fill K (Val v)) Φ) :
    Δ ⊢ gwp a E (fill K (Xchg (Val (LitV (LitLoc l))) (Val v'))) Φ :=
  tac_wp_later_op laters (fun Ψ => wptac_wp_xchg E Ψ l v v' a) hlater
    (hsplit.1.trans sep_comm.1) hcont

/-- Rocq: `tac_wp_faa`. -/
public theorem tac_wp_faa {Δ Δ' Δ'' : IProp GF} {E : CoPset} (K : List ectx_item)
    {l : Loc} {z1 z2 : ℤ} {Φ : val → IProp GF} {a : A}
    (hlater : Δ ⊢ ▷?laters Δ')
    (hsplit : Δ' ⊣⊢ Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) (LitV (LitInt z1)))
    (hcont : Δ'' ∗ wptac_mapsto_conc (gwp := gwp) l (DFrac.own 1) (LitV (LitInt (z1 + z2))) ⊢
      gwp a E (fill K (Val (LitV (LitInt z1)))) Φ) :
    Δ ⊢ gwp a E (fill K (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt z2))))) Φ :=
  tac_wp_later_op laters (fun Ψ => wptac_wp_faa E Ψ l z1 z2 a) hlater
    (hsplit.1.trans sep_comm.1) hcont

end concurrency_tactics

/-! ## Helpers for the tactics (not in Rocq) -/

/-- Helper: transport a `PureExec` instance along an equation of the reducts. -/
public theorem pure_exec_eq {φ : Prop} {n : ℕ} {e1 e2 e2' : expr}
    (h : PureExec (Λ := con_prob_lang) φ n e1 e2) (he : e2 = e2') :
    PureExec (Λ := con_prob_lang) φ n e1 e2' :=
  he ▸ h

/-- Helper: `DFrac.own 1` (used by the tactics to build points-to patterns). -/
public abbrev dfrac_own_one : DFrac := DFrac.own 1

/-- Helper: compose a bi-entailment with an entailment. -/
public theorem bientails_trans {PROP : Type _} [BI PROP] {P Q R : PROP} (h1 : P ⊣⊢ Q)
    (h2 : Q ⊢ R) : P ⊢ R :=
  h1.1.trans h2

/-- The side-condition tactic of the `wp_*` tactics (Rocq: `solve_vals_compare_safe`, and the
`tc_solve`/`TCEq` side conditions). -/
macro (priority := high) "wp_solve_side" : tactic => `(tactic| first
  | trivial
  | rfl
  | decide
  | (simp only [vals_compare_safe, val_is_unboxed, lit_is_unboxed, true_or, or_true]; done)
  | (simp [*]; done)
  | omega)

section meta_tactics

open Lean Meta Elab Tactic

/-- The derived forms (`abbrev`s) of `con_prob_lang`, unfolded by the tactics before searching
for evaluation contexts. -/
public meta def derivedForms : List Name :=
  [``ConProbLang.con_prob_lang.Lam, ``ConProbLang.con_prob_lang.Let,
   ``ConProbLang.con_prob_lang.Seq, ``ConProbLang.con_prob_lang.LamV,
   ``ConProbLang.con_prob_lang.LetCtx, ``ConProbLang.con_prob_lang.SeqCtx,
   ``ConProbLang.con_prob_lang.Alloc, ``ConProbLang.con_prob_lang.Match,
   ``ConProbLang.con_prob_lang.CAS, ``ConProbLang.con_prob_lang.Skip,
   ``ConProbLang.con_prob_lang.NONE, ``ConProbLang.con_prob_lang.NONEV,
   ``ConProbLang.con_prob_lang.SOME, ``ConProbLang.con_prob_lang.SOMEV,
   ``ConProbLang.con_prob_lang.alloc, ``ConProbLang.con_prob_lang.tick]

/-- Unfold the derived forms of `con_prob_lang` (a definitional unfolding). -/
public meta def expandDerived (e : Lean.Expr) : MetaM Lean.Expr := do
  deltaExpand (← instantiateMVars e) (derivedForms.contains ·)

/-- Rocq: `wp_expr_simpl`. Simplify an expression: unfold substitutions and derived forms, and
decide string comparisons. Returns the simplified expression and a proof of the equation (if
something changed). -/
public meta def gwpExprSimp (e : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
  let mut thms : SimpTheorems := {}
  for d in [``ConProbLang.con_prob_lang.subst, ``ConProbLang.con_prob_lang.subst'] ++
      derivedForms do
    thms ← thms.addDeclToUnfold d
  for l in [``ConProbLang.binder.BNamed.injEq, ``ne_eq, ``not_false_eq_true,
      ``not_true_eq_false, ``_root_.and_true, ``_root_.true_and, ``_root_.and_false,
      ``_root_.false_and, ``_root_.and_self,
      ``ite_true, ``ite_false] do
    thms ← thms.addConst l
  let mut procs : Simprocs := {}
  procs ← procs.add ``reduceIte (post := false)
  for p in [``String.reduceEq, ``reduceCtorEq] do
    procs ← procs.add p (post := true)
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let ⟨res, _⟩ ← Meta.simp (← instantiateMVars e) ctx (simprocs := #[procs])
  return (res.expr, res.proof?)

/-- Normalise a computed value (the result of `un_op_eval`/`bin_op_eval`) with the default
simp set. Returns the value and a proof of the equation (if something changed). -/
public meta def gwpValSimp (v : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
  let mut thms ← getSimpTheorems
  for d in [``ConProbLang.con_prob_lang.bin_op_eval, ``ConProbLang.con_prob_lang.un_op_eval,
      ``ConProbLang.con_prob_lang.bin_op_eval_int,
      ``ConProbLang.con_prob_lang.bin_op_eval_bool, ``ConProbLang.con_prob_lang.bin_op_eval_loc] do
    thms ← thms.addDeclToUnfold d
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let ⟨res, _⟩ ← Meta.simp (← instantiateMVars v) ctx (simprocs := #[← Simp.getSimprocs])
  return (res.expr, res.proof?)

/-- A WP goal `gwp a E e Φ` (without the expression `e`). -/
public meta structure GwpShape where
  GF : Lean.Expr
  A : Lean.Expr
  gwp : Lean.Expr
  a : Lean.Expr
  E : Lean.Expr
  Φ : Lean.Expr

/-- The WP `gwp a E e Φ`. -/
public meta def GwpShape.wp (w : GwpShape) (e : Lean.Expr) (Φ : Lean.Expr := w.Φ) : Lean.Expr :=
  mkAppN w.gwp #[w.a, w.E, e, Φ]

/-- `Val v`. -/
public meta def mkValE (v : Lean.Expr) : Lean.Expr := mkApp (mkConst ``expr.Val) v

/-- Meta-level `fill K e` (in constructor form). -/
public meta def gwpFill (K : List Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr := do
  let some e' := fillMeta K e | throwError "wp tactic: cannot fill the evaluation context"
  return e'

/-- A proof-mode goal `Δ ⊢ gwp a E e Φ`. -/
public meta structure GwpGoal where
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  w : GwpShape
  e : Lean.Expr

/-- Split a proof-mode goal `Δ ⊢ gwp a E e Φ` into its components, requiring that `e : expr`.
The derived forms in `e` are unfolded. -/
public meta def runTacticGwp {α} (tacName : Name)
    (k : MVarId → GwpGoal → ProofModeM α) : TacticM α :=
  ProofModeM.runTactic tacName fun mvar {prop, hyps, goal, ..} => do
    let propE := (← instantiateMVars prop).consumeMData
    unless propE.isAppOfArity ``Iris.IProp 1 do
      throwError "{tacName}: the goal {goal} must be an `IProp` {propE}"
    let GF := propE.appArg!
    let goalE := (← instantiateMVars goal).headBeta.consumeMData
    let args := goalE.getAppArgs
    let n := args.size
    unless n ≥ 4 do
      throwError "{tacName}: the goal {goal} is not a weakest precondition"
    let e := args[n-2]!
    unless ← isDefEq (← inferType e) (mkConst ``expr) do
      throwError "{tacName}: the goal {goal} is not a weakest precondition of a `con_prob_lang` \
        expression"
    let gwp := mkAppN goalE.getAppFn (args.extract 0 (n - 4))
    let a := args[n-4]!
    let e ← expandDerived e
    k mvar { hyps, w := { GF, A := ← inferType a, gwp, a, E := args[n-3]!, Φ := args[n-1]! }, e }

/-- Try to synthesize an instance (with iris-lean's instance search, which may leave
side-condition metavariables; these are added as goals). -/
public meta def trySynthRaw (ty : Lean.Expr) : ProofModeM (Option Lean.Expr) := do
  let LOption.some (e, mvars) ← ProofMode.trySynthInstance ty | return none
  mvars.toList.forM (addMVarGoal ·)
  return some e

/-- Synthesize the class `cls GF A [laters] gwp` for the WP. -/
public meta def synthGwpClass (w : GwpShape) (cls : Name) (laters? : Bool) :
    ProofModeM (Lean.Expr × Option Lean.Expr) := do
  if laters? then
    let laters ← mkFreshExprMVar (mkConst ``Bool)
    let ty ← mkAppM cls #[w.GF, w.A, laters, w.gwp]
    let some inst ← trySynthRaw ty
      | throwError "no instance {ty}"
    return (inst, some (← instantiateMVars laters))
  else
    let ty ← mkAppM cls #[w.GF, w.A, w.gwp]
    let some inst ← trySynthRaw ty
      | throwError "no instance {ty}"
    return (inst, none)

/-- Is `laters` (after `whnf`) `true`? -/
public meta def isLatersTrue (laters : Lean.Expr) : MetaM Bool := do
  let l ← whnfD laters
  if l.isConstOf ``Bool.true then return true
  if l.isConstOf ``Bool.false then return false
  throwError "wp tactic: cannot evaluate the `laters` parameter {laters}"

/-- Strip `n` laters from the context: `Δ ⊢ ▷^[n] Δ'`. -/
public meta def gwpStripLaters {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (n : Lean.Expr) :
    ProofModeM ((e' : Q($prop)) × Hyps bi e' × Lean.Expr) := do
  let M ← mkAppOptM ``modality_laterN #[prop, n, bi]
  let ⟨e', hyps', pf⟩ ← iModAction (bi1 := bi) hyps (M : Q(Modality $prop $prop))
  return ⟨e', hyps', pf⟩

/-- Solve a side condition with `wp_solve_side`; if this fails, either fail or add it as a goal. -/
public meta def gwpSolveSide (φ : Lean.Expr) (failOnUnsolved : Bool) : ProofModeM Lean.Expr := do
  let pf ← mkFreshExprSyntheticOpaqueMVar φ
  let solved ← observing? (evalTacticAt (← `(tactic| wp_solve_side)) pf.mvarId!)
  match solved with
  | some [] => return pf
  | _ =>
    if failOnUnsolved then throwError "wp tactic: failed to solve the side condition {φ}"
    addMVarGoal pf.mvarId!
    return pf

/-- Rocq: `wp_value_head`. If `e` is a value `Val v`, reduce the goal `Δ ⊢ gwp a E (Val v) Φ` to
`Δ ⊢ Φ v` (if `Φ v` can absorb a fancy update) or `Δ ⊢ |={E}=> Φ v`. -/
public meta def gwpValueHead {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (w : GwpShape) (e : Lean.Expr) :
    ProofModeM (Option Lean.Expr) := do
  let some v := isValExpr? e | return none
  let goal := (mkApp w.Φ v).headBeta
  let (inst, _) ← synthGwpClass w ``GwpTacticsBase false
  let fupdGoal ← mkAppM ``FUpd.fupd #[w.E, w.E, goal]
  let c ← mkFreshExprMVar (mkSort .zero)
  let p' ← mkFreshExprMVar (mkConst ``Bool)
  let A' ← mkFreshExprMVar prop
  let Q' ← mkFreshExprMVar prop
  let elimTy ← mkAppM ``ElimModal #[c, mkConst ``false, mkConst ``InOut.out, p', fupdGoal, A',
    goal, Q']
  let noFupd ← do
    if (← observing? (do
        let LOption.some _ ← ProofMode.trySynthInstance elimTy | failure)).isSome then
      pure (← observing? (gwpSolveSide (← instantiateMVars c) true)).isSome
    else pure false
  if noFupd then
    let pf ← addBIGoal hyps (goal : Q($prop))
    return some (← mkAppOptM ``tac_wp_value_nofupd
      #[w.GF, w.A, w.gwp, none, inst, ehyps, w.E, w.Φ, v, w.a, pf])
  else
    let pf ← addBIGoal hyps (fupdGoal : Q($prop))
    return some (← mkAppOptM ``tac_wp_value'
      #[w.GF, w.A, w.gwp, none, inst, ehyps, w.E, w.Φ, v, w.a, pf])

/-- Rocq: `wp_finish`. Simplify the expression, and remove the WP if it is a value. -/
public meta def gwpFinish {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (w : GwpShape) (e : Lean.Expr) :
    ProofModeM Lean.Expr := do
  let (e', pfeq?) ← gwpExprSimp e
  let next ← match ← gwpValueHead hyps w e' with
    | some pf => pure pf
    | none => addBIGoal hyps (w.wp e' : Q($prop))
  match pfeq? with
  | none => pure next
  | some pfeq =>
    mkAppOptM ``tac_wp_expr_eval #[w.GF, w.A, w.gwp, ehyps, w.a, w.E, w.Φ, e, e', pfeq, next]

/-- Rocq: `wp_bind_core`. Given `e = fill K e'`, reduce the goal `Δ ⊢ gwp a E e Φ` to
`Δ ⊢ gwp a E e' (λ v, gwp a E (fill K (Val v)) Φ)`, which is proved by `k`. -/
public meta def gwpBindCore (ehyps : Option Lean.Expr) (w : GwpShape) (K : List Lean.Expr)
    (e' : Lean.Expr) (k : Lean.Expr → ProofModeM Lean.Expr) : ProofModeM Lean.Expr := do
  if K.isEmpty then
    k (w.wp e')
  else
    let Φ' ← withLocalDeclD `v (mkConst ``val) fun v => do
      mkLambdaFVars #[v] (w.wp (← gwpFill K (mkValE v)))
    let pf ← k (w.wp e' Φ')
    mkAppOptM ``tac_wp_bind #[some w.GF, some w.A, some w.gwp, none, some (quoteList K), ehyps,
      some w.E, some w.Φ, some e', some w.a, some pf]

/-- The result of a pure-step search at a redex `e1`: the precondition `φ`, the number of steps
`n`, the reduct `e2`, the `PureExec` instance, and possibly a proof of `φ`. -/
public meta structure PureStepRes where
  φ : Lean.Expr
  n : Lean.Expr
  e2 : Lean.Expr
  inst : Lean.Expr
  hφ : Option Lean.Expr := none

/-- The `PureExec` instance search (Rocq: `tc_solve`). -/
public meta def findPureExecInst (e1 : Lean.Expr) : ProofModeM PureStepRes := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let n ← mkFreshExprMVar (mkConst ``Nat)
  let e2 ← mkFreshExprMVar (mkConst ``expr)
  let ty ← mkAppOptM ``PureExec #[mkConst ``con_prob_lang, φ, n, e1, e2]
  let some inst ← trySynthRaw ty | failure
  let φ ← instantiateMVars φ
  let n ← instantiateMVars n
  let e2 ← instantiateMVars e2
  let inst ← instantiateMVars inst
  return { φ, n, e2, inst }

/-- Normalise the reduct of an operator step (`UnOp`/`BinOp`): the `PureExec` instances
`pure_unop_eval`/`pure_binop_eval`/`pure_eqop` leave `un_op_eval`/`bin_op_eval`/`decide` in the
result; these are evaluated with `simp` (`gwpValSimp`), and the instance is transported along
the resulting equation (`pure_exec_eq`). -/
public meta def evalOpStep (e1 : Lean.Expr) : ProofModeM PureStepRes := do
  let res ← findPureExecInst e1
  match e1.consumeMData.getAppFnArgs with
  | (``expr.UnOp, _) | (``expr.BinOp, _) =>
    let (e2', pf?) ← gwpValSimp res.e2
    match pf? with
    | none => return res
    | some pf =>
      let inst ← mkAppOptM ``pure_exec_eq #[res.φ, res.n, e1, res.e2, e2', res.inst, pf]
      return { res with e2 := e2', inst }
  | _ => failure

/-- Find any pure step for `e1` (Rocq: `wp_pure _`). -/
public meta def findAnyPureExec (e1 : Lean.Expr) : ProofModeM PureStepRes := do
  if let some r ← observing? (evalOpStep e1) then return r
  findPureExecInst e1

/-- The pure step of `wp_rec` (Rocq: `wp_pure (App _ _)` with `AsRecV_recv` as an instance):
reduce `App (Val f) (Val v)` where `f` unfolds to a `RecV`. -/
public meta def findRecPureExec (e1 : Lean.Expr) : ProofModeM PureStepRes := do
  let (``expr.App, #[a1, a2]) := e1.consumeMData.getAppFnArgs | failure
  let some f := isValExpr? a1 | failure
  let some v := isValExpr? a2 | failure
  let f' ← whnfD f
  let (``val.RecV, #[fb, xb, body]) := f'.getAppFnArgs | failure
  let recv := mkApp3 (mkConst ``val.RecV) fb xb body
  let hrec ← mkExpectedTypeHint (← mkEqRefl f) (← mkEq f recv)
  let asrec := mkApp5 (mkConst ``AsRecV.mk) f fb xb body hrec
  let inst ← mkAppOptM ``pure_beta #[fb, xb, body, f, v, asrec]
  let e2 := mkApp3 (mkConst ``subst') xb v (mkApp3 (mkConst ``subst') fb f body)
  return { φ := mkConst ``True, n := mkNatLit 1, e2, inst, hφ := some (mkConst ``True.intro) }

/-- Rocq: `tac_wp_pure_later` applied at the first decomposition `e = fill K e1` for which
`find e1` succeeds. Returns the new context, the new expression `fill K e2`, and a function
turning a proof of the new goal into a proof of the old goal. -/
public meta def gwpPure {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (w : GwpShape) (e : Lean.Expr)
    (failOnUnsolved : Bool) (find : Lean.Expr → ProofModeM PureStepRes) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr ×
      (Lean.Expr → ProofModeM Lean.Expr)) := do
  let some (res, K, e1) ← reshapeExpr e fun _ e1 => find e1
    | throwError "wp_pure: cannot find a redex in {e}"
  let (inst, some laters) ← synthGwpClass w ``GwpTacticsPure true
    | throwError "wp_pure: no `GwpTacticsPure` instance"
  let cnt := if ← isLatersTrue laters then res.n else mkNatLit 0
  let hφ ← match res.hφ with
    | some hφ => pure hφ
    | none => gwpSolveSide res.φ failOnUnsolved
  let ⟨ehyps', hyps', pfLater⟩ ← gwpStripLaters hyps cnt
  let e' ← gwpFill K res.e2
  let mk (next : Lean.Expr) : ProofModeM Lean.Expr :=
    mkAppOptM ``tac_wp_pure_later #[w.GF, w.A, w.gwp, laters, inst, ehyps, ehyps', w.E,
      quoteList K, e1, res.e2, res.φ, res.n, w.Φ, w.a, res.inst, hφ, pfLater, next]
  return ⟨ehyps', hyps', e', mk⟩

/-- Elaborate a focus pattern (a term of type `expr` with holes). -/
public meta def elabFocus (focus : Syntax) : TacticM Lean.Expr := withMainContext do
  let f ← Tactic.elabTermEnsuringType focus (some (mkConst ``expr)) (mayPostpone := true)
  expandDerived f

/-- Rocq: `wp_pure efoc`, with a pure-step search `find`. -/
public meta def wpPureCore (tacName : Name) (focus : Option Syntax) (failOnUnsolved : Bool)
    (find : Lean.Expr → ProofModeM PureStepRes) : TacticM Unit := do
  let focusE ← focus.mapM elabFocus
  runTacticGwp tacName fun mvar {hyps, w, e, ..} => do
    let ⟨_, hyps', e', mkPf⟩ ← gwpPure hyps w e failOnUnsolved fun e1 => do
      if let some f := focusE then guard (← isDefEq e1 f)
      find e1
    let next ← gwpFinish hyps' w e'
    mvar.assign (← mkPf next)


/-- Rocq: `wp_expr_simpl`. Simplify the expression of the WP goal. -/
elab (priority := high) "wp_expr_simp" : tactic =>
  runTacticGwp `wp_expr_simp fun mvar {ehyps, hyps, w, e, ..} => do
    let (e', pfeq?) ← gwpExprSimp e
    let pf ← addBIGoal hyps (w.wp e')
    let pf ← match pfeq? with
      | none => pure pf
      | some pfeq =>
        mkAppOptM ``tac_wp_expr_eval #[w.GF, w.A, w.gwp, ehyps, w.a, w.E, w.Φ, e, e', pfeq, pf]
    mvar.assign pf

/-- Rocq: `wp_value_head`. -/
elab (priority := high) "wp_value_head" : tactic =>
  runTacticGwp `wp_value_head fun mvar {hyps, w, e, ..} => do
    let some pf ← gwpValueHead hyps w e | throwError "wp_value_head: {e} is not a value"
    mvar.assign pf

/-- Rocq: `wp_finish`. -/
elab (priority := high) "wp_finish" : tactic =>
  runTacticGwp `wp_finish fun mvar {hyps, w, e, ..} => do
    mvar.assign (← gwpFinish hyps w e)

/-- Rocq: `wp_pure efoc`. Take a pure step at the first redex (following the evaluation order)
that unifies with the focus `efoc` (a term of type `expr`, possibly with holes); `wp_pure`
takes any pure step. The side condition of the step is discharged if possible, and otherwise
left as a goal. -/
syntax (name := wpPureTac) (priority := high) "wp_pure" (ppSpace colGt term:max)? : tactic

elab_rules : tactic
  | `(tactic| wp_pure $[$f]?) => wpPureCore `wp_pure f false findAnyPureExec

/-- `wp_pure` that fails if the side condition of the step cannot be solved. -/
elab (priority := high) "wp_pure_strict" f:(ppSpace colGt term:max)? : tactic =>
  wpPureCore `wp_pure f true findAnyPureExec

/-- Rocq: `wp_pures`. Take pure steps as long as possible (only steps whose side condition is
solved automatically), then simplify, and remove the WP if the expression is a value. -/
macro (priority := high) "wp_pures" : tactic =>
  `(tactic| first
    | (wp_pure_strict; repeat wp_pure_strict)
    | wp_finish)

/-- Rocq: `wp_rec`. Beta-reduce the first application of a (possibly hidden behind a
definition) recursive function to a value. -/
elab (priority := high) "wp_rec" : tactic => wpPureCore `wp_rec none false findRecPureExec

/-- Rocq: `wp_lam`. -/
macro (priority := high) "wp_lam" : tactic => `(tactic| wp_rec)
/-- Rocq: `wp_if`. -/
macro (priority := high) "wp_if" : tactic => `(tactic| wp_pure (expr.If _ _ _))
/-- Rocq: `wp_if_true`. -/
macro (priority := high) "wp_if_true" : tactic =>
  `(tactic| wp_pure (expr.If (expr.Val (val.LitV (base_lit.LitBool true))) _ _))
/-- Rocq: `wp_if_false`. -/
macro (priority := high) "wp_if_false" : tactic =>
  `(tactic| wp_pure (expr.If (expr.Val (val.LitV (base_lit.LitBool false))) _ _))
/-- Rocq: `wp_unop`. -/
macro (priority := high) "wp_unop" : tactic => `(tactic| wp_pure (expr.UnOp _ _))
/-- Rocq: `wp_binop`. -/
macro (priority := high) "wp_binop" : tactic => `(tactic| wp_pure (expr.BinOp _ _ _))
/-- Rocq: `wp_op`. -/
macro (priority := high) "wp_op" : tactic => `(tactic| first | wp_unop | wp_binop)
/-- Rocq: `wp_let`. -/
macro (priority := high) "wp_let" : tactic =>
  `(tactic| (wp_pure (expr.Rec binder.BAnon (binder.BNamed _) _); wp_lam))
/-- Rocq: `wp_seq`. -/
macro (priority := high) "wp_seq" : tactic =>
  `(tactic| (wp_pure (expr.Rec binder.BAnon binder.BAnon _); wp_lam))
/-- Rocq: `wp_proj`. -/
macro (priority := high) "wp_proj" : tactic => `(tactic| first | wp_pure (expr.Fst _) | wp_pure (expr.Snd _))
/-- Rocq: `wp_case`. -/
macro (priority := high) "wp_case" : tactic => `(tactic| wp_pure (expr.Case _ _ _))
/-- Rocq: `wp_match`. -/
macro (priority := high) "wp_match" : tactic => `(tactic| (wp_case; wp_pure (expr.Rec _ _ _); wp_lam))
/-- Rocq: `wp_inj`. -/
macro (priority := high) "wp_inj" : tactic => `(tactic| first | wp_pure (expr.InjL _) | wp_pure (expr.InjR _))
/-- Rocq: `wp_pair`. -/
macro (priority := high) "wp_pair" : tactic => `(tactic| wp_pure (expr.Pair _ _))
/-- Rocq: `wp_closure`. -/
macro (priority := high) "wp_closure" : tactic => `(tactic| wp_pure (expr.Rec _ _ _))

/-- Rocq: `wp_bind efoc`. Bind the first subexpression (following the evaluation order) that
unifies with `efoc`. -/
syntax (name := wpBindTac) (priority := high) "wp_bind" ppSpace colGt term:max : tactic

elab_rules : tactic
  | `(tactic| wp_bind $f) => do
    let focus ← elabFocus f
    runTacticGwp `wp_bind fun mvar {ehyps, hyps, w, e, ..} => do
      let some ((), K, e') ← reshapeExpr e fun _ e' => do guard (← isDefEq e' focus)
        | throwError "wp_bind: cannot find {focus} in {e}"
      mvar.assign (← gwpBindCore (some ehyps) w K e' fun g => addBIGoal hyps g)

/-! ### `wp_apply` -/

/-- The state of the `wp_apply` loop: the current context (containing the lemma), the current
expression, and the proof transformer back to the original goal. -/
public meta structure GwpApplyState {u : Level} {prop : Q(Type u)} (bi : Q(BI $prop)) where
  {ehypsC : Q($prop)}
  hypsC : Hyps bi ehypsC
  eC : Lean.Expr
  prefixPf : Lean.Expr → ProofModeM Lean.Expr

/-- Rocq: `wp_apply_core`. Apply the lemma (in the context as `lemIVar`) at some evaluation
context of the current expression; with `smart`, take pure steps until it applies (Rocq:
`wp_smart_apply`). -/
public meta partial def gwpApplyLoop {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    (w : GwpShape) (lemIVar : IVarId) (smart : Bool) (failed : MessageData)
    (st : GwpApplyState bi) : ProofModeM Lean.Expr := do
  let ⟨_, hypsR, _, A', p', _, remPf⟩ := Hyps.remove (rp := true) st.hypsC lemIVar
  let applied ← reshapeExpr st.eC fun K e' =>
    gwpBindCore none w K e' fun g => iApply hypsR p' A' (g : Q($prop))
  if let some (pf, _, _) := applied then
    return ← st.prefixPf (← mkAppM ``bientails_trans #[remPf, pf])
  unless smart do throwError failed
  let r ← observing? (gwpPure st.hypsC w st.eC true findAnyPureExec)
  let some ⟨_, hypsN, eN, mkPf⟩ := r | throwError failed
  let (eN', pfeq?) ← gwpExprSimp eN
  let prefixPf (pf : Lean.Expr) : ProofModeM Lean.Expr := do
    let pf ← match pfeq? with
      | none => pure pf
      | some pfeq =>
        mkAppOptM ``tac_wp_expr_eval #[w.GF, w.A, w.gwp, none, w.a, w.E, w.Φ, eN, eN', pfeq, pf]
    st.prefixPf (← mkPf pf)
  gwpApplyLoop w lemIVar smart failed { hypsC := hypsN, eC := eN', prefixPf }

/-- Rocq: `wp_apply lem` / `wp_smart_apply lem` (without the trailing `iNext`). -/
public meta def gwpApplyRaw (tacName : Name) (smart : Bool) (pmt : TSyntax `pmTerm) :
    TacticM Unit := do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  runTacticGwp tacName fun mvar {bi, hyps, w, e, ..} => do
    let goal := w.wp e
    let ⟨_, hypsP, p, A, posePf⟩ ← iHave hyps goal pmt true
    let lemIVar ← mkFreshIVarId (isTrue p)
    let ⟨_, hyps0, addPf⟩ := Hyps.add bi .anonymous lemIVar p A hypsP
    let failed ← addMessageContext m!"{tacName}: cannot apply {A}"
    let prefixPf (pf : Lean.Expr) : ProofModeM Lean.Expr := do
      return (mkApp posePf (← mkAppM ``bientails_trans #[addPf, pf])).headBeta
    mvar.assign (← gwpApplyLoop w lemIVar smart failed { hypsC := hyps0, eC := e, prefixPf })

/-! ### Heap, tape and concurrency tactics -/

/-- A WP goal for the heap tactics: the goal, the instance of the class of the tactic, its
`laters` parameter, and the context `hyps'` after stripping `▷?laters` (`pfLater`). -/
public meta structure GwpHeapGoal where
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  {ehyps' : Q($prop)}
  hyps' : Hyps bi ehyps'
  pfLater : Lean.Expr
  w : GwpShape
  e : Lean.Expr
  inst : Lean.Expr
  laters : Lean.Expr

/-- The shared prologue of the heap tactics (Rocq: `wp_pures; lazymatch goal with ..`, and
`MaybeIntoLaterNEnvs`). -/
public meta def runTacticHeapGwp {α} (tacName : Name) (cls : Name)
    (k : MVarId → GwpHeapGoal → ProofModeM α) : TacticM α := do
  try evalTactic (← `(tactic| wp_pures))
  catch _ => throwError "{tacName}: the goal is not a WP"
  runTacticGwp tacName fun mvar {hyps, w, e, ..} => do
    let (inst, some laters) ← synthGwpClass w cls true
      | throwError "{tacName}: no instance of {cls}"
    let cnt := mkNatLit (if ← isLatersTrue laters then 1 else 0)
    let ⟨_, hyps', pfLater⟩ ← gwpStripLaters hyps cnt
    k mvar { hyps, hyps', pfLater, w, e, inst, laters }

/-- Unfold a projection of a class instance (e.g. `wptac_mapsto` of the Coneris instance to
`heap_elem`), for display. -/
public meta def unfoldInst (e : Lean.Expr) : MetaM Lean.Expr := do
  match ← unfoldProjInst? e with
  | some e' => return e'.headBeta
  | none => return e

/-- The projection `cls.field` of the instance `g.inst`, applied to `args`, and unfolded. -/
public meta def gwpField (g : GwpHeapGoal) (field : Name) (args : Array Lean.Expr) :
    MetaM Lean.Expr := do
  let f ← mkAppOptM field
    (#[g.w.GF, g.w.A, g.laters, g.w.gwp, g.inst].map some ++ args.map some)
  unfoldInst f

/-- `gwpValSimp`, keeping the result only if it is definitionally equal to the input. -/
public meta def gwpValSimpDefEq (e : Lean.Expr) : MetaM Lean.Expr := do
  let (e', _) ← gwpValSimp e
  if ← withNewMCtxDepth (isDefEq e e') then return e' else return e

/-- `DFrac.own 1`. -/
public meta def dfracOwnOne : MetaM Lean.Expr := whnfR (mkConst ``dfrac_own_one)

/-- Locate (and remove) a hypothesis `□?p pat` of the context (Rocq: `envs_lookup`,
`iAssumptionCore`). Returns its name, its identifier, the remaining context, and the proof of
`Δ ⊣⊢ Δ'' ∗ □?p pat`. -/
public meta def lookupHyp {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (pat p : Lean.Expr) :
    ProofModeM (Name × IVarId × (e'' : Q($prop)) × Hyps bi e'' × Lean.Expr) := do
  let some ((name, vid), ⟨e'', hyps'', _, _, _, _, pf⟩) ← hyps.removeG false fun name vid p' ty => do
      let ok ← observing? (do
        guard (← isDefEq ty pat)
        guard (← isDefEq p' p))
      return ok.map fun _ => (name, vid)
    | throwError "cannot find a hypothesis {← instantiateMVars pat}"
  return ⟨name, vid, e'', hyps'', pf⟩

/-- Match `Val (LitV (LitLoc l))`. -/
public meta def matchLocVal? (e : Lean.Expr) : Option Lean.Expr := do
  let v ← isValExpr? e
  let (``val.LitV, #[lit]) := v.consumeMData.getAppFnArgs | none
  let (``base_lit.LitLoc, #[l]) := lit.consumeMData.getAppFnArgs | none
  return l

/-- Match `Val (LitV (LitLbl l))`. -/
public meta def matchLblVal? (e : Lean.Expr) : Option Lean.Expr := do
  let v ← isValExpr? e
  let (``val.LitV, #[lit]) := v.consumeMData.getAppFnArgs | none
  let (``base_lit.LitLbl, #[l]) := lit.consumeMData.getAppFnArgs | none
  return l

/-- Match `Val (LitV (LitInt z))`. -/
public meta def matchIntVal? (e : Lean.Expr) : Option Lean.Expr := do
  let v ← isValExpr? e
  let (``val.LitV, #[lit]) := v.consumeMData.getAppFnArgs | none
  let (``base_lit.LitInt, #[z]) := lit.consumeMData.getAppFnArgs | none
  return z

/-- `LitV (LitLoc l)`, `LitV (LitLbl l)`, `LitV (LitInt z)`, `LitV LitUnit`, `PairV v (LitV (LitBool b))`. -/
public meta def mkLocV (l : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst ``val.LitV) (mkApp (mkConst ``base_lit.LitLoc) l)
public meta def mkLblV (l : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst ``val.LitV) (mkApp (mkConst ``base_lit.LitLbl) l)
public meta def mkIntV (z : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst ``val.LitV) (mkApp (mkConst ``base_lit.LitInt) z)
public meta def mkUnitV : Lean.Expr := mkApp (mkConst ``val.LitV) (mkConst ``base_lit.LitUnit)
public meta def mkPairBoolV (v : Lean.Expr) (b : Bool) : Lean.Expr :=
  mkApp2 (mkConst ``val.PairV) v
    (mkApp (mkConst ``val.LitV) (mkApp (mkConst ``base_lit.LitBool) (toExpr b)))

/-- Build the continuation goal `∀ l, P l -∗ gwp a E (fill K (Val (mkV l))) Φ` of the
allocation tactics. -/
public meta def allocContGoal (w : GwpShape) (K : List Lean.Expr) (P : Lean.Expr → MetaM Lean.Expr)
    (mkV : Lean.Expr → Lean.Expr) : MetaM Lean.Expr := do
  let body ← withLocalDeclD `l (mkConst ``Loc) fun l => do
    let wp := w.wp (← gwpFill K (mkValE (mkV l)))
    mkLambdaFVars #[l] (← mkAppM ``Iris.BI.wand #[← P l, wp])
  mkAppM ``Iris.BI.forall #[body]

/-- `Δ'' ∗ P'` for the updating tactics: add `P'` back under the name of the removed
hypothesis, and finish the continuation. Returns the proof of `Δ'' ∗ P' ⊢ gwp a E e' Φ`. -/
public meta def readdAndFinish {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}
    {e'' : Q($prop)} (hyps'' : Hyps bi e'') (name : Name) (vid : IVarId) (P' : Lean.Expr)
    (w : GwpShape) (e' : Lean.Expr) : ProofModeM Lean.Expr := do
  let ⟨_, hyps''', pfAdd⟩ := hyps''.add bi name vid q(false) (P' : Q($prop))
  let pf ← gwpFinish hyps''' w e'
  mkAppM ``bientails_trans #[pfAdd, pf]

/-- The allocation core of `wp_alloc` (Rocq: `tac_wp_alloc`/`tac_wp_allocN`). Leaves the goal
`Δ' ⊢ ∀ l, l ↦ v -∗ WP ..` (resp. with `l ↦∗ replicate n v`). -/
elab (priority := high) "wp_alloc_core" : tactic =>
  runTacticHeapGwp `wp_alloc ``GwpTacticsHeap fun mvar g => do
    let some ((n, v), K, _) ← reshapeExpr g.e fun _ e' => do
        let (``expr.AllocN, #[a1, a2]) := e'.consumeMData.getAppFnArgs | failure
        let some n := matchIntVal? a1 | failure
        let some v := isValExpr? a2 | failure
        return (n, v)
      | throwError "wp_alloc: cannot find 'Alloc' in {g.e}"
    let own1 ← dfracOwnOne
    if ← isDefEq n (toExpr (1 : Int)) then
      let goal ← allocContGoal g.w K
        (fun l => gwpField g ``GwpTacticsHeap.wptac_mapsto #[l, own1, v]) mkLocV
      let pf ← addBIGoal g.hyps' goal
      mvar.assign (← mkAppOptM ``tac_wp_alloc #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
        g.ehyps, g.ehyps', g.w.E, quoteList K, v, g.w.Φ, g.w.a, g.pfLater, pf])
    else
      let vs ← mkAppM ``List.replicate #[← gwpValSimpDefEq (← mkAppM ``Int.toNat #[n]), v]
      let goal ← allocContGoal g.w K
        (fun l => gwpField g ``GwpTacticsHeap.wptac_mapsto_array #[l, own1, vs]) mkLocV
      let pf ← addBIGoal g.hyps' goal
      let hn ← gwpSolveSide (← mkAppM ``LT.lt #[toExpr (0 : Int), n]) false
      mvar.assign (← mkAppOptM ``tac_wp_allocN #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
        g.ehyps, g.ehyps', g.w.E, quoteList K, v, n, g.w.Φ, g.w.a, hn, g.pfLater, pf])

/-- Rocq: `wp_alloc l as "H"`. Allocate a reference (or an array, for `AllocN`), introducing
the location `l` and the points-to with the intro pattern(s). -/
syntax (name := wpAllocTac) (priority := high) "wp_alloc" ppSpace colGt ident
  (" as" (ppSpace colGt introPat)+)? : tactic

macro_rules
  | `(tactic| wp_alloc $l:ident as $pats*) =>
    `(tactic| focus (wp_alloc_core; iintro %$l:ident $pats*; wp_finish))
  | `(tactic| wp_alloc $l:ident) => `(tactic| focus (wp_alloc_core; iintro %$l:ident _; wp_finish))

/-- Rocq: `wp_load`. -/
elab (priority := high) "wp_load" : tactic =>
  runTacticHeapGwp `wp_load ``GwpTacticsHeap fun mvar g => do
    let some (l, K, _) ← reshapeExpr g.e fun _ e' => do
        let (``expr.Load, #[a]) := e'.consumeMData.getAppFnArgs | failure
        let some l := matchLocVal? a | failure
        return l
      | throwError "wp_load: cannot find 'Load' in {g.e}"
    let dq ← mkFreshExprMVar (mkConst ``DFrac)
    let v ← mkFreshExprMVar (mkConst ``val)
    let p ← mkFreshExprMVar (mkConst ``Bool)
    let pat ← gwpField g ``GwpTacticsHeap.wptac_mapsto #[l, dq, v]
    let ⟨_, _, e'', _, pfSplit⟩ ← lookupHyp g.hyps' pat p
    let dq ← instantiateMVars dq
    let v ← instantiateMVars v
    let p ← instantiateMVars p
    let pfCont ← gwpFinish g.hyps' g.w (← gwpFill K (mkValE v))
    mvar.assign (← mkAppOptM ``tac_wp_load #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
      g.ehyps, g.ehyps', e'', p, g.w.E, quoteList K, l, dq, v, g.w.Φ, g.w.a, g.pfLater, pfSplit,
      pfCont])

/-- Rocq: `wp_store`. -/
elab (priority := high) "wp_store" : tactic => do
  runTacticHeapGwp `wp_store ``GwpTacticsHeap fun mvar g => do
    let some ((l, v'), K, _) ← reshapeExpr g.e fun _ e' => do
        let (``expr.Store, #[a1, a2]) := e'.consumeMData.getAppFnArgs | failure
        let some l := matchLocVal? a1 | failure
        let some v' := isValExpr? a2 | failure
        return (l, v')
      | throwError "wp_store: cannot find 'Store' in {g.e}"
    let own1 ← dfracOwnOne
    let v ← mkFreshExprMVar (mkConst ``val)
    let pat ← gwpField g ``GwpTacticsHeap.wptac_mapsto #[l, own1, v]
    let ⟨name, vid, e'', hyps'', pfSplit⟩ ← lookupHyp g.hyps' pat (mkConst ``false)
    let v ← instantiateMVars v
    let P' ← gwpField g ``GwpTacticsHeap.wptac_mapsto #[l, own1, v']
    let pfCont ← readdAndFinish hyps'' name vid P' g.w (← gwpFill K (mkValE mkUnitV))
    mvar.assign (← mkAppOptM ``tac_wp_store #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
      g.ehyps, g.ehyps', e'', g.w.E, quoteList K, l, v, v', g.w.Φ, g.w.a, g.pfLater, pfSplit,
      pfCont])
  evalTactic (← `(tactic| try wp_seq))

/-- The core of `wp_alloctape` (Rocq: `tac_wp_alloctape`). -/
elab (priority := high) "wp_alloctape_core" : tactic =>
  runTacticHeapGwp `wp_alloctape ``GwpTacticsTapes fun mvar g => do
    let some (z, K, _) ← reshapeExpr g.e fun _ e' => do
        let (``expr.AllocTape, #[a]) := e'.consumeMData.getAppFnArgs | failure
        let some z := matchIntVal? a | failure
        return z
      | throwError "wp_alloctape: cannot find 'AllocTape' in {g.e}"
    let own1 ← dfracOwnOne
    let N ← gwpValSimpDefEq (← mkAppM ``Int.toNat #[z])
    let nil ← mkAppOptM ``List.nil #[mkConst ``Nat]
    let goal ← allocContGoal g.w K
      (fun l => gwpField g ``GwpTacticsTapes.wptac_mapsto_tape #[l, own1, N, nil]) mkLblV
    let pf ← addBIGoal g.hyps' goal
    let hN ← gwpSolveSide (← mkEq N (← mkAppM ``Int.toNat #[z])) false
    mvar.assign (← mkAppOptM ``tac_wp_alloctape #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
      g.ehyps, g.ehyps', g.w.E, quoteList K, N, z, g.w.Φ, g.w.a, hN, g.pfLater, pf])

/-- Rocq: `wp_alloctape l as "H"`. -/
syntax (name := wpAllocTapeTac) (priority := high) "wp_alloctape" ppSpace colGt ident
  (" as" (ppSpace colGt introPat)+)? : tactic

macro_rules
  | `(tactic| wp_alloctape $l:ident as $pats*) =>
    `(tactic| focus (wp_alloctape_core; iintro %$l:ident $pats*; wp_finish))
  | `(tactic| wp_alloctape $l:ident) =>
    `(tactic| focus (wp_alloctape_core; iintro %$l:ident _; wp_finish))

/-- The core of `wp_randtape` (Rocq: `tac_wp_rand_tape`). -/
elab (priority := high) "wp_randtape_core" : tactic =>
  runTacticHeapGwp `wp_randtape ``GwpTacticsTapes fun mvar g => do
    let some ((z, l), K, _) ← reshapeExpr g.e fun _ e' => do
        let (``expr.Rand, #[a1, a2]) := e'.consumeMData.getAppFnArgs | failure
        let some z := matchIntVal? a1 | failure
        let some l := matchLblVal? a2 | failure
        return (z, l)
      | throwError "wp_randtape: cannot find 'Rand' in {g.e}"
    let own1 ← dfracOwnOne
    let N ← mkFreshExprMVar (mkConst ``Nat)
    let n ← mkFreshExprMVar (mkConst ``Nat)
    let ns ← mkFreshExprMVar (← mkAppM ``List #[mkConst ``Nat])
    let pat ← gwpField g ``GwpTacticsTapes.wptac_mapsto_tape #[l, own1, N, ← mkAppM ``List.cons #[n, ns]]
    let ⟨name, vid, e'', hyps'', pfSplit⟩ ← lookupHyp g.hyps' pat (mkConst ``false)
    let N ← instantiateMVars N
    let n ← instantiateMVars n
    let ns ← instantiateMVars ns
    let P' ← gwpField g ``GwpTacticsTapes.wptac_mapsto_tape #[l, own1, N, ns]
    let ⟨_, hyps''', pfAdd⟩ := hyps''.add _ name vid q(false) P'
    let wp := g.w.wp (← gwpFill K (mkValE (mkIntV (← mkAppOptM ``Nat.cast #[mkConst ``Int, none, n]))))
    let le ← mkAppM ``LE.le #[n, N]
    let goal ← mkAppM ``Iris.BI.wand #[← mkAppOptM ``Iris.BI.pure #[g.prop, none, le], wp]
    let pf ← addBIGoal hyps''' goal
    let hN ← gwpSolveSide (← mkEq N (← mkAppM ``Int.toNat #[z])) false
    mvar.assign (← mkAppOptM ``tac_wp_rand_tape #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
      g.ehyps, g.ehyps', e'', g.w.E, quoteList K, l, N, z, n, ns, g.w.Φ, g.w.a, hN, g.pfLater,
      pfSplit, ← mkAppM ``bientails_trans #[pfAdd, pf]])

/-- Rocq: `wp_randtape as "H"` (default `%_`: the bound `n ≤ N` goes to the Lean context). -/
syntax (name := wpRandTapeTac) (priority := high) "wp_randtape"
  (" as" (ppSpace colGt introPat)+)? : tactic

macro_rules
  | `(tactic| wp_randtape as $pats*) =>
    `(tactic| focus (wp_randtape_core; iintro $pats*; wp_finish))
  | `(tactic| wp_randtape) => `(tactic| focus (wp_randtape_core; iintro %_; wp_finish))

/-- Match a `CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)` redex. -/
public meta def findCmpXchg (e : Lean.Expr) :
    ProofModeM ((Lean.Expr × Lean.Expr × Lean.Expr) × List Lean.Expr) := do
  let some (r, K, _) ← reshapeExpr e fun _ e' => do
      let (``expr.CmpXchg, #[a0, a1, a2]) := e'.consumeMData.getAppFnArgs | failure
      let some l := matchLocVal? a0 | failure
      let some v1 := isValExpr? a1 | failure
      let some v2 := isValExpr? a2 | failure
      return (l, v1, v2)
    | throwError "wp_cmpxchg: cannot find 'CmpXchg' in {e}"
  return (r, K)

/-- Rocq: `wp_cmpxchg_fail`. -/
elab (priority := high) "wp_cmpxchg_fail" : tactic =>
  runTacticHeapGwp `wp_cmpxchg_fail ``GwpTacticsAtomicConcurrency fun mvar g => do
    let ((l, v1, v2), K) ← findCmpXchg g.e
    let dq ← mkFreshExprMVar (mkConst ``DFrac)
    let v ← mkFreshExprMVar (mkConst ``val)
    let p ← mkFreshExprMVar (mkConst ``Bool)
    let pat ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, dq, v]
    let ⟨_, _, e'', _, pfSplit⟩ ← lookupHyp g.hyps' pat p
    let dq ← instantiateMVars dq
    let v ← instantiateMVars v
    let p ← instantiateMVars p
    let hne ← gwpSolveSide (← mkAppM ``Ne #[v, v1]) false
    let hsafe ← gwpSolveSide (← mkAppM ``vals_compare_safe #[v, v1]) false
    let pfCont ← gwpFinish g.hyps' g.w (← gwpFill K (mkValE (mkPairBoolV v false)))
    mvar.assign (← mkAppOptM ``tac_wp_cmpxchg_fail #[g.w.GF, g.w.A, g.w.gwp, g.laters, none,
      g.inst, g.ehyps, g.ehyps', e'', p, g.w.E, quoteList K, l, dq, v, v1, v2, g.w.Φ, g.w.a,
      g.pfLater, pfSplit, hne, hsafe, pfCont])

/-- Rocq: `wp_cmpxchg_suc`. -/
elab (priority := high) "wp_cmpxchg_suc" : tactic =>
  runTacticHeapGwp `wp_cmpxchg_suc ``GwpTacticsAtomicConcurrency fun mvar g => do
    let ((l, v1, v2), K) ← findCmpXchg g.e
    let own1 ← dfracOwnOne
    let v ← mkFreshExprMVar (mkConst ``val)
    let pat ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, v]
    let ⟨name, vid, e'', hyps'', pfSplit⟩ ← lookupHyp g.hyps' pat (mkConst ``false)
    let v ← instantiateMVars v
    let heq ← gwpSolveSide (← mkEq v v1) false
    let hsafe ← gwpSolveSide (← mkAppM ``vals_compare_safe #[v, v1]) false
    let P' ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, v2]
    let pfCont ← readdAndFinish hyps'' name vid P' g.w (← gwpFill K (mkValE (mkPairBoolV v true)))
    mvar.assign (← mkAppOptM ``tac_wp_cmpxchg_suc #[g.w.GF, g.w.A, g.w.gwp, g.laters, none,
      g.inst, g.ehyps, g.ehyps', e'', g.w.E, quoteList K, l, v, v1, v2, g.w.Φ, g.w.a, g.pfLater,
      pfSplit, heq, hsafe, pfCont])

/-- Rocq: `wp_cmpxchg as H1 | H2`. Case on `v = v1`, with the hypotheses `h1 : v = v1` in the
first and `h2 : v ≠ v1` in the second goal. -/
elab (priority := high) "wp_cmpxchg" " as " h1:ident " | " h2:ident : tactic =>
  runTacticHeapGwp `wp_cmpxchg ``GwpTacticsAtomicConcurrency fun mvar g => do
    let ((l, v1, v2), K) ← findCmpXchg g.e
    let own1 ← dfracOwnOne
    let v ← mkFreshExprMVar (mkConst ``val)
    let pat ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, v]
    let ⟨name, vid, e'', hyps'', pfSplit⟩ ← lookupHyp g.hyps' pat (mkConst ``false)
    let v ← instantiateMVars v
    let hsafe ← gwpSolveSide (← mkAppM ``vals_compare_safe #[v, v1]) false
    let P' ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, v2]
    let pfSuc ← withLocalDeclD h1.getId (← mkEq v v1) fun h => do
      let pf ← readdAndFinish hyps'' name vid P' g.w (← gwpFill K (mkValE (mkPairBoolV v true)))
      mkLambdaFVars #[h] pf
    let pfFail ← withLocalDeclD h2.getId (← mkAppM ``Ne #[v, v1]) fun h => do
      let pf ← gwpFinish g.hyps' g.w (← gwpFill K (mkValE (mkPairBoolV v false)))
      mkLambdaFVars #[h] pf
    mvar.assign (← mkAppOptM ``tac_wp_cmpxchg #[g.w.GF, g.w.A, g.w.gwp, g.laters, none,
      g.inst, g.ehyps, g.ehyps', e'', g.w.E, quoteList K, l, v, v1, v2, g.w.Φ, g.w.a, g.pfLater,
      pfSplit, hsafe, pfSuc, pfFail])

/-- Rocq: `wp_xchg`. -/
elab (priority := high) "wp_xchg" : tactic => do
  runTacticHeapGwp `wp_xchg ``GwpTacticsAtomicConcurrency fun mvar g => do
    let some ((l, v'), K, _) ← reshapeExpr g.e fun _ e' => do
        let (``expr.Xchg, #[a1, a2]) := e'.consumeMData.getAppFnArgs | failure
        let some l := matchLocVal? a1 | failure
        let some v' := isValExpr? a2 | failure
        return (l, v')
      | throwError "wp_xchg: cannot find 'Xchg' in {g.e}"
    let own1 ← dfracOwnOne
    let v ← mkFreshExprMVar (mkConst ``val)
    let pat ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, v]
    let ⟨name, vid, e'', hyps'', pfSplit⟩ ← lookupHyp g.hyps' pat (mkConst ``false)
    let v ← instantiateMVars v
    let P' ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, v']
    let pfCont ← readdAndFinish hyps'' name vid P' g.w (← gwpFill K (mkValE v))
    mvar.assign (← mkAppOptM ``tac_wp_xchg #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
      g.ehyps, g.ehyps', e'', g.w.E, quoteList K, l, v, v', g.w.Φ, g.w.a, g.pfLater, pfSplit,
      pfCont])
  evalTactic (← `(tactic| try wp_seq))

/-- Rocq: `wp_faa`. -/
elab (priority := high) "wp_faa" : tactic =>
  runTacticHeapGwp `wp_faa ``GwpTacticsAtomicConcurrency fun mvar g => do
    let some ((l, z2), K, _) ← reshapeExpr g.e fun _ e' => do
        let (``expr.FAA, #[a1, a2]) := e'.consumeMData.getAppFnArgs | failure
        let some l := matchLocVal? a1 | failure
        let some z2 := matchIntVal? a2 | failure
        return (l, z2)
      | throwError "wp_faa: cannot find 'FAA' in {g.e}"
    let own1 ← dfracOwnOne
    let z1 ← mkFreshExprMVar (mkConst ``Int)
    let pat ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, mkIntV z1]
    let ⟨name, vid, e'', hyps'', pfSplit⟩ ← lookupHyp g.hyps' pat (mkConst ``false)
    let z1 ← instantiateMVars z1
    let z12 ← gwpValSimpDefEq (← mkAppM ``HAdd.hAdd #[z1, z2])
    let P' ← gwpField g ``GwpTacticsAtomicConcurrency.wptac_mapsto_conc #[l, own1, mkIntV z12]
    let pfCont ← readdAndFinish hyps'' name vid P' g.w (← gwpFill K (mkValE (mkIntV z1)))
    mvar.assign (← mkAppOptM ``tac_wp_faa #[g.w.GF, g.w.A, g.w.gwp, g.laters, none, g.inst,
      g.ehyps, g.ehyps', e'', g.w.E, quoteList K, l, z1, z2, g.w.Φ, g.w.a, g.pfLater, pfSplit,
      pfCont])

/-- Rocq: `wp_apply` (the core, without the post-processing). -/
elab (priority := high) "gwp_apply_raw" colGt pmt:pmTerm : tactic =>
  gwpApplyRaw `wp_apply false pmt

/-- Rocq: `wp_smart_apply` (the core, without the post-processing). -/
elab (priority := high) "gwp_smart_apply_raw" colGt pmt:pmTerm : tactic =>
  gwpApplyRaw `wp_smart_apply true pmt

/-- Strip a leading `▷` and simplify WP expressions in the goals an application produced (Rocq:
`try iNext; try wp_expr_simpl`). -/
macro (priority := high) "gwp_apply_post" : tactic =>
  `(tactic| ((try inext) <;> (try wp_expr_simp)))

/-- Rocq: `wp_apply lem` and `wp_apply lem as (x1 .. xn) "pat"`. `wp_apply t` poses the
proof-mode term `t`, whose conclusion must be a WP `gwp a E e' Ψ`, and applies it to the goal
`gwp a E e Φ` after binding an evaluation context `K` with `e = fill K e'`. `wp_apply t with
pats` introduces `pats` in the last Iris goal. -/
syntax (name := wpApplyTac) (priority := high) "wp_apply " colGt pmTerm
  (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| wp_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then `(tactic| focusLastIrisGoal (iintro $pats*))
      else `(tactic| skip)
    `(tactic| focus (((gwp_apply_raw $pmt) <;> gwp_apply_post); $t:tactic))

/-- Rocq: `wp_smart_apply lem`. Like `wp_apply`, but takes pure steps until the lemma
applies. -/
syntax (name := wpSmartApplyTac) (priority := high) "wp_smart_apply " colGt pmTerm
  (" with" (colGt ppSpace introPat)+)? : tactic

macro_rules
  | `(tactic| wp_smart_apply $pmt:pmTerm $[with $pats*]?) => do
    let t : TSyntax `tactic ←
      if let some pats := pats then `(tactic| focusLastIrisGoal (iintro $pats*))
      else `(tactic| skip)
    `(tactic| focus (((gwp_smart_apply_raw $pmt) <;> gwp_apply_post); $t:tactic))

/-! ### `awp_apply` -/

/-- Rocq: `iApply (wptac_wp_frame_wand with [SGoal $ SpecGoal GSpatial false [] Hs false]);
[iAccu| ..]` (the first half of the `tac_suc` of `awp_apply lem without Hs`). On a goal
`gwp a E e Φ`, frames the hypotheses `hs`: the new goal is
`gwp a E e (fun v => R -∗ Φ v)` where `R` is the separating conjunction of `hs`. -/
elab (priority := high) "gwp_frame_wand" hs:(ppSpace colGt frameIdent)* : tactic => do
  let pf ← runTacticGwp `awp_apply fun mvar {hyps, w, e, ..} => do
    let (inst, some laters) ← synthGwpClass w ``GwpTacticsFrameWand true
      | throwError "awp_apply: no instance of GwpTacticsFrameWand"
    let propTy ← whnf (← inferType w.Φ)
    let R ← mkFreshExprMVar propTy.bindingBody!
    let pf ← mkAppOptM ``wptac_wp_frame_wand
      #[w.GF, w.A, laters, w.gwp, inst, w.E, e, w.Φ, w.a, R]
    mvar.assign (← addBIGoal hyps (w.wp e))
    return pf
  let stx ← Term.exprToSyntax pf
  evalTactic (← `(tactic| iapply $stx:term $$ [$hs*]))
  -- Rocq: `iAccu` on the goal for the framed proposition `R` (a metavariable).
  evalTactic (← `(tactic| all_goals (try iaccu)))

/-- Rocq: `awp_apply lem without Hs` (without the trailing `iAuIntro`): for the evaluation
contexts `K` of the WP expression (in the order of `reshape_expr`), bind `K`, frame `hs` with
`gwp_frame_wand`, and apply `pmt`; the first `K` for which this succeeds is used. -/
public meta def awpApplyWithout (pmt : TSyntax `pmTerm) (hs : Array (TSyntax `frameIdent)) :
    TacticM Unit := do
  -- The candidate subexpressions `e'` (with `e = fill K e'`), outermost first.
  let cands ← IO.mkRef (#[] : Array Lean.Expr)
  let s ← saveState
  try
    runTacticGwp `awp_apply fun _ {e, ..} => do
      let _ ← reshapeExpr e fun _ e' => do
        cands.modify (·.push e')
        (throwError "next" : ProofModeM Unit)
      pure ()
  finally
    s.restore
  for e' in ← cands.get do
    let s ← saveState
    try
      let focus ← Term.exprToSyntax e'
      evalTactic (← `(tactic| wp_bind $focus))
      evalTactic (← `(tactic| gwp_frame_wand $hs*))
      evalTactic (← `(tactic| iapply $pmt))
      return
    catch _ =>
      s.restore
  throwError "awp_apply: cannot apply {pmt}"

elab (priority := high) "awp_apply_without_raw " pmt:pmTerm " without"
    hs:(ppSpace colGt frameIdent)+ :
    tactic =>
  awpApplyWithout pmt hs

/-- Rocq: `awp_apply lem`. Like `wp_apply t` (without the trailing `iNext`), and then
introduces the atomic update of the last goal with `iauintro` (Rocq: `iAuIntro`), leaving an
atomic accessor `atomic_acc` whose abort condition is the spatial context. -/
syntax (name := awpApplyTac) (priority := high) "awp_apply " colGt pmTerm : tactic

/-- Rocq: `awp_apply lem without "H1 .. Hn"`. Like `awp_apply t`, but first frames the
hypotheses `H1 .. Hn` (with `wptac_wp_frame_wand`), so that they are not part of the abort
condition of the atomic accessor and are given back after the atomic step. -/
syntax (name := awpApplyWithoutTac) (priority := high) "awp_apply " colGt pmTerm " without"
  (ppSpace colGt frameIdent)+ : tactic

macro_rules
  | `(tactic| awp_apply $pmt:pmTerm) =>
    `(tactic| focus ((gwp_apply_raw $pmt); focusLastIrisGoal iauintro))
  | `(tactic| awp_apply $pmt:pmTerm without $hs*) =>
    `(tactic| focus ((awp_apply_without_raw $pmt without $hs*); focusLastIrisGoal iauintro))

end meta_tactics
end Coneris
