module

public import Metrology.ConProbLang.Common.Locations
public import Metrology.ConProbLang.Common.ConEctxiLanguage
public import Mathlib.Data.Int.Bitwise
public import Mathlib.Tactic.DeriveCountable

/-!
# The concurrent probabilistic language `con_prob_lang`

Ported from clutch/theories/con_prob_lang/lang.v

`con_prob_lang` is `heap_lang` without prophecy variables, with tapes (`AllocTape`), uniform
sampling (`Rand`, optionally reading presampled values from a tape) and a no-op `Tick`.
Head steps are `Distr`-valued (`head_step : expr → state → Distr (expr × state × List expr)`),
the language is an instance of `conEctxiLanguage` (`con_prob_ectxi_lang`), and hence of
`conEctxLanguage` (`con_prob_ectx_lang`) and `conLanguage` (`con_prob_lang`).

## Design (and Rocq → Lean mapping)

* Everything inside the Rocq `Module con_prob_lang` lives in the namespace
  `ConProbLang.con_prob_lang`; downstream files should `open ConProbLang con_prob_lang`
  (Rocq: `Export con_prob_lang`). The concrete `to_val`, `of_val`, `head_step`, `state_step`,
  `get_active`, ... therefore do not clash with the generic `ConProbLang.to_val` etc. of
  `conLanguage` (Lean resolves the overload by type).
* Syntax: the inductives keep their Rocq names (`base_lit`, `un_op`, `bin_op`, `expr`, `val`,
  `ectx_item`) and so do the constructors (`Val`, `Var`, `Rec`, `App`, ..., `LitV`, `RecV`, ...,
  `LitInt`, `LitLoc`, `LitLbl`, ..., `AppLCtx`, ...). All constructors are `export`ed into
  `ConProbLang.con_prob_lang`, so `Val (LitV (LitInt 1))` works as in Rocq. `expr`/`val` are a
  `mutual` inductive, as in Rocq and in iris-lean's `HeapLang.Exp`/`Val`.
* `binder` (stdpp) is the inductive `ConProbLang.binder` with constructors `BAnon`, `BNamed`.
  Strings are `String`; the (missing in Mathlib) instance `Countable String` is provided here
  (`string_countable`).
* `of_val` is Rocq notation for `Val`; here `of_val` is an `abbrev` for `expr.Val` (with simp
  lemma `of_val_eq`); statements use `Val` directly.
* `Z` is `ℤ`, `Z.to_nat` is `Int.toNat`, `Z.lnot` is `Int.lnot`, `quot`/`rem` are
  `Int.tdiv`/`Int.tmod`, `Z.land`/`Z.lor`/`Z.lxor` are `Int.land`/`Int.lor`/`Int.xor`,
  `≪`/`≫` are Mathlib's `<<<`/`>>>` on `ℤ` (shift amount in `ℤ`, as `Z.shiftl`/`Z.shiftr`).
  `bool_decide P` is `decide P`.
* `lit_is_unboxed`, `val_is_unboxed`, `vals_compare_safe` are `Prop`s with `Decidable`
  instances, as in Rocq.
* `tape := { n : nat & list (fin (S n)) }` is the structure `tape` with fields `bound : ℕ`
  and `contents : List (Fin (bound + 1))`; Rocq's `(n; xs)` is `⟨n, xs⟩`.
* `state` is a structure with `heap : Std.ExtTreeMap Loc val` and
  `tapes : Std.ExtTreeMap Loc tape` (default comparator `compare` from `LinearOrder Loc`).
  `σ.(heap) !! l` is `σ.heap[l]?`, `<[l := v]> m` is `m.insert l v`, `dom m` membership is
  `l ∈ m`, `elements (dom m)` is `m.keys`, `{[l := v]}` is `(∅ : Std.ExtTreeMap _ _).insert l v`.
* Unions: `Std.ExtTreeMap`'s `∪` is RIGHT-biased (`(m₁ ∪ m₂)[k]? = m₂[k]?.or m₁[k]?`), while
  stdpp's is left-biased. Rocq's `m₁ ∪ m₂` is therefore written `m₂ ∪ m₁` here; in particular
  `state_upd_heap_N l n v σ` updates the heap with `fun h => h ∪ heap_array l (replicate n v)`
  (Rocq: `λ h, heap_array l (replicate n v) ∪ h`), and `heap_array l (v :: vs)` is
  `(heap_array (l +ₗ 1) vs).insert l v` (Rocq: `{[l := v]} ∪ heap_array (l +ₗ 1) vs`).
  `m₁ ##ₘ m₂` is `map_disjoint m₁ m₂` (defined below).
* `head_step` returns `Distr (expr × state × List expr)` (right-nested triple).
* `state_step σ α` matches on `σ.tapes[α]?` (Rocq: `if bool_decide (α ∈ dom σ.(tapes)) then
  let: (N; ns) := σ.(tapes) !!! α in ... else dzero`); `state_step_unfold` has the Rocq shape.
  Accordingly, `state_step_rel.AddTapeS` has the single hypothesis
  `σ.tapes[α]? = some ⟨N, ns⟩` (Rocq: `α ∈ dom σ.(tapes)` and `σ.(tapes) !!! α = (N; ns)`).
* `decomp_item`'s local `noval` is the top-level `decomp_noval`.
* The languages: `con_prob_ectxi_lang : conEctxiLanguage`,
  `con_prob_ectx_lang := con_ectxi_lang_ectx con_prob_ectxi_lang`,
  `con_prob_lang := con_ectxi_lang con_prob_ectxi_lang` (all in namespace `ConProbLang`).
  `cfg` (Rocq: top-level `list expr * state`) is `ConProbLang.con_prob_lang.cfg`
  (reducibly equal to `ConProbLang.cfg con_prob_lang`).
* `head_step_support_equiv_rel` gives the relational characterisation `head_step_rel` of the
  support; the Rocq `Hint Constructors head_step_rel : head_step` (+ the `Hint Extern`s choosing
  `0` for `Rand`) is the tactic `solve_head_step_rel`.

## Tactics
* `inv_head_step` (Rocq: `inv_head_step`): turns every hypothesis `0 < head_step e σ ρ`
  (or `head_step e σ ρ > 0`) into `head_step_rel` (destructing a variable `ρ` into a triple)
  and inverts it with `cases`. Unlike Rocq's version it does not simplify map lookups
  afterwards; follow it by `simp_all` if needed.
* `solve_head_step_rel`: proves `head_step_rel e σ ?e' ?σ' ?efs` goals by trying the
  constructors (with `0` for the sampled value of `Rand`), discharging side conditions by
  `rfl`/`assumption`/`simp_all`.
* `solve_head_step`: proves `0 < head_step e σ (e', σ', efs)` via
  `head_step_support_equiv_rel` and `solve_head_step_rel`.
* `solve_red` (Rocq: `solve_red` of `con_prob_lang/tactics.v`, restricted to its non-Iris
  cases): proves `reducible (Λ := con_prob_lang) e σ` / `head_reducible e σ` goals.
* `solve_distr`, `inv_distr`, `solve_distr_mass` are provided by `Metrology.Prob.Distribution`.

## Scheduler section
* In `sch_typeclasses`, configurations are typed as `(con_lang_mdp con_prob_lang).mdpstate`
  (equal to `cfg` only at default transparency), thread ids as
  `(con_lang_mdp con_prob_lang).mdpaction` and values as `.mdpstate_ret`, so that all terms are
  well-typed at reducible transparency (needed by `simp`/`rw`). The test `tid < length ρ.1`
  inside `non_stutter_step'`/`non_stutter_step_prefix` is written `thread_lt tid ρ`
  (`thread_lt_iff : thread_lt tid ρ ↔ tid < ρ.1.length`). `NonStuttering` keeps the Rocq form.
* `λ '(sch_σ', tid), ...` is written with projections `q.1`, `q.2`.

## Added helpers (not in Rocq)
`map_getElem?_insert`, `map_getElem?_insert_ne`, `map_insert_insert`, `map_insert_id`,
`map_mem_iff`, `map_getElem?_union` (on `Std.ExtTreeMap Loc _`), `to_val_Val`,
`to_val_eq_none_iff`, `to_val_eq_some_iff`, `of_val_eq`, `state.ext'`, `subst'_BAnon`,
`subst'_BNamed`, simp lemmas `state_upd_heap_heap/_tapes`, `state_upd_tapes_heap'/_tapes`,
`heap_array_nil/_cons`, `decomp_noval_of_to_val`, `decomp_noval_eq_some`, `dunifv_zero`,
`dunifv_succ`, `CmpXchgS_true/_false`, `head_step_support_equiv_rel_1/_2` (the two directions),
`rand_lbl_head_step_rel`, `head_step_reducible_transfer`, `head_reducible_of_rel`,
`reducible_of_rel`, `fill` (= `conEctxiLanguage.fill` for `con_prob_ectxi_lang`), instances
`con_prob_lang_ctx_item`/`con_prob_lang_ctx` (Rocq finds these through canonical structures),
rfl lemmas `con_prob_lang_{expr,val,state,state_idx,to_val,of_val,state_step,get_active}`,
`con_prob_ectx_lang_head_step`, `non_stutter_step'_succ`, `non_stutter_scheduler_apply`,
`con_lang_mdp_step_stutter`.
Order: `head_ctx_step_val` is stated after `head_step_support_equiv_rel` (its proof uses
`inv_head_step`), and `fill_item_no_val_inj` after `decomp_fill_item` (it is derived from it).

## Omissions
* `Delimit Scope`/`Bind Scope`, `Global Arguments`, the canonical OFEs `stateO`, `locO`, `valO`,
  `exprO` (Lean uses discrete OFEs at use sites), `tapes_lookup_total` / `tapes_insert`
  (Lean uses `Std.ExtTreeMap`'s own `[·]?`/`insert`), `tape_countable` in Rocq is
  (mis-)stated as `EqDecision`; here a real `Countable tape` instance is given.
* `expr_ord_wf'` (the Rocq helper with an explicit fuel `h`) is replaced by the direct proof
  `expr_ord_wf` via `InvImage` of `<` on `ℕ`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

/-! ## Preliminaries: strings and binders -/

/-- `Countable String` (Rocq: `string_countable` from stdpp). -/
instance string_countable : Countable String := by
  refine Function.Injective.countable (f := fun s : String => s.toList.map Char.toNat) ?_
  intro s t h
  have : s.toList = t.toList :=
    List.map_injective_iff.2 (fun a b h => Char.toNat_inj.1 h) h
  exact String.toList_inj.1 this

/-- Rocq (stdpp): `binder`. -/
inductive binder where
  | BAnon
  | BNamed (s : String)
deriving DecidableEq, Inhabited, Repr, Countable

export binder (BAnon BNamed)

/-! ## Generic helpers on `Std.ExtTreeMap Loc _` -/

section map_helpers

variable {V : Type*}

theorem map_getElem?_insert (m : Std.ExtTreeMap Loc V) (k a : Loc) (v : V) :
    (m.insert k v)[a]? = if k = a then some v else m[a]? := by
  rw [Std.ExtTreeMap.getElem?_insert]
  simp only [compare_eq_iff_eq]

@[simp] theorem map_getElem?_insert_ne (m : Std.ExtTreeMap Loc V) (k a : Loc) (v : V)
    (h : k ≠ a) : (m.insert k v)[a]? = m[a]? := by
  rw [map_getElem?_insert, ite_eq_right_iff.2 (fun h' => absurd h' h)]

theorem map_insert_insert (m : Std.ExtTreeMap Loc V) (k : Loc) (v w : V) :
    (m.insert k v).insert k w = m.insert k w := by
  ext a : 1
  simp only [map_getElem?_insert]
  split <;> rfl

theorem map_insert_id (m : Std.ExtTreeMap Loc V) (k : Loc) (v : V) (h : m[k]? = some v) :
    m.insert k v = m := by
  ext a : 1
  rw [map_getElem?_insert]
  split
  · subst_vars; exact h.symm
  · rfl

theorem map_mem_iff (m : Std.ExtTreeMap Loc V) (k : Loc) : k ∈ m ↔ ∃ v, m[k]? = some v := by
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]

theorem map_getElem?_union (m₁ m₂ : Std.ExtTreeMap Loc V) (k : Loc) :
    (m₁ ∪ m₂)[k]? = (m₂[k]?).or (m₁[k]?) := Std.ExtTreeMap.getElem?_union

end map_helpers

namespace con_prob_lang

/-! ## Syntax -/

/-- Rocq: `base_lit`. -/
inductive base_lit : Type where
  | LitInt (n : ℤ)
  | LitBool (b : Bool)
  | LitUnit
  | LitLoc (l : Loc)
  | LitLbl (l : Loc)
deriving DecidableEq, Repr, Countable

/-- Rocq: `un_op`. -/
inductive un_op : Type where
  | NegOp
  | MinusUnOp
deriving DecidableEq, Repr, Countable

/-- Rocq: `bin_op`. -/
inductive bin_op : Type where
  /- Arithmetic -/
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp
  /- Bitwise -/
  | AndOp | OrOp | XorOp
  /- Shifts -/
  | ShiftLOp | ShiftROp
  /- Relations -/
  | LeOp | LtOp | EqOp
  /- Pointer offset -/
  | OffsetOp
deriving DecidableEq, Repr, Countable

export base_lit (LitInt LitBool LitUnit LitLoc LitLbl)
export un_op (NegOp MinusUnOp)
export bin_op (PlusOp MinusOp MultOp QuotOp RemOp AndOp OrOp XorOp ShiftLOp ShiftROp LeOp LtOp
  EqOp OffsetOp)

mutual
/-- Rocq: `expr`. -/
inductive expr : Type where
  /- Values -/
  | Val (v : val)
  /- Base lambda calculus -/
  | Var (x : String)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  /- Base types and their operations -/
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  /- Products -/
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  /- Sums -/
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 e1 e2 : expr)
  /- Heap -/
  | AllocN (e1 e2 : expr) /- Array length and initial value -/
  | Load (e : expr)
  | Store (e1 e2 : expr)
  /- Probabilistic choice -/
  | AllocTape (e : expr)
  | Rand (e1 e2 : expr)
  /- No-op operator used for cost -/
  | Tick (e : expr)
  /- Concurrency -/
  | Fork (e : expr)
  /- Arbitrary atomic expressions -/
  | CmpXchg (e0 e1 e2 : expr)
  | Xchg (e0 e1 : expr)
  | FAA (e1 e2 : expr)
/-- Rocq: `val`. -/
inductive val : Type where
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
end

export expr (Val Var Rec App UnOp BinOp If Pair Fst Snd InjL InjR Case AllocN Load Store
  AllocTape Rand Tick Fork CmpXchg Xchg FAA)
export val (LitV RecV PairV InjLV InjRV)

/-- Rocq: `of_val` (a notation for `Val` in Rocq). -/
abbrev of_val : val → expr := expr.Val

@[simp] theorem of_val_eq (v : val) : of_val v = Val v := rfl

/-- Rocq: `to_val`. -/
def to_val (e : expr) : Option val :=
  match e with
  | Val v => some v
  | _ => none

@[simp] theorem to_val_Val (v : val) : to_val (Val v) = some v := rfl

theorem to_val_eq_none_iff (e : expr) : to_val e = none ↔ ∀ v, e ≠ Val v := by
  cases e <;> simp [to_val]

theorem to_val_eq_some_iff (e : expr) (v : val) : to_val e = some v ↔ e = Val v := by
  cases e <;> simp [to_val]

/-! We assume the following encoding of values to 64-bit words: see the Rocq file. Every value
is machine-word-sized and can hence be atomically read and written; the sets of boxed and
unboxed values are disjoint. -/

/-- Rocq: `lit_is_unboxed`. -/
def lit_is_unboxed (l : base_lit) : Prop :=
  match l with
  | LitInt _ | LitBool _ | LitLoc _ | LitLbl _ | LitUnit => True

/-- Rocq: `val_is_unboxed`. -/
def val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False

/-- Rocq: `lit_is_unboxed_dec`. -/
instance lit_is_unboxed_dec (l : base_lit) : Decidable (lit_is_unboxed l) := by
  unfold lit_is_unboxed; split <;> infer_instance

/-- Rocq: `val_is_unboxed_dec`. -/
instance val_is_unboxed_dec (v : val) : Decidable (val_is_unboxed v) := by
  unfold val_is_unboxed; split <;> infer_instance

/-- Rocq: `vals_compare_safe`. We just compare the word-sized representation of two values,
without looking into boxed data. This works out fine if at least one of the to-be-compared
values is unboxed. -/
def vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1

instance vals_compare_safe_dec (vl v1 : val) : Decidable (vals_compare_safe vl v1) := by
  unfold vals_compare_safe; infer_instance

/-- Rocq: `tape := { n : nat & list (fin (S n)) }`. -/
structure tape where
  bound : ℕ
  contents : List (Fin (bound + 1))
deriving DecidableEq

/-- `tape ≃ Σ n, List (Fin (n + 1))`. -/
def tape.equivSigma : tape ≃ Σ n : ℕ, List (Fin (n + 1)) where
  toFun t := ⟨t.bound, t.contents⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Rocq: `tape_inhabited`. -/
instance tape_inhabited : Inhabited tape := ⟨⟨0, []⟩⟩

/-- Rocq: `tape_eq_dec`. -/
instance tape_eq_dec : DecidableEq tape := inferInstance

/-- Rocq: `tape_countable`. -/
instance tape_countable : Countable tape :=
  Function.Injective.countable tape.equivSigma.injective

/-- Rocq: `state`. The state: a `Loc`-indexed heap of `val`s, and `Loc`-indexed tapes. -/
structure state : Type where
  heap : Std.ExtTreeMap Loc val
  tapes : Std.ExtTreeMap Loc tape

@[ext] theorem state.ext' {σ σ' : state} (h1 : σ.heap = σ'.heap) (h2 : σ.tapes = σ'.tapes) :
    σ = σ' := by
  cases σ; cases σ'; simp_all

/-! Equality and other typeclass stuff -/

/-- Rocq: `to_of_val`. -/
theorem to_of_val (v : val) : to_val (Val v) = some v := rfl

/-- Rocq: `of_to_val`. -/
theorem of_to_val (e : expr) (v : val) (h : to_val e = some v) : Val v = e :=
  ((to_val_eq_some_iff e v).1 h).symm

/-- Rocq: `of_val_inj`. -/
theorem of_val_inj : Function.Injective expr.Val := fun _ _ h => by cases h; rfl

/-- Rocq: `base_lit_eq_dec`. -/
instance base_lit_eq_dec : DecidableEq base_lit := inferInstance
/-- Rocq: `un_op_eq_dec`. -/
instance un_op_eq_dec : DecidableEq un_op := inferInstance
/-- Rocq: `bin_op_eq_dec`. -/
instance bin_op_eq_dec : DecidableEq bin_op := inferInstance

deriving instance DecidableEq for expr, val

/-- Rocq: `expr_eq_dec`. -/
instance expr_eq_dec : DecidableEq expr := inferInstance
/-- Rocq: `val_eq_dec`. -/
instance val_eq_dec : DecidableEq val := inferInstance

/-- Rocq: `state_eq_dec`. -/
instance state_eq_dec : DecidableEq state := fun σ σ' =>
  if h : σ.heap = σ'.heap ∧ σ.tapes = σ'.tapes then isTrue (state.ext' h.1 h.2)
  else isFalse (fun e => h ⟨congrArg state.heap e, congrArg state.tapes e⟩)

/-- Rocq: `base_lit_countable`. -/
instance base_lit_countable : Countable base_lit := inferInstance
/-- Rocq: `un_op_finite`. -/
instance un_op_finite : Countable un_op := inferInstance
/-- Rocq: `bin_op_countable`. -/
instance bin_op_countable : Countable bin_op := inferInstance

deriving instance Countable for expr

/-- Rocq: `expr_countable`. -/
instance expr_countable : Countable expr := inferInstance

/-- Rocq: `val_countable`. -/
instance val_countable : Countable val :=
  Function.Injective.countable of_val_inj

/-- Rocq: `state_countable`. -/
instance state_countable : Countable state := by
  refine Function.Injective.countable
    (f := fun σ : state => (σ.heap.toList, σ.tapes.toList)) ?_
  intro σ σ' h
  simp only [Prod.mk.injEq, Std.ExtTreeMap.toList_inj] at h
  exact state.ext' h.1 h.2

/-- Rocq: `state_inhabited`. -/
instance state_inhabited : Inhabited state := ⟨⟨∅, ∅⟩⟩
/-- Rocq: `val_inhabited`. -/
instance val_inhabited : Inhabited val := ⟨LitV LitUnit⟩
/-- Rocq: `expr_inhabited`. -/
instance expr_inhabited : Inhabited expr := ⟨Val default⟩

/-! ## Evaluation contexts -/

/-- Rocq: `ectx_item`. -/
inductive ectx_item : Type where
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 e2 : expr)
  | AllocNLCtx (v2 : val)
  | AllocNRCtx (e1 : expr)
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr)
  | AllocTapeCtx
  | RandLCtx (v2 : val)
  | RandRCtx (e1 : expr)
  | TickCtx
  | XchgLCtx (v2 : val)
  | XchgRCtx (e1 : expr)
  | CmpXchgLCtx (v1 v2 : val)
  | CmpXchgMCtx (e0 : expr) (v2 : val)
  | CmpXchgRCtx (e0 e1 : expr)
  | FaaLCtx (v2 : val)
  | FaaRCtx (e1 : expr)
deriving DecidableEq

export ectx_item (AppLCtx AppRCtx UnOpCtx BinOpLCtx BinOpRCtx IfCtx PairLCtx PairRCtx FstCtx
  SndCtx InjLCtx InjRCtx CaseCtx AllocNLCtx AllocNRCtx LoadCtx StoreLCtx StoreRCtx AllocTapeCtx
  RandLCtx RandRCtx TickCtx XchgLCtx XchgRCtx CmpXchgLCtx CmpXchgMCtx CmpXchgRCtx FaaLCtx FaaRCtx)

/-- Rocq: `fill_item`. -/
def fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (Val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocNLCtx v2 => AllocN e (Val v2)
  | AllocNRCtx e1 => AllocN e1 e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | AllocTapeCtx => AllocTape e
  | RandLCtx v2 => Rand e (Val v2)
  | RandRCtx e1 => Rand e1 e
  | TickCtx => Tick e
  | XchgLCtx v2 => Xchg e (Val v2)
  | XchgRCtx e1 => Xchg e1 e
  | CmpXchgLCtx v1 v2 => CmpXchg e (Val v1) (Val v2)
  | CmpXchgMCtx e0 v2 => CmpXchg e0 e (Val v2)
  | CmpXchgRCtx e0 e1 => CmpXchg e0 e1 e
  | FaaLCtx v2 => FAA e (Val v2)
  | FaaRCtx e1 => FAA e1 e

/-- The local `noval` of Rocq's `decomp_item`. -/
def decomp_noval (e : expr) (ei : ectx_item) : Option (ectx_item × expr) :=
  match e with
  | Val _ => none
  | _ => some (ei, e)

theorem decomp_noval_of_to_val (e : expr) (ei : ectx_item) (h : to_val e = none) :
    decomp_noval e ei = some (ei, e) := by
  cases e <;> simp_all [decomp_noval, to_val]

theorem decomp_noval_eq_some (e : expr) (ei ei' : ectx_item) (e' : expr)
    (h : decomp_noval e ei = some (ei', e')) : ei' = ei ∧ e' = e ∧ to_val e = none := by
  cases e <;> simp_all [decomp_noval, to_val]

/-- Rocq: `decomp_item`. -/
def decomp_item (e : expr) : Option (ectx_item × expr) :=
  match e with
  | App e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (AppLCtx v)
      | _ => some (AppRCtx e1, e2)
  | UnOp op e => decomp_noval e (UnOpCtx op)
  | BinOp op e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (BinOpLCtx op v)
      | _ => some (BinOpRCtx op e1, e2)
  | If e0 e1 e2 => decomp_noval e0 (IfCtx e1 e2)
  | Pair e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (PairLCtx v)
      | _ => some (PairRCtx e1, e2)
  | Fst e => decomp_noval e FstCtx
  | Snd e => decomp_noval e SndCtx
  | InjL e => decomp_noval e InjLCtx
  | InjR e => decomp_noval e InjRCtx
  | Case e0 e1 e2 => decomp_noval e0 (CaseCtx e1 e2)
  | AllocN e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (AllocNLCtx v)
      | _ => some (AllocNRCtx e1, e2)
  | Load e => decomp_noval e LoadCtx
  | Store e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (StoreLCtx v)
      | _ => some (StoreRCtx e1, e2)
  | AllocTape e => decomp_noval e AllocTapeCtx
  | Rand e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (RandLCtx v)
      | _ => some (RandRCtx e1, e2)
  | Tick e => decomp_noval e TickCtx
  | Fork _ => none
  | CmpXchg e0 e1 e2 =>
      match e2 with
      | Val v2 =>
          match e1 with
          | Val v1 => decomp_noval e0 (CmpXchgLCtx v1 v2)
          | _ => some (CmpXchgMCtx e0 v2, e1)
      | _ => some (CmpXchgRCtx e0 e1, e2)
  | Xchg e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (XchgLCtx v)
      | _ => some (XchgRCtx e1, e2)
  | FAA e1 e2 =>
      match e2 with
      | Val v => decomp_noval e1 (FaaLCtx v)
      | _ => some (FaaRCtx e1, e2)
  | _ => none

/-! ## Substitution -/

/-- Rocq: `subst`. -/
def subst (x : String) (v : val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if x = y then Val v else Var y
  | Rec f y e =>
     Rec f y <| if BNamed x ≠ f ∧ BNamed x ≠ y then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | AllocTape e => AllocTape (subst x v e)
  | Rand e1 e2 => Rand (subst x v e1) (subst x v e2)
  | Tick e => Tick (subst x v e)
  | Fork e => Fork (subst x v e)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | Xchg e1 e2 => Xchg (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)

/-- Rocq: `subst'`. -/
def subst' (mx : binder) (v : val) : expr → expr :=
  match mx with
  | BNamed x => subst x v
  | BAnon => fun x => x

@[simp] theorem subst'_BAnon (v : val) (e : expr) : subst' BAnon v e = e := rfl
@[simp] theorem subst'_BNamed (x : String) (v : val) (e : expr) :
    subst' (BNamed x) v e = subst x v e := rfl

/-! ## The stepping relation -/

/-- Rocq: `un_op_eval`. -/
def un_op_eval (op : un_op) (v : val) : Option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => some <| LitV <| LitBool (!b)
  | NegOp, LitV (LitInt z) => some <| LitV <| LitInt (Int.lnot z)
  | MinusUnOp, LitV (LitInt z) => some <| LitV <| LitInt (- z)
  | _, _ => none

/-- Rocq: `bin_op_eval_int`. -/
def bin_op_eval_int (op : bin_op) (n1 n2 : ℤ) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (Int.tdiv n1 n2)
  | RemOp => LitInt (Int.tmod n1 n2)
  | AndOp => LitInt (Int.land n1 n2)
  | OrOp => LitInt (Int.lor n1 n2)
  | XorOp => LitInt (Int.xor n1 n2)
  | ShiftLOp => LitInt (n1 <<< n2)
  | ShiftROp => LitInt (n1 >>> n2)
  | LeOp => LitBool (decide (n1 ≤ n2))
  | LtOp => LitBool (decide (n1 < n2))
  | EqOp => LitBool (decide (n1 = n2))
  | OffsetOp => LitInt (n1 + n2) /- Treat offsets as ints -/

/-- Rocq: `bin_op_eval_bool`. -/
def bin_op_eval_bool (op : bin_op) (b1 b2 : Bool) : Option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => none /- Arithmetic -/
  | AndOp => some (LitBool (b1 && b2))
  | OrOp => some (LitBool (b1 || b2))
  | XorOp => some (LitBool (Bool.xor b1 b2))
  | ShiftLOp | ShiftROp => none /- Shifts -/
  | LeOp | LtOp => none /- InEquality -/
  | EqOp => some (LitBool (decide (b1 = b2)))
  | OffsetOp => none

/-- Rocq: `bin_op_eval_loc`. -/
def bin_op_eval_loc (op : bin_op) (l1 : Loc) (v2 : base_lit) : Option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => some <| LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => some <| LitBool (decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => some <| LitBool (decide (l1 <ₗ l2))
  | _, _ => none

/-- Rocq: `bin_op_eval`. -/
def bin_op_eval (op : bin_op) (v1 v2 : val) : Option val :=
  if op = EqOp then
    if vals_compare_safe v1 v2 then
      some <| LitV <| LitBool <| decide (v1 = v2)
    else
      none
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => some <| LitV <| bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => none

/-- Rocq: `state_upd_heap`. -/
def state_upd_heap (f : Std.ExtTreeMap Loc val → Std.ExtTreeMap Loc val) (σ : state) : state :=
  { heap := f σ.heap, tapes := σ.tapes }

/-- Rocq: `state_upd_tapes`. -/
def state_upd_tapes (f : Std.ExtTreeMap Loc tape → Std.ExtTreeMap Loc tape) (σ : state) :
    state :=
  { heap := σ.heap, tapes := f σ.tapes }

@[simp] theorem state_upd_heap_heap (f) (σ : state) : (state_upd_heap f σ).heap = f σ.heap := rfl
@[simp] theorem state_upd_heap_tapes (f) (σ : state) : (state_upd_heap f σ).tapes = σ.tapes := rfl
@[simp] theorem state_upd_tapes_heap' (f) (σ : state) : (state_upd_tapes f σ).heap = σ.heap := rfl
@[simp] theorem state_upd_tapes_tapes (f) (σ : state) :
    (state_upd_tapes f σ).tapes = f σ.tapes := rfl

/-- Rocq: `state_upd_tapes_twice`. -/
theorem state_upd_tapes_twice (σ : state) (l : Loc) (n : ℕ) (xs ys : List (Fin (n + 1))) :
    state_upd_tapes (·.insert l ⟨n, ys⟩) (state_upd_tapes (·.insert l ⟨n, xs⟩) σ) =
      state_upd_tapes (·.insert l ⟨n, ys⟩) σ := by
  simp only [state_upd_tapes, map_insert_insert]

/-- Rocq: `state_upd_tapes_same`. -/
theorem state_upd_tapes_same (σ σ' : state) (l : Loc) (n : ℕ) (xs ys : List (Fin (n + 1)))
    (h : state_upd_tapes (·.insert l ⟨n, ys⟩) σ = state_upd_tapes (·.insert l ⟨n, xs⟩) σ') :
    xs = ys := by
  have := congrArg (fun σ => σ.tapes[l]?) h
  simp only [state_upd_tapes, Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq,
    tape.mk.injEq, heq_eq_eq, true_and] at this
  exact this.symm

/-- Rocq: `state_upd_tapes_no_change`. -/
theorem state_upd_tapes_no_change (σ : state) (l : Loc) (n : ℕ) (ys : List (Fin (n + 1)))
    (h : σ.tapes[l]? = some ⟨n, ys⟩) : state_upd_tapes (·.insert l ⟨n, ys⟩) σ = σ := by
  cases σ
  simp only [state_upd_tapes] at h ⊢
  rw [map_insert_id _ _ _ h]

/-- Rocq: `state_upd_tapes_same'`. -/
theorem state_upd_tapes_same' (σ σ' : state) (l : Loc) (n : ℕ) (xs : List (Fin (n + 1)))
    (x y : Fin (n + 1))
    (h : state_upd_tapes (·.insert l ⟨n, xs ++ [x]⟩) σ =
      state_upd_tapes (·.insert l ⟨n, xs ++ [y]⟩) σ') : x = y := by
  have := state_upd_tapes_same _ _ _ _ _ _ h
  simp only [List.append_cancel_left_eq, List.cons.injEq, and_true] at this
  exact this.symm

/-- Rocq: `state_upd_tapes_neq'`. -/
theorem state_upd_tapes_neq' (σ σ' : state) (l : Loc) (n : ℕ) (xs : List (Fin (n + 1)))
    (x y : Fin (n + 1)) (h : x ≠ y) :
    state_upd_tapes (·.insert l ⟨n, xs ++ [x]⟩) σ ≠
      state_upd_tapes (·.insert l ⟨n, xs ++ [y]⟩) σ' :=
  fun h' => h (state_upd_tapes_same' _ _ _ _ _ _ _ h')

/-- Rocq: `heap_array`. Rocq: `{[l := v]} ∪ heap_array (l +ₗ 1) vs'`. -/
def heap_array (l : Loc) : List val → Std.ExtTreeMap Loc val
  | [] => ∅
  | v :: vs' => (heap_array (l +ₗ 1) vs').insert l v

@[simp] theorem heap_array_nil (l : Loc) : heap_array l [] = ∅ := rfl
theorem heap_array_cons (l : Loc) (v : val) (vs : List val) :
    heap_array l (v :: vs) = (heap_array (l +ₗ 1) vs).insert l v := rfl

/-- Rocq: `heap_array_singleton`. -/
theorem heap_array_singleton (l : Loc) (v : val) :
    heap_array l [v] = (∅ : Std.ExtTreeMap Loc val).insert l v := rfl

/-- Rocq: `heap_array_lookup`. -/
theorem heap_array_lookup (l : Loc) (vs : List val) (v : val) (k : Loc) :
    (heap_array l vs)[k]? = some v ↔
      ∃ j : ℤ, 0 ≤ j ∧ k = l +ₗ j ∧ vs[j.toNat]? = some v := by
  induction vs generalizing l with
  | nil =>
    simp only [heap_array_nil, Std.ExtTreeMap.getElem?_empty, reduceCtorEq, List.getElem?_nil,
      and_false, exists_const]
  | cons v' vs ih =>
    rw [heap_array_cons, map_getElem?_insert]
    constructor
    · split
      · rename_i hlk
        intro h
        exact ⟨0, le_rfl, by simp [hlk], by simpa using h⟩
      · intro h
        obtain ⟨j, hj, rfl, hv⟩ := (ih _).1 h
        refine ⟨1 + j, by omega, by rw [loc_add_assoc], ?_⟩
        rw [show (1 + j).toNat = j.toNat + 1 by omega]
        simpa using hv
    · rintro ⟨j, hj, rfl, hv⟩
      by_cases hj0 : j = 0
      · subst hj0
        simp only [loc_add_0, ↓reduceIte]
        simpa using hv
      · have hne : ¬ (l = l +ₗ j) := by
          intro h
          have := congrArg Loc.loc_car h
          simp at this
          omega
        simp only [hne, ↓reduceIte]
        apply (ih _).2
        refine ⟨j - 1, by omega, by rw [loc_add_assoc]; congr 1; omega, ?_⟩
        rw [show j.toNat = (j - 1).toNat + 1 by omega] at hv
        simpa using hv

/-- Rocq: `m₁ ##ₘ m₂` (disjointness of finite maps). -/
def map_disjoint {V : Type*} (m₁ m₂ : Std.ExtTreeMap Loc V) : Prop :=
  ∀ k, k ∈ m₁ → k ∉ m₂

/-- Rocq: `heap_array_map_disjoint`. -/
theorem heap_array_map_disjoint (h : Std.ExtTreeMap Loc val) (l : Loc) (vs : List val)
    (Hdisj : ∀ i : ℤ, 0 ≤ i → i < vs.length → h[l +ₗ i]? = none) :
    map_disjoint (heap_array l vs) h := by
  intro k hk hk'
  obtain ⟨v, hv⟩ := (map_mem_iff _ _).1 hk
  obtain ⟨j, hj, rfl, hvj⟩ := (heap_array_lookup _ _ _ _).1 hv
  have hlt := (List.getElem?_eq_some_iff.1 hvj).1
  have := Hdisj j hj (by omega)
  obtain ⟨w, hw⟩ := (map_mem_iff _ _).1 hk'
  rw [this] at hw
  cases hw

/-- Rocq: `heap_array_app`. (Rocq: `heap_array l vs1 ∪ heap_array (l +ₗ length vs1) vs2`,
with a left-biased union; `Std.ExtTreeMap`'s `∪` is right-biased.) -/
theorem heap_array_app (l : Loc) (vs1 vs2 : List val) :
    heap_array l (vs1 ++ vs2) = heap_array (l +ₗ (vs1.length : ℤ)) vs2 ∪ heap_array l vs1 := by
  induction vs1 generalizing l with
  | nil =>
    ext k : 1
    simp [map_getElem?_union]
  | cons v vs1 ih =>
    rw [List.cons_append, heap_array_cons, heap_array_cons, ih]
    ext k : 1
    rw [map_getElem?_union, map_getElem?_insert, map_getElem?_insert, map_getElem?_union,
      loc_add_assoc]
    simp only [List.length_cons]
    split
    · simp
    · rw [show (1 + (vs1.length : ℤ)) = ((vs1.length + 1 : ℕ) : ℤ) by omega]

/-- Rocq: `state_upd_heap_N`. (Rocq: `λ h, heap_array l (replicate n v) ∪ h`.) -/
def state_upd_heap_N (l : Loc) (n : ℕ) (v : val) (σ : state) : state :=
  state_upd_heap (fun h => h ∪ heap_array l (List.replicate n v)) σ

/-- Rocq: `state_upd_heap_singleton`. -/
theorem state_upd_heap_singleton (l : Loc) (v : val) (σ : state) :
    state_upd_heap_N l 1 v σ = state_upd_heap (·.insert l v) σ := by
  cases σ
  simp only [state_upd_heap_N, state_upd_heap, state.mk.injEq, and_true]
  ext k : 1
  rw [map_getElem?_union, map_getElem?_insert, List.replicate_one, heap_array_singleton,
    map_getElem?_insert]
  split <;> simp

/-- Rocq: `state_upd_tapes_heap`. -/
theorem state_upd_tapes_heap (σ : state) (l1 l2 : Loc) (n : ℕ) (xs : List (Fin (n + 1)))
    (m : ℕ) (v : val) :
    state_upd_tapes (·.insert l2 ⟨n, xs⟩) (state_upd_heap_N l1 m v σ) =
      state_upd_heap_N l1 m v (state_upd_tapes (·.insert l2 ⟨n, xs⟩) σ) := rfl

/-- Rocq: `heap_array_replicate_S_end`. (Rocq: `heap_array l (replicate n v) ∪ {[l +ₗ n := v]}`;
the two maps are disjoint.) -/
theorem heap_array_replicate_S_end (l : Loc) (v : val) (n : ℕ) :
    heap_array l (List.replicate (n + 1) v) =
      (heap_array l (List.replicate n v)).insert (l +ₗ (n : ℤ)) v := by
  rw [List.replicate_succ', heap_array_app, List.length_replicate]
  ext k : 1
  rw [map_getElem?_union, heap_array_singleton, map_getElem?_insert, map_getElem?_insert]
  split
  · rcases h : (heap_array l (List.replicate n v))[k]? with _ | w
    · rfl
    · obtain ⟨j, -, -, hj⟩ := (heap_array_lookup _ _ _ _).1 h
      rw [List.getElem?_replicate] at hj
      split at hj <;> simp_all
  · simp

/-- Rocq: `head_step`. -/
def head_step (e1 : expr) (σ1 : state) : Distr (expr × state × List expr) :=
  match e1 with
  | Rec f x e =>
      dret (Val <| RecV f x e, σ1, [])
  | Pair (Val v1) (Val v2) =>
      dret (Val <| PairV v1 v2, σ1, [])
  | InjL (Val v) =>
      dret (Val <| InjLV v, σ1, [])
  | InjR (Val v) =>
      dret (Val <| InjRV v, σ1, [])
  | App (Val (RecV f x e1)) (Val v2) =>
      dret (subst' x v2 (subst' f (RecV f x e1) e1), σ1, [])
  | UnOp op (Val v) =>
      match un_op_eval op v with
      | some w => dret (Val w, σ1, [])
      | _ => dzero
  | BinOp op (Val v1) (Val v2) =>
      match bin_op_eval op v1 v2 with
      | some w => dret (Val w, σ1, [])
      | _ => dzero
  | If (Val (LitV (LitBool true))) e1 _ =>
      dret (e1, σ1, [])
  | If (Val (LitV (LitBool false))) _ e2 =>
      dret (e2, σ1, [])
  | Fst (Val (PairV v1 _)) =>
      dret (Val v1, σ1, [])
  | Snd (Val (PairV _ v2)) =>
      dret (Val v2, σ1, [])
  | Case (Val (InjLV v)) e1 _ =>
      dret (App e1 (Val v), σ1, [])
  | Case (Val (InjRV v)) _ e2 =>
      dret (App e2 (Val v), σ1, [])
  | AllocN (Val (LitV (LitInt N))) (Val v) =>
      let ℓ := fresh_loc σ1.heap
      if 0 < N.toNat then
        dret (Val <| LitV <| LitLoc ℓ, state_upd_heap_N ℓ N.toNat v σ1, [])
      else dzero
  | Load (Val (LitV (LitLoc l))) =>
      match σ1.heap[l]? with
      | some v => dret (Val v, σ1, [])
      | none => dzero
  | Store (Val (LitV (LitLoc l))) (Val w) =>
      match σ1.heap[l]? with
      | some _ => dret (Val <| LitV LitUnit, state_upd_heap (·.insert l w) σ1, [])
      | none => dzero
  /- Since our language only has integers, we use `Int.toNat`, which maps positive
     integers to the corresponding nat, and the rest to 0. We sample from
     `dunifP N = dunif (1 + N)` to avoid the case `dunif 0 = dzero`. -/
  /- Uniform sampling from [0, 1 , ..., N] -/
  | Rand (Val (LitV (LitInt N))) (Val (LitV LitUnit)) =>
      dmap (fun n : Fin _ => (Val <| LitV <| LitInt n, σ1, [])) (dunifP N.toNat)
  | AllocTape (Val (LitV (LitInt z))) =>
      let ι := fresh_loc σ1.tapes
      dret (Val <| LitV <| LitLbl ι, state_upd_tapes (·.insert ι ⟨z.toNat, []⟩) σ1, [])
  /- Labelled sampling, conditional on tape contents -/
  | Rand (Val (LitV (LitInt N))) (Val (LitV (LitLbl l))) =>
      match σ1.tapes[l]? with
      | some ⟨M, ns⟩ =>
          if M = N.toNat then
            match ns with
            | n :: ns =>
                /- the tape is non-empty so we consume the first number -/
                dret (Val <| LitV <| LitInt (n : ℕ), state_upd_tapes (·.insert l ⟨M, ns⟩) σ1, [])
            | [] =>
                /- the tape is allocated but empty, so we sample from [0, 1, ..., M] uniformly -/
                dmap (fun n : Fin _ => (Val <| LitV <| LitInt n, σ1, [])) (dunifP M)
          else
            /- bound did not match the bound of the tape -/
            dmap (fun n : Fin _ => (Val <| LitV <| LitInt n, σ1, [])) (dunifP N.toNat)
      | none => dzero
  | Tick (Val (LitV (LitInt _))) => dret (Val <| LitV <| LitUnit, σ1, [])
  | Fork e => dret (Val <| LitV <| LitUnit, σ1, [e])
  | CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2) =>
      match σ1.heap[l]? with
      | some v =>
          if vals_compare_safe v v1 then
            let b := decide (v = v1)
            dret (Val <| PairV v (LitV <| LitBool b),
                  (if b then state_upd_heap (·.insert l v2) σ1 else σ1), [])
          else dzero
      | none => dzero
  | Xchg (Val (LitV (LitLoc l))) (Val v2) =>
      match σ1.heap[l]? with
      | some v1 => dret (Val v1, state_upd_heap (·.insert l v2) σ1, [])
      | none => dzero
  | FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2))) =>
      match σ1.heap[l]? with
      | some (LitV (LitInt i1)) =>
          dret (Val <| LitV <| LitInt i1, state_upd_heap (·.insert l (LitV (LitInt (i1 + i2)))) σ1,
            [])
      | _ => dzero
  | _ => dzero

/-- Rocq: `state_step`. (Rocq: `if bool_decide (α ∈ dom σ1.(tapes)) then let: (N; ns) :=
σ1.(tapes) !!! α in ... else dzero`.) -/
def state_step (σ1 : state) (α : Loc) : Distr state :=
  match σ1.tapes[α]? with
  | some ⟨N, ns⟩ => dmap (fun n => state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ1) (dunifP N)
  | none => dzero

/-- Rocq: `state_step_unfold`. -/
theorem state_step_unfold (σ : state) (α : Loc) (N : ℕ) (ns : List (Fin (N + 1)))
    (h : σ.tapes[α]? = some ⟨N, ns⟩) :
    state_step σ α = dmap (fun n => state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ) (dunifP N) := by
  simp only [state_step, h]

/-- Helper (not in Rocq): `dunifv N 0 = dret []`. -/
theorem dunifv_zero (N : ℕ) : dunifv N 0 = dret [] := by
  ext v
  rw [dunifv_pmf, dret_pmf_unfold]
  simp [List.length_eq_zero_iff]

/-- Helper (not in Rocq): sampling a list of length `p + 1` is sampling a list of length `p`
and then one more element. -/
theorem dunifv_succ (N p : ℕ) :
    dunifv N (p + 1) = (dunifv N p ≫= fun v => dmap (fun n => v ++ [n]) (dunifP N)) := by
  ext w
  rw [dbind_unfold_pmf]
  rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
  · rw [dunifv_pmf, ite_eq_right_iff.2 (by simp)]
    symm
    refine ENNReal.tsum_eq_zero.2 fun v => ?_
    rw [dmap_elem_ne _ _ _ (by rintro ⟨n, -, h⟩; simp at h), mul_zero]
  · rw [List.concat_eq_append, tsum_eq_single w']
    · rw [dmap_elem_eq _ x _ _ (fun a b h => by simpa using h) rfl, dunifv_pmf, dunifv_pmf,
        dunifP_pmf]
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff]
      split
      · rw [pow_succ, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
          (Or.inr (by exact_mod_cast N.succ_ne_zero))]
      · rw [zero_mul]
    · intro v hv
      rw [dmap_elem_ne _ _ _, mul_zero]
      rintro ⟨n, -, h⟩
      have := (List.append_inj' h rfl).1
      exact hv this

/-- Rocq: `iterM_state_step_unfold`. -/
theorem iterM_state_step_unfold (σ : state) (N p : ℕ) (α : Loc) (xs : List (Fin (N + 1)))
    (h : σ.tapes[α]? = some ⟨N, xs⟩) :
    iterM p (fun σ1' => state_step σ1' α) σ =
      dmap (fun v => state_upd_tapes (·.insert α ⟨N, xs ++ v⟩) σ) (dunifv N p) := by
  induction p with
  | zero =>
    rw [iterM_O, dunifv_zero, dmap_dret, List.append_nil, state_upd_tapes_no_change _ _ _ _ h]
  | succ p ih =>
    have h1 : iterM 1 (fun σ1' => state_step σ1' α) = fun a => state_step a α := funext fun a => by
      rw [iterM_Sn]; exact dret_id_right _
    rw [iterM_plus, ih, h1]
    rw [dunifv_succ, dmap_dbind, dmap, ← dbind_assoc]
    refine dbind_ext_right _ _ _ fun v => ?_
    rw [dret_id_left, state_step_unfold _ _ N (xs ++ v)
      (by simp [state_upd_tapes]), dmap_comp]
    congr 1
    funext n
    simp only [Function.comp, state_upd_tapes_twice, List.append_assoc]

/-- Side conditions for `solve_head_step_rel`. -/
syntax "solve_head_step_rel_side" : tactic
macro_rules
  | `(tactic| solve_head_step_rel_side) => `(tactic| first
    | rfl | assumption | (simp_all; done) | omega)

/-! ## Basic properties about the language -/

/-- Rocq: `fill_item_inj` (an `Inj` instance in Rocq). -/
theorem fill_item_inj (Ki : ectx_item) : Function.Injective (fill_item Ki) := by
  intro e e' h
  cases Ki <;> simp_all [fill_item]

/-- Rocq: `fill_item_val`. -/
theorem fill_item_val (Ki : ectx_item) (e : expr) (h : ∃ v, to_val (fill_item Ki e) = some v) :
    ∃ v, to_val e = some v := by
  obtain ⟨v, hv⟩ := h
  cases Ki <;> simp [fill_item, to_val] at hv

/-- Rocq: `val_head_stuck`. -/
theorem val_head_stuck (e : expr) (σ : state) (ρ : expr × state × List expr)
    (h : 0 < head_step e σ ρ) : to_val e = none := by
  cases e with
  | Val v => simp [head_step] at h
  | _ => rfl

/-- Rocq: `head_step_rel`. A relational characterization of the support of `head_step` to make
it easier to do inversion and prove reducibility easier, c.f. `head_step_support_equiv_rel`. -/
inductive head_step_rel : expr → state → expr → state → List expr → Prop where
  | RecS (f x : binder) (e : expr) (σ : state) :
    head_step_rel (Rec f x e) σ (Val <| RecV f x e) σ []
  | PairS (v1 v2 : val) (σ : state) :
    head_step_rel (Pair (Val v1) (Val v2)) σ (Val <| PairV v1 v2) σ []
  | InjLS (v : val) (σ : state) :
    head_step_rel (InjL <| Val v) σ (Val <| InjLV v) σ []
  | InjRS (v : val) (σ : state) :
    head_step_rel (InjR <| Val v) σ (Val <| InjRV v) σ []
  | BetaS (f x : binder) (e1 : expr) (v2 : val) (e' : expr) (σ : state) :
    e' = subst' x v2 (subst' f (RecV f x e1) e1) →
    head_step_rel (App (Val <| RecV f x e1) (Val v2)) σ e' σ []
  | UnOpS (op : un_op) (v v' : val) (σ : state) :
    un_op_eval op v = some v' →
    head_step_rel (UnOp op (Val v)) σ (Val v') σ []
  | BinOpS (op : bin_op) (v1 v2 v' : val) (σ : state) :
    bin_op_eval op v1 v2 = some v' →
    head_step_rel (BinOp op (Val v1) (Val v2)) σ (Val v') σ []
  | IfTrueS (e1 e2 : expr) (σ : state) :
    head_step_rel (If (Val <| LitV <| LitBool true) e1 e2) σ e1 σ []
  | IfFalseS (e1 e2 : expr) (σ : state) :
    head_step_rel (If (Val <| LitV <| LitBool false) e1 e2) σ e2 σ []
  | FstS (v1 v2 : val) (σ : state) :
    head_step_rel (Fst (Val <| PairV v1 v2)) σ (Val v1) σ []
  | SndS (v1 v2 : val) (σ : state) :
    head_step_rel (Snd (Val <| PairV v1 v2)) σ (Val v2) σ []
  | CaseLS (v : val) (e1 e2 : expr) (σ : state) :
    head_step_rel (Case (Val <| InjLV v) e1 e2) σ (App e1 (Val v)) σ []
  | CaseRS (v : val) (e1 e2 : expr) (σ : state) :
    head_step_rel (Case (Val <| InjRV v) e1 e2) σ (App e2 (Val v)) σ []
  | AllocNS (z : ℤ) (N : ℕ) (v : val) (σ : state) (l : Loc) :
    l = fresh_loc σ.heap →
    N = z.toNat →
    0 < N →
    head_step_rel (AllocN (Val (LitV (LitInt z))) (Val v)) σ
      (Val <| LitV <| LitLoc l) (state_upd_heap_N l N v σ) []
  | LoadS (l : Loc) (v : val) (σ : state) :
    σ.heap[l]? = some v →
    head_step_rel (Load (Val <| LitV <| LitLoc l)) σ (Val v) σ []
  | StoreS (l : Loc) (v w : val) (σ : state) :
    σ.heap[l]? = some v →
    head_step_rel (Store (Val <| LitV <| LitLoc l) (Val w)) σ
      (Val <| LitV LitUnit) (state_upd_heap (·.insert l w) σ) []
  | RandNoTapeS (z : ℤ) (N : ℕ) (n : Fin (N + 1)) (σ : state) :
    N = z.toNat →
    head_step_rel (Rand (Val <| LitV <| LitInt z) (Val <| LitV LitUnit)) σ
      (Val <| LitV <| LitInt (n : ℕ)) σ []
  | AllocTapeS (z : ℤ) (N : ℕ) (σ : state) (l : Loc) :
    l = fresh_loc σ.tapes →
    N = z.toNat →
    head_step_rel (AllocTape (Val (LitV (LitInt z)))) σ
      (Val <| LitV <| LitLbl l) (state_upd_tapes (·.insert l ⟨N, []⟩) σ) []
  | RandTapeS (l : Loc) (z : ℤ) (N : ℕ) (n : Fin (N + 1)) (ns : List (Fin (N + 1)))
      (σ : state) :
    N = z.toNat →
    σ.tapes[l]? = some ⟨N, n :: ns⟩ →
    head_step_rel (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ
      (Val <| LitV <| LitInt (n : ℕ)) (state_upd_tapes (·.insert l ⟨N, ns⟩) σ) []
  | RandTapeEmptyS (l : Loc) (z : ℤ) (N : ℕ) (n : Fin (N + 1)) (σ : state) :
    N = z.toNat →
    σ.tapes[l]? = some ⟨N, []⟩ →
    head_step_rel (Rand (Val (LitV (LitInt z))) (Val <| LitV <| LitLbl l)) σ
      (Val <| LitV <| LitInt (n : ℕ)) σ []
  | RandTapeOtherS (l : Loc) (z : ℤ) (M N : ℕ) (ms : List (Fin (M + 1))) (n : Fin (N + 1))
      (σ : state) :
    N = z.toNat →
    σ.tapes[l]? = some ⟨M, ms⟩ →
    N ≠ M →
    head_step_rel (Rand (Val (LitV (LitInt z))) (Val <| LitV <| LitLbl l)) σ
      (Val <| LitV <| LitInt (n : ℕ)) σ []
  | TickS (σ : state) (z : ℤ) :
    head_step_rel (Tick <| Val <| LitV <| LitInt z) σ (Val <| LitV <| LitUnit) σ []
  | ForkS (e : expr) (σ : state) :
    head_step_rel (Fork e) σ (Val <| LitV <| LitUnit) σ [e]
  | CmpXchgS (σ : state) (l : Loc) (vl v1 v2 : val) (b : Bool) :
    σ.heap[l]? = some vl →
    vals_compare_safe vl v1 →
    b = decide (vl = v1) →
    head_step_rel (CmpXchg (Val <| LitV <| LitLoc l) (Val v1) (Val v2)) σ
      (Val <| PairV vl (LitV <| LitBool b))
      (if b then state_upd_heap (·.insert l v2) σ else σ) []
  | XchgS (σ : state) (l : Loc) (v1 v2 : val) :
    σ.heap[l]? = some v1 →
    head_step_rel (Xchg (Val <| LitV <| LitLoc l) (Val v2)) σ (Val v1)
      (state_upd_heap (·.insert l v2) σ) []
  | FAAS (σ : state) (l : Loc) (i1 i2 : ℤ) :
    σ.heap[l]? = some (LitV (LitInt i1)) →
    head_step_rel (FAA (Val <| LitV <| LitLoc l) (Val <| LitV <| LitInt i2)) σ
      (Val <| LitV <| LitInt i1) (state_upd_heap (·.insert l (LitV (LitInt (i1 + i2)))) σ) []

export head_step_rel (RecS PairS InjLS InjRS BetaS UnOpS BinOpS IfTrueS IfFalseS FstS SndS
  CaseLS CaseRS AllocNS LoadS StoreS RandNoTapeS AllocTapeS RandTapeS RandTapeEmptyS
  RandTapeOtherS TickS ForkS CmpXchgS XchgS FAAS)

theorem CmpXchgS_true (σ : state) (l : Loc) (vl v1 v2 : val) (h : σ.heap[l]? = some vl)
    (hs : vals_compare_safe vl v1) (hb : decide (vl = v1) = true) :
    head_step_rel (CmpXchg (Val <| LitV <| LitLoc l) (Val v1) (Val v2)) σ
      (Val <| PairV vl (LitV <| LitBool (decide (vl = v1))))
      (state_upd_heap (·.insert l v2) σ) [] := by
  have := CmpXchgS σ l vl v1 v2 _ h hs rfl
  simpa only [hb, ↓reduceIte] using this

theorem CmpXchgS_false (σ : state) (l : Loc) (vl v1 v2 : val) (h : σ.heap[l]? = some vl)
    (hs : vals_compare_safe vl v1) (hb : ¬ decide (vl = v1) = true) :
    head_step_rel (CmpXchg (Val <| LitV <| LitLoc l) (Val v1) (Val v2)) σ
      (Val <| PairV vl (LitV <| LitBool (decide (vl = v1)))) σ [] := by
  have := CmpXchgS σ l vl v1 v2 _ h hs rfl
  simpa only [hb, Bool.false_eq_true, ↓reduceIte] using this

/-- Rocq: `eauto with head_step` on `head_step_rel` goals (the `Hint Constructors head_step_rel`
and the `Hint Extern`s proposing `0` for the sampled value of `Rand`). Tries every constructor of
`head_step_rel`, closing the side conditions with `solve_head_step_rel_side`. -/
macro "solve_head_step_rel" : tactic => `(tactic| first
    | ((apply head_step_rel.RecS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.PairS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.InjLS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.InjRS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.BetaS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.UnOpS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.BinOpS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.IfTrueS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.IfFalseS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.FstS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.SndS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.CaseLS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.CaseRS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.AllocNS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.LoadS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.StoreS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.RandNoTapeS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.AllocTapeS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.RandTapeS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.RandTapeEmptyS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.RandTapeOtherS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.TickS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.ForkS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.CmpXchgS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.XchgS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply head_step_rel.FAAS <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply CmpXchgS_true <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩)
    | ((apply CmpXchgS_false <;> try solve_head_step_rel_side) <;> exact ⟨0, Nat.succ_pos _⟩))

/-- Rocq: `state_step_rel`. -/
inductive state_step_rel : state → Loc → state → Prop where
  | AddTapeS (α : Loc) (N : ℕ) (n : Fin (N + 1)) (ns : List (Fin (N + 1))) (σ : state) :
    σ.tapes[α]? = some ⟨N, ns⟩ →
    state_step_rel σ α (state_upd_tapes (·.insert α ⟨N, ns ++ [n]⟩) σ)

export state_step_rel (AddTapeS)

theorem head_step_support_equiv_rel_2 (e1 e2 : expr) (σ1 σ2 : state) (l : List expr)
    (h : head_step_rel e1 σ1 e2 σ2 l) : 0 < head_step e1 σ1 (e2, σ2, l) := by
  cases h <;> subst_vars <;> simp_all [head_step] <;>
    (try simp only [Ne.symm ‹¬ _ = _›, ↓reduceIte]) <;> solve_distr

theorem head_step_support_equiv_rel_1 (e1 e2 : expr) (σ1 σ2 : state) (l : List expr)
    (h : 0 < head_step e1 σ1 (e2, σ2, l)) : head_step_rel e1 σ1 e2 σ2 l := by
  unfold head_step at h
  split at h <;> (try dsimp only at h) <;> (repeat' split at h) <;> inv_distr <;>
    simp only [Prod.mk.injEq] at * <;> obtain ⟨rfl, rfl, rfl⟩ := ‹_ = _ ∧ _ = _ ∧ _ = _› <;>
    subst_vars <;> solve_head_step_rel

/-- Rocq: `head_step_support_equiv_rel`. -/
theorem head_step_support_equiv_rel (e1 e2 : expr) (σ1 σ2 : state) (l : List expr) :
    0 < head_step e1 σ1 (e2, σ2, l) ↔ head_step_rel e1 σ1 e2 σ2 l :=
  ⟨head_step_support_equiv_rel_1 e1 e2 σ1 σ2 l, head_step_support_equiv_rel_2 e1 e2 σ1 σ2 l⟩

section inv_head_step_tactic

open Lean Meta Elab Tactic

/-- Find a hypothesis `0 < head_step e σ ρ` (or `head_step e σ ρ > 0`); return it and `ρ`. -/
meta def findHeadStepPosHyp : TacticM (Option (FVarId × Expr)) := withMainContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let rhs? : Option Expr :=
      match ty.getAppFnArgs with
      | (``LT.lt, #[_, _, _, rhs]) => some rhs
      | (``GT.gt, #[_, _, lhs, _]) => some lhs
      | _ => none
    let some rhs := rhs? | continue
    let (``Distr.pmf, #[_, _, μ, ρ]) := rhs.getAppFnArgs | continue
    unless μ.getAppFn.constName? == some ``head_step do continue
    return some (ldecl.fvarId, ρ)
  return none

/-- One step of `inv_head_step`. -/
meta def invHeadStepStep : TacticM Bool := do
  let some (fv, ρ) ← findHeadStepPosHyp | return false
  -- destruct a variable triple first
  let ρ ← instantiateMVars ρ
  if ρ.isFVar then
    let gs ← (← getMainGoal).cases ρ.fvarId!
    replaceMainGoal (gs.map (·.mvarId)).toList
    return true
  if let (``Prod.mk, #[_, _, _, b]) := ρ.getAppFnArgs then
    if b.isFVar then
      let gs ← (← getMainGoal).cases b.fvarId!
      replaceMainGoal (gs.map (·.mvarId)).toList
      return true
  let n ← mkFreshUserName `h
  let g ← (← getMainGoal).rename fv n
  replaceMainGoal [g]
  let h := mkIdent n
  let h' := mkIdent (← mkFreshUserName `h)
  evalTactic (← `(tactic| have $h':ident := (head_step_support_equiv_rel _ _ _ _ _).1 $h))
  evalTactic (← `(tactic| clear $h:ident))
  evalTactic (← `(tactic| cases $h':ident))
  return true

/-- Rocq: `inv_head_step`. Inverts every hypothesis `0 < head_step e σ ρ` (or
`head_step e σ ρ > 0`): a variable `ρ` is destructed into a triple, the hypothesis is turned
into `head_step_rel` (`head_step_support_equiv_rel`) and inverted with `cases`. -/
elab "inv_head_step" : tactic => do
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    if (← getGoals).isEmpty then return
    unless ← invHeadStepStep do return

end inv_head_step_tactic

/-- Rocq: `solve_step`'s `head_step _ _ _ > 0` case (`eauto with head_step`): proves
`0 < head_step e σ (e', σ', efs)` via `head_step_support_equiv_rel`. -/
macro "solve_head_step" : tactic =>
  `(tactic| (change 0 < head_step _ _ (_, _, _)
             apply (head_step_support_equiv_rel _ _ _ _ _).2; solve_head_step_rel))

/-- Rocq: `head_ctx_step_val`. -/
theorem head_ctx_step_val (Ki : ectx_item) (e : expr) (σ : state) (ρ : expr × state × List expr)
    (h : 0 < head_step (fill_item Ki e) σ ρ) : ∃ v, to_val e = some v := by
  cases Ki <;> simp only [fill_item] at h <;> inv_head_step <;> simp

/-- Rocq: `state_step_support_equiv_rel`. -/
theorem state_step_support_equiv_rel (σ1 : state) (α : Loc) (σ2 : state) :
    0 < state_step σ1 α σ2 ↔ state_step_rel σ1 α σ2 := by
  constructor
  · intro h
    unfold state_step at h
    split at h
    · inv_distr
      exact AddTapeS _ _ _ _ _ ‹_›
    · inv_distr
  · rintro ⟨α, N, n, ns, σ, h⟩
    rw [state_step_unfold _ _ _ _ h]
    solve_distr

/-- Helper (not in Rocq): a labelled `Rand` on an allocated tape can always step. -/
theorem rand_lbl_head_step_rel (σ : state) (l : Loc) (z : ℤ) (t : tape)
    (h : σ.tapes[l]? = some t) :
    ∃ e2 σ2 efs, head_step_rel (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl l)))) σ e2 σ2 efs := by
  obtain ⟨M, ms⟩ := t
  by_cases hM : z.toNat = M
  · subst hM
    cases ms with
    | nil => exact ⟨_, _, _, RandTapeEmptyS l z _ 0 σ rfl h⟩
    | cons n ns => exact ⟨_, _, _, RandTapeS l z _ n ns σ rfl h⟩
  · exact ⟨_, _, _, RandTapeOtherS l z M _ ms 0 σ rfl h hM⟩

/-- Helper (not in Rocq): head reducibility only depends on the heap and on which tapes are
allocated. -/
theorem head_step_reducible_transfer (e : expr) (σ σ' : state) (hh : σ.heap = σ'.heap)
    (ht : ∀ (l : Loc) (t : tape), σ.tapes[l]? = some t → ∃ t', σ'.tapes[l]? = some t')
    (h : ∃ ρ, 0 < head_step e σ ρ) : ∃ ρ', 0 < head_step e σ' ρ' := by
  obtain ⟨ρ, h⟩ := h
  have key : ∀ e2 σ2 efs, head_step_rel e σ' e2 σ2 efs → ∃ ρ', 0 < head_step e σ' ρ' :=
    fun e2 σ2 efs hr => ⟨(e2, σ2, efs), (head_step_support_equiv_rel _ _ _ _ _).2 hr⟩
  inv_head_step
  all_goals first
    | (rw [hh] at *; exact key _ _ _ (by solve_head_step_rel))
    | (obtain ⟨t', ht'⟩ := ht _ _ (by assumption)
       obtain ⟨_, _, _, hr⟩ := rand_lbl_head_step_rel σ' _ _ t' ht'
       exact key _ _ _ hr)

/-- Rocq: `state_step_head_step_not_stuck`. -/
theorem state_step_head_step_not_stuck (e : expr) (σ σ' : state) (α : Loc)
    (h : 0 < state_step σ α σ') :
    (∃ ρ, 0 < head_step e σ ρ) ↔ (∃ ρ', 0 < head_step e σ' ρ') := by
  rw [state_step_support_equiv_rel] at h
  obtain ⟨α, N, n, ns, σ, hα⟩ := h
  constructor
  · refine head_step_reducible_transfer e _ _ rfl fun l t hl => ?_
    simp only [state_upd_tapes_tapes, map_getElem?_insert]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨t, hl⟩
  · refine head_step_reducible_transfer e _ _ rfl fun l t hl => ?_
    simp only [state_upd_tapes_tapes, map_getElem?_insert] at hl
    split at hl
    · subst_vars; exact ⟨_, hα⟩
    · exact ⟨t, hl⟩

/-- Rocq: `state_step_mass`. -/
theorem state_step_mass (σ : state) (α : Loc) (h : α ∈ σ.tapes) :
    ∑' σ', state_step σ α σ' = 1 := by
  obtain ⟨⟨N, ns⟩, ht⟩ := (map_mem_iff _ _).1 h
  rw [state_step_unfold _ _ _ _ ht, dmap_mass, dunifP_mass]

/-- Rocq: `head_step_mass`. -/
theorem head_step_mass (e : expr) (σ : state) (h : ∃ ρ, 0 < head_step e σ ρ) :
    ∑' ρ, head_step e σ ρ = 1 := by
  obtain ⟨ρ, h⟩ := h
  inv_head_step <;> subst_vars <;> simp_all [head_step] <;>
    (try simp only [Ne.symm ‹¬ _ = _›, ↓reduceIte]) <;>
    first
    | solve_distr_mass
    | simp only [dmap_mass, dunifP_mass]
    | exact ENNReal.mul_inv_cancel (by positivity) (by simp)

/-- Rocq: `height`. -/
def height (e : expr) : ℕ :=
  match e with
  | Val _ => 1
  | Var _ => 1
  | Rec _ _ e => 1 + height e
  | App e1 e2 => 1 + height e1 + height e2
  | UnOp _ e => 1 + height e
  | BinOp _ e1 e2 => 1 + height e1 + height e2
  | If e0 e1 e2 => 1 + height e0 + height e1 + height e2
  | Pair e1 e2 => 1 + height e1 + height e2
  | Fst e => 1 + height e
  | Snd e => 1 + height e
  | InjL e => 1 + height e
  | InjR e => 1 + height e
  | Case e0 e1 e2 => 1 + height e0 + height e1 + height e2
  | AllocN e1 e2 => 1 + height e1 + height e2
  | Load e => 1 + height e
  | Store e1 e2 => 1 + height e1 + height e2
  | AllocTape e => 1 + height e
  | Rand e1 e2 => 1 + height e1 + height e2
  | Tick e => 1 + height e
  | Fork e => 1 + height e
  | CmpXchg e0 e1 e2 => 1 + height e0 + height e1 + height e2
  | Xchg e1 e2 => 1 + height e1 + height e2
  | FAA e1 e2 => 1 + height e1 + height e2

/-- Rocq: `expr_ord`. -/
def expr_ord (e1 e2 : expr) : Prop := height e1 < height e2

/-- Rocq: `expr_ord_wf` (Rocq proves it via the helper `expr_ord_wf'`). -/
theorem expr_ord_wf : WellFounded expr_ord := InvImage.wf height wellFounded_lt

/-- Rocq: `decomp_fill_item`. -/
theorem decomp_fill_item (Ki : ectx_item) (e : expr) (h : to_val e = none) :
    decomp_item (fill_item Ki e) = some (Ki, e) := by
  have hv := (to_val_eq_none_iff e).1 h
  cases Ki <;> simp only [fill_item, decomp_item] <;> simp_all [decomp_noval_of_to_val]

/-- Rocq: `decomp_fill_item_2`. -/
theorem decomp_fill_item_2 (e e' : expr) (Ki : ectx_item) (h : decomp_item e = some (Ki, e')) :
    fill_item Ki e' = e ∧ to_val e' = none := by
  cases e <;> simp only [decomp_item] at h <;> (repeat' split at h) <;>
    first
    | (obtain ⟨rfl, rfl, hv⟩ := decomp_noval_eq_some _ _ _ _ h; exact ⟨rfl, hv⟩)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       refine ⟨rfl, (to_val_eq_none_iff _).2 ?_⟩
       rintro v rfl
       simp_all)
    | cases h

/-- Rocq: `decomp_expr_ord`. -/
theorem decomp_expr_ord (Ki : ectx_item) (e e' : expr) (h : decomp_item e = some (Ki, e')) :
    expr_ord e' e := by
  obtain ⟨rfl, -⟩ := decomp_fill_item_2 _ _ _ h
  unfold expr_ord
  cases Ki <;> simp only [fill_item, height] <;> omega

/-- Rocq: `fill_item_no_val_inj`. -/
theorem fill_item_no_val_inj (Ki1 Ki2 : ectx_item) (e1 e2 : expr) (h1 : to_val e1 = none)
    (h2 : to_val e2 = none) (h : fill_item Ki1 e1 = fill_item Ki2 e2) : Ki1 = Ki2 := by
  have := decomp_fill_item Ki1 e1 h1
  rw [h, decomp_fill_item Ki2 e2 h2] at this
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this.1.symm

/-- Rocq: `get_active`. -/
def get_active (σ : state) : List Loc := σ.tapes.keys

/-- Rocq: `state_step_get_active_mass`. -/
theorem state_step_get_active_mass (σ : state) (α : Loc) (h : α ∈ get_active σ) :
    ∑' σ', state_step σ α σ' = 1 :=
  state_step_mass σ α (Std.ExtTreeMap.mem_keys.1 h)

/-- Rocq: `state_steps_mass`. -/
theorem state_steps_mass (σ : state) (αs : List Loc) (h : αs ⊆ get_active σ) :
    ∑' σ', foldlM state_step σ αs σ' = 1 := by
  induction αs generalizing σ with
  | nil => simp
  | cons α αs ih =>
    rw [foldlM_cons]
    refine dbind_det _ _ (state_step_get_active_mass _ _ (h List.mem_cons_self)) ?_
    intro σ' hσ'
    apply ih
    rw [state_step_support_equiv_rel] at hσ'
    obtain ⟨α, N, n, ns, σ, hα⟩ := hσ'
    intro α' hα'
    have := h (List.mem_cons_of_mem _ hα')
    simp only [get_active, Std.ExtTreeMap.mem_keys, state_upd_tapes_tapes,
      Std.ExtTreeMap.mem_insert] at this ⊢
    exact Or.inr this

/-- Rocq: `con_prob_lang_mixin`. -/
theorem con_prob_lang_mixin :
    ConEctxiLanguageMixin expr.Val to_val fill_item decomp_item expr_ord head_step state_step
      get_active where
  mixin_to_of_val := to_of_val
  mixin_of_to_val := of_to_val
  mixin_val_stuck := val_head_stuck
  mixin_state_step_head_not_stuck := state_step_head_step_not_stuck
  mixin_state_step_mass := state_step_get_active_mass
  mixin_head_step_mass := head_step_mass
  mixin_fill_item_val := fill_item_val
  mixin_fill_item_inj := fill_item_inj
  mixin_fill_item_no_val_inj := fill_item_no_val_inj
  mixin_expr_ord_wf := expr_ord_wf
  mixin_decomp_ord := decomp_expr_ord
  mixin_decomp_fill_item Ki e h := decomp_fill_item Ki e h
  mixin_decomp_fill_item_2 := decomp_fill_item_2
  mixin_head_ctx_step_val := head_ctx_step_val

end con_prob_lang

/-! ## Language -/

open con_prob_lang in
/-- Rocq: `con_prob_ectxi_lang` (a `Canonical Structure`). -/
abbrev con_prob_ectxi_lang : conEctxiLanguage where
  expr := expr
  val := val
  ectx_item := ectx_item
  state := state
  state_idx := Loc
  expr_eqdec := inferInstance
  val_eqdec := inferInstance
  state_eqdec := inferInstance
  state_idx_eqdec := inferInstance
  expr_countable := inferInstance
  val_countable := inferInstance
  state_countable := inferInstance
  state_idx_countable := inferInstance
  of_val := expr.Val
  to_val := con_prob_lang.to_val
  fill_item := con_prob_lang.fill_item
  decomp_item := con_prob_lang.decomp_item
  expr_ord := con_prob_lang.expr_ord
  head_step := con_prob_lang.head_step
  state_step := con_prob_lang.state_step
  get_active := con_prob_lang.get_active
  con_ectxi_language_mixin := con_prob_lang_mixin

/-- Rocq: `con_prob_ectx_lang` (a `Canonical Structure`). -/
abbrev con_prob_ectx_lang : conEctxLanguage := ConEctxLanguageOfEctxi con_prob_ectxi_lang

/-- Rocq: `con_prob_lang` (a `Canonical Structure`). -/
abbrev con_prob_lang : conLanguage := ConLanguageOfEctx con_prob_ectx_lang

namespace con_prob_lang

/-- The `fill` of `con_prob_lang` (Rocq: `fill` of `ectx_language`, found through canonical
structures): `conEctxiLanguage.fill` for `con_prob_ectxi_lang`. -/
abbrev fill (K : List ectx_item) (e : expr) : expr :=
  conEctxiLanguage.fill (Λ := con_prob_ectxi_lang) K e

/-- Rocq: `ectxi_lang_ctx_item` for `con_prob_lang` (found via canonical structures in Rocq). -/
instance con_prob_lang_ctx_item (Ki : ectx_item) :
    ConLanguageCtx (Λ := con_prob_lang) (fill_item Ki) :=
  conEctxiLanguage.ectxi_lang_ctx_item (Λ := con_prob_ectxi_lang) Ki

/-- Rocq: `con_ectx_lang_ctx` for `con_prob_lang` (found via canonical structures in Rocq). -/
instance con_prob_lang_ctx (K : List ectx_item) :
    ConLanguageCtx (Λ := con_prob_lang) (fill K) :=
  conEctxiLanguage.con_ectxi_lang_ctx (Λ := con_prob_ectxi_lang) K

theorem con_prob_lang_expr : con_prob_lang.expr = expr := rfl
theorem con_prob_lang_val : con_prob_lang.val = val := rfl
theorem con_prob_lang_state : con_prob_lang.state = state := rfl
theorem con_prob_lang_state_idx : con_prob_lang.state_idx = Loc := rfl
@[simp] theorem con_prob_lang_to_val (e : expr) :
    ConProbLang.to_val (Λ := con_prob_lang) e = to_val e := rfl
@[simp] theorem con_prob_lang_of_val (v : val) :
    ConProbLang.of_val (Λ := con_prob_lang) v = Val v := rfl
@[simp] theorem con_prob_lang_state_step (σ : state) (α : Loc) :
    ConProbLang.state_step (Λ := con_prob_lang) σ α = state_step σ α := rfl
@[simp] theorem con_prob_lang_get_active (σ : state) :
    ConProbLang.get_active (Λ := con_prob_lang) σ = get_active σ := rfl
theorem con_prob_ectx_lang_head_step (e : expr) (σ : state) :
    con_prob_ectx_lang.head_step e σ = head_step e σ := rfl

/-- Rocq: `cfg` (top-level `list expr * state`). -/
abbrev cfg : Type := List expr × state

/-- Helper for `solve_red`: a `head_step_rel` step witnesses head reducibility. -/
theorem head_reducible_of_rel {e e' : expr} {σ σ' : state} {efs : List expr}
    (h : head_step_rel e σ e' σ' efs) :
    conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e σ :=
  ⟨(e', σ', efs), (head_step_support_equiv_rel _ _ _ _ _).2 h⟩

/-- Helper for `solve_red`: a `head_step_rel` step witnesses reducibility. -/
theorem reducible_of_rel {e e' : expr} {σ σ' : state} {efs : List expr}
    (h : head_step_rel e σ e' σ' efs) : reducible (Λ := con_prob_lang) e σ :=
  conEctxLanguage.head_prim_reducible (Λ := con_prob_ectx_lang) e σ (head_reducible_of_rel h)

/-- Rocq: `solve_red` (from `con_prob_lang/tactics.v`), restricted to its non-Iris cases:
proves `reducible (Λ := con_prob_lang) e σ` goals, descending through `fill` with
`reducible_fill`, and `head_reducible e σ` goals with `solve_head_step`. -/
syntax "solve_red" : tactic
macro_rules
  | `(tactic| solve_red) => `(tactic| first
    | (apply head_reducible_of_rel; solve_head_step_rel)
    | (apply reducible_of_rel; solve_head_step_rel)
    | (apply ConProbLang.reducible_fill; solve_red))

example (σ : state) :
    reducible (Λ := con_prob_lang) (Pair (Val (LitV LitUnit)) (Val (LitV LitUnit))) σ := by
  solve_red
example (σ : state) (l : Loc) (v : val) (h : σ.heap[l]? = some v) :
    reducible (Λ := con_prob_lang) (Load (Val (LitV (LitLoc l)))) σ := by
  solve_red
example (σ : state) :
    reducible (Λ := con_prob_lang) (Rand (Val (LitV (LitInt 3))) (Val (LitV LitUnit))) σ := by
  solve_red
example (σ : state) (v : val) :
    reducible (Λ := con_prob_lang)
      (fill [AppLCtx v] (Pair (Val (LitV LitUnit)) (Val (LitV LitUnit)))) σ := by
  solve_red
example (σ : state) (e' : expr) (σ' : state) (efs : List expr)
    (h : 0 < head_step (Fst (Val (PairV (LitV LitUnit) (LitV (LitBool true))))) σ (e', σ', efs)) :
    e' = Val (LitV LitUnit) ∧ σ' = σ ∧ efs = [] := by
  inv_head_step
  exact ⟨rfl, rfl, rfl⟩

/-! ## Scheduler type classes -/

section sch_typeclasses

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate
set_option quotPrecheck false in
/-- The return type of `con_lang_mdp con_prob_lang` (reducibly `val`). -/
local notation "CPRet" => (con_lang_mdp con_prob_lang).mdpstate_ret
set_option quotPrecheck false in
/-- The action type of `con_lang_mdp con_prob_lang` (reducibly `ℕ`, the thread id). -/
local notation "CPAct" => (con_lang_mdp con_prob_lang).mdpaction

/-- `tid < length ρ.1` for a thread id `tid` (an action of `con_lang_mdp con_prob_lang`) and a
configuration `ρ`. (Rocq writes `tid < length ρ.1` directly; in Lean the action type
`(con_lang_mdp con_prob_lang).mdpaction` is only reducible to `ℕ` at default transparency, and
this helper keeps the terms below well-typed at reducible transparency, which `simp`/`rw`
need.) -/
def thread_lt (tid : CPAct) (ρ : CPState) : Prop := @LT.lt ℕ _ tid ρ.1.length

instance thread_lt_dec (tid : CPAct) (ρ : CPState) : Decidable (thread_lt tid ρ) :=
  Nat.decLt tid ρ.1.length

theorem thread_lt_iff (tid : ℕ) (ρ : cfg) : thread_lt tid ρ ↔ tid < ρ.1.length := Iff.rfl


/-- Rocq: `TapeOblivious`. -/
class TapeOblivious (sch_int_σ : Type*) [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) : Prop where
  tape_oblivious : ∀ (ζ : sch_int_σ) (ρ ρ' : CPState), ρ.1 = ρ'.1 → ρ.2.heap = ρ'.2.heap →
    sch (ζ, ρ) = sch (ζ, ρ')

/-- Rocq: `sch_tape_oblivious`. -/
theorem sch_tape_oblivious {si : Type*} [Countable si]
    {sch : scheduler (con_lang_mdp con_prob_lang) si} [TapeOblivious si sch] (ζ : si)
    (ρ ρ' : CPState) (h1 : ρ.1 = ρ'.1) (h2 : ρ.2.heap = ρ'.2.heap) : sch (ζ, ρ) = sch (ζ, ρ') :=
  TapeOblivious.tape_oblivious ζ ρ ρ' h1 h2

/-- Rocq: `sch_tape_oblivious_state_upd_tapes`. -/
theorem sch_tape_oblivious_state_upd_tapes {si : Type*} [Countable si]
    {sch : scheduler (con_lang_mdp con_prob_lang) si} [TapeOblivious si sch] (ζ : si) (α : Loc)
    (t : tape) (σ : state) (es : List expr) :
    sch (ζ, ((es, state_upd_tapes (·.insert α t) σ) : CPState)) = sch (ζ, ((es, σ) : CPState)) :=
  sch_tape_oblivious ζ _ _ rfl rfl

/- non-stutter -/

variable {sch_int_σ : Type*} [Countable sch_int_σ]
variable (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)

/-- Rocq: `non_stutter_step'`. -/
def non_stutter_step' : ℕ → sch_int_σ × CPState → Distr (sch_int_σ × CPAct)
  | 0, _ => dzero
  | n + 1, p =>
    sch p ≫= fun q =>
      if thread_lt q.2 p.2 then dret q else non_stutter_step' n (q.1, p.2)

theorem non_stutter_step'_succ (n : ℕ) (p : sch_int_σ × CPState) :
    non_stutter_step' sch (n + 1) p =
      (sch p ≫= fun q =>
        if thread_lt q.2 p.2 then dret q else non_stutter_step' sch n (q.1, p.2)) := rfl

/-- Rocq: `non_stutter_step'_mono`. -/
theorem non_stutter_step'_mono (p : sch_int_σ × CPState) (n : ℕ) (x : sch_int_σ × CPAct) :
    non_stutter_step' sch n p x ≤ non_stutter_step' sch (n + 1) p x := by
  induction n generalizing p with
  | zero => exact (dzero_0 x).trans_le zero_le
  | succ n ih =>
    rw [non_stutter_step'_succ, non_stutter_step'_succ, dbind_unfold_pmf, dbind_unfold_pmf]
    refine ENNReal.tsum_le_tsum fun q => mul_le_mul' le_rfl ?_
    split
    · exact le_rfl
    · exact ih _

/-- Rocq: `non_stutter_step'_property`. -/
theorem non_stutter_step'_property (n : ℕ) (ζ : sch_int_σ) (ρ : CPState) (ζ' : sch_int_σ) (tid : ℕ)
    (h : 0 < non_stutter_step' sch n (ζ, ρ) (ζ', tid)) : tid < ρ.1.length := by
  induction n generalizing ζ with
  | zero => exact absurd h (dzero_supp_empty _)
  | succ n ih =>
    rw [non_stutter_step'_succ, dbind_pos] at h
    obtain ⟨q, hq, -⟩ := h
    split at hq
    · rename_i hlt
      obtain rfl := dret_pos _ _ hq
      exact hlt
    · exact ih _ hq

/-- Rocq: `non_stutter_step`. -/
def non_stutter_step (p : sch_int_σ × CPState) : Distr (sch_int_σ × CPAct) :=
  lim_distr (fun n => non_stutter_step' sch n p) (fun n x => non_stutter_step'_mono sch p n x)

/-- Rocq: `non_stutter_step_unfold`. -/
theorem non_stutter_step_unfold (a : sch_int_σ × CPState) (b : sch_int_σ × CPAct) :
    non_stutter_step sch a b = ⨆ n, non_stutter_step' sch n a b := rfl

/-- Rocq: `non_stutter_step_prefix`. -/
theorem non_stutter_step_prefix (ζ : sch_int_σ) (ρ : CPState) :
    non_stutter_step sch (ζ, ρ) =
      (sch (ζ, ρ) ≫= fun q =>
        if thread_lt q.2 ρ then dret q else non_stutter_step sch (q.1, ρ)) := by
  ext v
  have hmono : Monotone fun n => non_stutter_step' sch n (ζ, ρ) v :=
    monotone_nat_of_le_succ fun n => non_stutter_step'_mono sch _ n v
  rw [non_stutter_step_unfold, ← Monotone.iSup_nat_add hmono 1, dbind_unfold_pmf]
  simp only [non_stutter_step'_succ, dbind_unfold_pmf]
  have : ∀ q : sch_int_σ × CPAct,
      (sch (ζ, ρ) q * (if thread_lt q.2 ρ then dret q else non_stutter_step sch (q.1, ρ)) v) =
        ⨆ n, sch (ζ, ρ) q *
          (if thread_lt q.2 ρ then dret q else non_stutter_step' sch n (q.1, ρ)) v := by
    intro q
    rw [← ENNReal.mul_iSup]
    congr 1
    split
    · rw [iSup_const]
    · rfl
  simp only [this]
  refine (tsum_iSup_of_monotone ?_).symm
  intro q
  refine monotone_nat_of_le_succ fun n => mul_le_mul' le_rfl ?_
  split
  · exact le_rfl
  · exact non_stutter_step'_mono sch _ n v

/-- Rocq: `non_stutter_scheduler`. -/
def non_stutter_scheduler : scheduler (con_lang_mdp con_prob_lang) sch_int_σ :=
  ⟨non_stutter_step sch⟩

theorem non_stutter_scheduler_apply (p : sch_int_σ × CPState) :
    non_stutter_scheduler sch p = non_stutter_step sch p := rfl

/-- Rocq: `non_stutter_scheduler_tape_oblivious`. -/
theorem non_stutter_scheduler_tape_oblivious [HTO : TapeOblivious _ sch] :
    TapeOblivious _ (non_stutter_scheduler sch) := by
  constructor
  intro ζ ρ ρ' h1 h2
  change non_stutter_step sch (ζ, ρ) = non_stutter_step sch (ζ, ρ')
  have key : ∀ n (ζ : sch_int_σ), non_stutter_step' sch n (ζ, ρ) = non_stutter_step' sch n (ζ, ρ') := by
    intro n
    induction n with
    | zero => intro ζ; rfl
    | succ n ih =>
      intro ζ
      rw [non_stutter_step'_succ, non_stutter_step'_succ, HTO.tape_oblivious ζ ρ ρ' h1 h2]
      refine dbind_ext_right _ _ _ fun q => ?_
      dsimp only
      simp only [show thread_lt q.2 ρ ↔ thread_lt q.2 ρ' by unfold thread_lt; rw [h1], ih]
  ext v
  rw [non_stutter_step_unfold, non_stutter_step_unfold]
  simp only [key]

/-- Rocq: `NonStuttering`. -/
class NonStuttering {sch_int_σ : Type*} [Countable sch_int_σ]
    (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) : Prop where
  non_stuttering : ∀ (ζ : sch_int_σ) (ρ : CPState) (ζ' : sch_int_σ) (tid : ℕ),
    0 < sch (ζ, ρ) (ζ', tid) → tid < ρ.1.length

/-- Rocq: `non_stutter_scheduler_non_stuttering`. -/
theorem non_stutter_scheduler_non_stuttering : NonStuttering (non_stutter_scheduler sch) := by
  constructor
  intro ζ ρ ζ' tid h
  change 0 < non_stutter_step sch (ζ, ρ) (ζ', tid) at h
  rw [non_stutter_step_unfold, lt_iSup_iff] at h
  obtain ⟨n, hn⟩ := h
  exact non_stutter_step'_property sch n ζ ρ ζ' tid hn

/-- Helper (not in Rocq): scheduling a non-existent thread of a non-final configuration
stutters. -/
theorem con_lang_mdp_step_stutter (ρ : ConProbLang.cfg con_prob_lang) (tid : ℕ) (hρ : con_lang_mdp_to_final con_prob_lang ρ = none)
    (htid : ρ.1.length ≤ tid) : con_lang_mdp_step con_prob_lang tid ρ = dret ρ := by
  unfold con_lang_mdp_to_final at hρ
  unfold con_lang_mdp_step
  have h0 : (ρ.1[0]? >>= ConProbLang.to_val (Λ := con_prob_lang)) = none := by
    split at hρ <;> simp_all
  rw [h0]
  simp only [List.getElem?_eq_none htid]

/-- Rocq: `non_stutter_scheduler_same_semantics`. -/
theorem non_stutter_scheduler_same_semantics (ζ : sch_int_σ) (ρ : CPState) (v : CPRet) :
    sch_lim_exec sch (ζ, ρ) v ≤ sch_lim_exec (non_stutter_scheduler sch) (ζ, ρ) v := by
  apply sch_lim_exec_leq
  intro n
  induction n generalizing ζ ρ v with
  | zero =>
    cases hf : (con_lang_mdp con_prob_lang).to_final ρ with
    | some b =>
      rw [sch_exec_is_final _ _ _ _ hf, sch_lim_exec_final _ _ _ hf]
    | none =>
      rw [sch_exec_O_not_final _ _ (to_final_None_2 _ hf)]
      exact zero_le
  | succ n ih =>
    cases hf : (con_lang_mdp con_prob_lang).to_final ρ with
    | some b =>
      rw [sch_exec_is_final _ _ _ _ hf, sch_lim_exec_final _ _ _ hf]
    | none =>
      have hnf := to_final_None_2 _ hf
      rw [sch_exec_Sn_not_final _ _ _ hnf, sch_lim_exec_not_final _ _ hnf]
      simp only [sch_step]
      rw [non_stutter_scheduler_apply, non_stutter_step_prefix, ← dbind_assoc, ← dbind_assoc,
        ← dbind_assoc]
      refine distr_le_dbind _ _ _ _ (distr_le_refl _) (fun q w => ?_) v
      split
      · rw [dret_id_left]
        exact distr_le_dbind _ _ _ _ (distr_le_refl _) (fun a b => ih a.1 a.2 b) w
      · rename_i hq
        have hst : (con_lang_mdp con_prob_lang).step q.2 ρ = dret ρ :=
          con_lang_mdp_step_stutter ρ q.2 hf (Nat.le_of_not_lt hq)
        rw [hst, dmap_dret, dret_id_left]
        have := ih q.1 ρ w
        rw [sch_lim_exec_not_final _ _ hnf, sch_step, ← dbind_assoc] at this
        exact this

end sch_typeclasses

end con_prob_lang
end ConProbLang
