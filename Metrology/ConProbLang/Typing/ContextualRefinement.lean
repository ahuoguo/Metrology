module

public import Metrology.ConProbLang.Typing.Types
public import Metrology.ConProbLang.LubTermination

/-!
# Contextual refinement

Ported from clutch/theories/con_prob_lang/typing/contextual_refinement.v

Notion of contextual refinement & proof that it is a precongruence.

## Imports
The Rocq file imports `clutch.prob.markov`, `clutch.clutch.primitive_laws` (commented out),
`iris.proofmode`, `Reals`/`Rbar`: none of them is used, so they are dropped. The only thing
used from `clutch.con_prob_lang.lub_termination` is `lub_termination_prob`, imported from
`Metrology.ConProbLang.LubTermination` (as in Rocq).

## Rocq → Lean mapping
* `lub_termination_prob e σ` (a `Lub_Rbar` of real numbers in Rocq) is the `ℝ≥0∞`-valued
  `sSup` defined in `LubTermination.lean`. `SeriesC` is `∑'`.
* `ctx` is `List ctx_item`; `fill_ctx K e = K.foldr fill_ctx_item e`.
* The notations `Γ ⊨ e ≤ctx≤ e' : τ` and `Γ ⊨ e =ctx= e' : τ` are scoped.
* The `Reflexive`/`Transitive` instances `ctx_refines_reflexive`, `ctx_refines_transitive`,
  `ctx_equiv_transitive` are theorems (statements `∀ e, ctx_refines Γ e e τ` etc.);
  additionally `Std.Refl`/`IsTrans` and `Trans` (for `calc`) instances are registered.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob

namespace ConProbLang

namespace con_prob_lang

/-! ## Contexts -/

/-- Rocq: `ctx_item`. -/
inductive ctx_item : Type where
  /- Base lambda calculus -/
  | CTX_Rec (f x : binder)
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  /- Base types and their operations -/
  | CTX_UnOp (op : un_op)
  | CTX_BinOpL (op : bin_op) (e2 : expr)
  | CTX_BinOpR (op : bin_op) (e1 : expr)
  | CTX_IfL (e1 : expr) (e2 : expr)
  | CTX_IfM (e0 : expr) (e2 : expr)
  | CTX_IfR (e0 : expr) (e1 : expr)
  /- Products -/
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  /- Sums -/
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  /- Heap -/
  | CTX_Alloc
  | CTX_Load
  | CTX_StoreL (e2 : expr)
  | CTX_StoreR (e1 : expr)
  /- Recursive Types -/
  | CTX_Fold
  | CTX_Unfold
  /- Polymorphic Types -/
  | CTX_TLam
  | CTX_TApp
  /- Existential types (we do not have an explicit PACK operation) -/
  | CTX_UnpackL (x : binder) (e2 : expr)
  | CTX_UnpackR (x : binder) (e1 : expr)
  | CTX_AllocTape
  | CTX_RandL (e2 : expr)
  | CTX_RandR (e1 : expr)
  /- Concurrency -/
  | CTX_Fork
  | CTX_CmpXchgL (e1 : expr) (e2 : expr)
  | CTX_CmpXchgM (e0 : expr) (e2 : expr)
  | CTX_CmpXchgR (e0 : expr) (e1 : expr)
  | CTX_XchgL (e1 : expr)
  | CTX_XchgR (e0 : expr)
  | CTX_FAAL (e1 : expr)
  | CTX_FAAR (e0 : expr)
deriving DecidableEq, Inhabited

export ctx_item (CTX_Rec CTX_AppL CTX_AppR CTX_UnOp CTX_BinOpL CTX_BinOpR CTX_IfL CTX_IfM
  CTX_IfR CTX_PairL CTX_PairR CTX_Fst CTX_Snd CTX_InjL CTX_InjR CTX_CaseL CTX_CaseM CTX_CaseR
  CTX_Alloc CTX_Load CTX_StoreL CTX_StoreR CTX_Fold CTX_Unfold CTX_TLam CTX_TApp CTX_UnpackL
  CTX_UnpackR CTX_AllocTape CTX_RandL CTX_RandR CTX_Fork CTX_CmpXchgL CTX_CmpXchgM CTX_CmpXchgR
  CTX_XchgL CTX_XchgR CTX_FAAL CTX_FAAR)

/-- Rocq: `fill_ctx_item`. -/
def fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  /- Base lambda calculus -/
  | CTX_Rec f x => Rec f x e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  /- Base types and operations -/
  | CTX_UnOp op => UnOp op e
  | CTX_BinOpL op e2 => BinOp op e e2
  | CTX_BinOpR op e1 => BinOp op e1 e
  | CTX_IfL e1 e2 => If e e1 e2
  | CTX_IfM e0 e2 => If e0 e e2
  | CTX_IfR e0 e1 => If e0 e1 e
  /- Products -/
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  /- Sums -/
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  /- Heap & atomic CAS/FAA -/
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  /- Recursive & polymorphic types -/
  | CTX_Fold => e
  | CTX_Unfold => App (Val rec_unfold) e
  | CTX_TLam => TLam e
  | CTX_TApp => TApp e
  | CTX_UnpackL x e1 => Unpack x e e1
  | CTX_UnpackR x e0 => Unpack x e0 e
  | CTX_AllocTape => AllocTape e
  | CTX_RandL e2 => Rand e e2
  | CTX_RandR e1 => Rand e1 e
  /- Concurrency -/
  | CTX_Fork => Fork e
  | CTX_CmpXchgL e1 e2 => CmpXchg e e1 e2
  | CTX_CmpXchgM e0 e2 => CmpXchg e0 e e2
  | CTX_CmpXchgR e0 e1 => CmpXchg e0 e1 e
  | CTX_XchgL e2 => Xchg e e2
  | CTX_XchgR e1 => Xchg e1 e
  | CTX_FAAL e2 => FAA e e2
  | CTX_FAAR e1 => FAA e1 e

/-- Rocq: `ctx`. -/
abbrev ctx := List ctx_item

/-- Rocq: `fill_ctx`. -/
def fill_ctx (K : ctx) (e : expr) : expr := K.foldr fill_ctx_item e

@[simp] theorem fill_ctx_nil (e : expr) : fill_ctx [] e = e := rfl
@[simp] theorem fill_ctx_cons (k : ctx_item) (K : ctx) (e : expr) :
    fill_ctx (k :: K) e = fill_ctx_item k (fill_ctx K e) := rfl

/-! ## Typed contexts -/

/-- Rocq: `typed_ctx_item`. -/
inductive typed_ctx_item :
    ctx_item → varmap type → type → varmap type → type → Prop where
  /- Base lambda calculus -/
  | TP_CTX_Rec (Γ : varmap type) (τ τ' : type) (f x : binder) :
      typed_ctx_item (CTX_Rec f x) (binder_insert f (TArrow τ τ') (binder_insert x τ Γ)) τ' Γ
        (TArrow τ τ')
  | TP_CTX_AppL (Γ : varmap type) (e2 : expr) (τ τ' : type) :
      typed Γ e2 τ →
      typed_ctx_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
  | TP_CTX_AppR (Γ : varmap type) (e1 : expr) (τ τ' : type) :
      typed Γ e1 (TArrow τ τ') →
      typed_ctx_item (CTX_AppR e1) Γ τ Γ τ'
  /- Base types and operations -/
  | TP_CTX_UnOp_Nat (op : un_op) (Γ : varmap type) (τ : type) :
      unop_int_res_type op = some τ →
      typed_ctx_item (CTX_UnOp op) Γ TInt Γ τ
  | TP_CTX_UnOp_Bool (op : un_op) (Γ : varmap type) (τ : type) :
      unop_bool_res_type op = some τ →
      typed_ctx_item (CTX_UnOp op) Γ TBool Γ τ
  | TP_CTX_BinOpL_Nat (op : bin_op) (Γ : varmap type) (e2 : expr) (τ : type) :
      typed Γ e2 TInt →
      binop_int_res_type op = some τ →
      typed_ctx_item (CTX_BinOpL op e2) Γ TInt Γ τ
  | TP_CTX_BinOpR_Nat (op : bin_op) (e1 : expr) (Γ : varmap type) (τ : type) :
      typed Γ e1 TInt →
      binop_int_res_type op = some τ →
      typed_ctx_item (CTX_BinOpR op e1) Γ TInt Γ τ
  | TP_CTX_BinOpL_Bool (op : bin_op) (Γ : varmap type) (e2 : expr) (τ : type) :
      typed Γ e2 TBool →
      binop_bool_res_type op = some τ →
      typed_ctx_item (CTX_BinOpL op e2) Γ TBool Γ τ
  | TP_CTX_BinOpR_Bool (op : bin_op) (e1 : expr) (Γ : varmap type) (τ : type) :
      typed Γ e1 TBool →
      binop_bool_res_type op = some τ →
      typed_ctx_item (CTX_BinOpR op e1) Γ TBool Γ τ
  | TP_CTX_BinOpL_UnboxedEq (e2 : expr) (Γ : varmap type) (τ : type) :
      UnboxedType τ →
      typed Γ e2 τ →
      typed_ctx_item (CTX_BinOpL EqOp e2) Γ τ Γ TBool
  | TP_CTX_BinOpR_UnboxedEq (e1 : expr) (Γ : varmap type) (τ : type) :
      UnboxedType τ →
      typed Γ e1 τ →
      typed_ctx_item (CTX_BinOpR EqOp e1) Γ τ Γ TBool
  | TP_CTX_IfL (Γ : varmap type) (e1 e2 : expr) (τ : type) :
      typed Γ e1 τ → typed Γ e2 τ →
      typed_ctx_item (CTX_IfL e1 e2) Γ TBool Γ τ
  | TP_CTX_IfM (Γ : varmap type) (e0 e2 : expr) (τ : type) :
      typed Γ e0 TBool → typed Γ e2 τ →
      typed_ctx_item (CTX_IfM e0 e2) Γ τ Γ τ
  | TP_CTX_IfR (Γ : varmap type) (e0 e1 : expr) (τ : type) :
      typed Γ e0 TBool → typed Γ e1 τ →
      typed_ctx_item (CTX_IfR e0 e1) Γ τ Γ τ
  /- Products -/
  | TP_CTX_PairL (Γ : varmap type) (e2 : expr) (τ τ' : type) :
      typed Γ e2 τ' →
      typed_ctx_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
  | TP_CTX_PairR (Γ : varmap type) (e1 : expr) (τ τ' : type) :
      typed Γ e1 τ →
      typed_ctx_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
  | TP_CTX_Fst (Γ : varmap type) (τ τ' : type) :
      typed_ctx_item CTX_Fst Γ (TProd τ τ') Γ τ
  | TP_CTX_Snd (Γ : varmap type) (τ τ' : type) :
      typed_ctx_item CTX_Snd Γ (TProd τ τ') Γ τ'
  /- Sums -/
  | TP_CTX_InjL (Γ : varmap type) (τ τ' : type) :
      typed_ctx_item CTX_InjL Γ τ Γ (TSum τ τ')
  | TP_CTX_InjR (Γ : varmap type) (τ τ' : type) :
      typed_ctx_item CTX_InjR Γ τ' Γ (TSum τ τ')
  | TP_CTX_CaseL (Γ : varmap type) (e1 e2 : expr) (τ1 τ2 τ' : type) :
      typed Γ e1 (TArrow τ1 τ') → typed Γ e2 (TArrow τ2 τ') →
      typed_ctx_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
  | TP_CTX_CaseM (Γ : varmap type) (e0 e2 : expr) (τ1 τ2 τ' : type) :
      typed Γ e0 (TSum τ1 τ2) → typed Γ e2 (TArrow τ2 τ') →
      typed_ctx_item (CTX_CaseM e0 e2) Γ (TArrow τ1 τ') Γ τ'
  | TP_CTX_CaseR (Γ : varmap type) (e0 e1 : expr) (τ1 τ2 τ' : type) :
      typed Γ e0 (TSum τ1 τ2) → typed Γ e1 (TArrow τ1 τ') →
      typed_ctx_item (CTX_CaseR e0 e1) Γ (TArrow τ2 τ') Γ τ'
  /- Heap -/
  | TPCTX_Alloc (Γ : varmap type) (τ : type) :
      typed_ctx_item CTX_Alloc Γ τ Γ (TRef τ)
  | TP_CTX_Load (Γ : varmap type) (τ : type) :
      typed_ctx_item CTX_Load Γ (TRef τ) Γ τ
  | TP_CTX_StoreL (Γ : varmap type) (e2 : expr) (τ : type) :
      typed Γ e2 τ → typed_ctx_item (CTX_StoreL e2) Γ (TRef τ) Γ TUnit
  | TP_CTX_StoreR (Γ : varmap type) (e1 : expr) (τ : type) :
      typed Γ e1 (TRef τ) →
      typed_ctx_item (CTX_StoreR e1) Γ τ Γ TUnit
  /- Polymorphic & recursive types -/
  | TP_CTX_Fold (Γ : varmap type) (τ : type) :
      typed_ctx_item CTX_Fold Γ (τ.[TRec τ/]) Γ (TRec τ)
  | TP_CTX_Unfold (Γ : varmap type) (τ : type) :
      typed_ctx_item CTX_Unfold Γ (TRec τ) Γ (τ.[TRec τ/])
  | TP_CTX_TLam (Γ : varmap type) (τ : type) :
      typed_ctx_item CTX_TLam (⤉Γ) τ Γ (TForall τ)
  | TP_CTX_TApp (Γ : varmap type) (τ τ' : type) :
      typed_ctx_item CTX_TApp Γ (TForall τ) Γ (τ.[τ'/])
  | TP_CTX_UnpackL (x : binder) (e2 : expr) (Γ : varmap type) (τ τ2 : type) :
      typed (binder_insert x τ (⤉Γ)) e2 (type.subst (type.ren (· + 1)) τ2) →
      typed_ctx_item (CTX_UnpackL x e2) Γ (TExists τ) Γ τ2
  | TP_CTX_UnpackR (x : binder) (e1 : expr) (Γ : varmap type) (τ τ2 : type) :
      typed Γ e1 (TExists τ) →
      typed_ctx_item (CTX_UnpackR x e1)
        (binder_insert x τ (⤉Γ)) (type.subst (type.ren (· + 1)) τ2) Γ τ2
  | TP_CTX_AllocTape (Γ : varmap type) :
      typed_ctx_item CTX_AllocTape Γ TNat Γ TTape
  | TP_CTX_RandUnitL (Γ : varmap type) (e2 : expr) :
      typed Γ e2 TUnit → typed_ctx_item (CTX_RandL e2) Γ TNat Γ TNat
  | TP_CTX_RandTapeL (Γ : varmap type) (e2 : expr) :
      typed Γ e2 TTape → typed_ctx_item (CTX_RandL e2) Γ TNat Γ TNat
  | TP_CTX_RandUnitR (Γ : varmap type) (e1 : expr) :
      typed Γ e1 TNat → typed_ctx_item (CTX_RandR e1) Γ TUnit Γ TNat
  | TP_CTX_RandTapeR (Γ : varmap type) (e1 : expr) :
      typed Γ e1 TNat → typed_ctx_item (CTX_RandR e1) Γ TTape Γ TNat
  | TP_CTX_Fork (Γ : varmap type) :
      typed_ctx_item CTX_Fork Γ TUnit Γ TUnit
  | TP_CTX_CmpXchgL (Γ : varmap type) (e1 e2 : expr) (τ : type) :
      UnboxedType τ →
      typed Γ e1 τ → typed Γ e2 τ →
      typed_ctx_item (CTX_CmpXchgL e1 e2) Γ (TRef τ) Γ (TProd τ TBool)
  | TP_CTX_CmpXchgM (Γ : varmap type) (e0 e2 : expr) (τ : type) :
      UnboxedType τ →
      typed Γ e0 (TRef τ) → typed Γ e2 τ →
      typed_ctx_item (CTX_CmpXchgM e0 e2) Γ τ Γ (TProd τ TBool)
  | TP_CTX_CmpXchgR (Γ : varmap type) (e0 e1 : expr) (τ : type) :
      UnboxedType τ →
      typed Γ e0 (TRef τ) → typed Γ e1 τ →
      typed_ctx_item (CTX_CmpXchgR e0 e1) Γ τ Γ (TProd τ TBool)
  | TP_CTX_XchgL (Γ : varmap type) (e2 : expr) (τ : type) :
      typed Γ e2 τ → typed_ctx_item (CTX_XchgL e2) Γ (TRef τ) Γ τ
  | TP_CTX_XchgR (Γ : varmap type) (e1 : expr) (τ : type) :
      typed Γ e1 (TRef τ) →
      typed_ctx_item (CTX_XchgR e1) Γ τ Γ τ
  | TP_CTX_FAAL (Γ : varmap type) (e2 : expr) :
      typed Γ e2 TNat → typed_ctx_item (CTX_FAAL e2) Γ (TRef TNat) Γ TNat
  | TP_CTX_FAAR (Γ : varmap type) (e1 : expr) :
      typed Γ e1 (TRef TNat) →
      typed_ctx_item (CTX_FAAR e1) Γ TNat Γ TNat

/-- Rocq: `typed_ctx`. -/
inductive typed_ctx : ctx → varmap type → type → varmap type → type → Prop where
  | TPCTX_nil (Γ : varmap type) (τ : type) :
      typed_ctx [] Γ τ Γ τ
  | TPCTX_cons (Γ1 : varmap type) (τ1 : type) (Γ2 : varmap type) (τ2 : type)
      (Γ3 : varmap type) (τ3 : type) (k : ctx_item) (K : ctx) :
      typed_ctx_item k Γ2 τ2 Γ3 τ3 →
      typed_ctx K Γ1 τ1 Γ2 τ2 →
      typed_ctx (k :: K) Γ1 τ1 Γ3 τ3

/-! ## Contextual refinement -/

/-- Rocq: `ctx_refines`. The main definition of contextual refinement that we use. -/
def ctx_refines (Γ : varmap type) (e e' : expr) (τ : type) : Prop :=
  ∀ (K : ctx) (σ₀ : state) (τ' : type),
    typed_ctx K Γ τ ∅ τ' →
    lub_termination_prob (fill_ctx K e) σ₀ ≤ lub_termination_prob (fill_ctx K e') σ₀

@[inherit_doc] scoped notation:100 Γ:100 " ⊨ " e:101 " ≤ctx≤ " e':101 " : " τ:200 =>
  ctx_refines Γ e e' τ

/-- Tries every constructor of `typed`, closing the premises by assumption. -/
local macro "typed_constr" : tactic =>
  `(tactic| first
    | (apply typed.Rec_typed <;> assumption)
    | (apply typed.App_typed <;> assumption)
    | (apply typed.UnOp_typed_int <;> assumption)
    | (apply typed.UnOp_typed_bool <;> assumption)
    | (apply typed.BinOp_typed_int <;> assumption)
    | (apply typed.BinOp_typed_bool <;> assumption)
    | (apply typed.UnboxedEq_typed <;> assumption)
    | (apply typed.If_typed <;> assumption)
    | (apply typed.Pair_typed <;> assumption)
    | (apply typed.Fst_typed <;> assumption)
    | (apply typed.Snd_typed <;> assumption)
    | (apply typed.InjL_typed <;> assumption)
    | (apply typed.InjR_typed <;> assumption)
    | (apply typed.Case_typed <;> assumption)
    | (apply typed.TAlloc <;> assumption)
    | (apply typed.TLoad <;> assumption)
    | (apply typed.TStore <;> assumption)
    | (apply typed.TFold <;> assumption)
    | (apply typed.TUnfold <;> assumption)
    | (apply typed.TLam_typed <;> assumption)
    | (apply typed.TApp_typed <;> assumption)
    | (apply typed.TUnpack <;> assumption)
    | (apply typed.TAllocTape <;> assumption)
    | (apply typed.TRand <;> assumption)
    | (apply typed.TRandU <;> assumption)
    | (apply typed.Fork_typed <;> assumption)
    | (apply typed.CmpXchg_typed <;> assumption)
    | (apply typed.Xchg_typed <;> assumption)
    | (apply typed.Faa_typed <;> assumption))

/-- Rocq: `typed_ctx_item_typed`. -/
theorem typed_ctx_item_typed (k : ctx_item) (Γ : varmap type) (τ : type) (Γ' : varmap type)
    (τ' : type) (e : expr) :
    typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' → typed Γ' (fill_ctx_item k e) τ' := by
  intro He Hk
  induction Hk <;> simp only [fill_ctx_item] <;> typed_constr

/-- Rocq: `typed_ctx_typed`. -/
theorem typed_ctx_typed (K : ctx) (Γ : varmap type) (τ : type) (Γ' : varmap type) (τ' : type)
    (e : expr) : typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ' := by
  intro He HK
  induction HK with
  | TPCTX_nil => exact He
  | TPCTX_cons _ _ _ _ _ _ k K Hk _ ih => exact typed_ctx_item_typed _ _ _ _ _ _ (ih He) Hk

/-- Rocq: `ctx_refines_reflexive` (a `Reflexive` instance). -/
theorem ctx_refines_reflexive (Γ : varmap type) (τ : type) (e : expr) : ctx_refines Γ e e τ :=
  fun _ _ _ _ => le_rfl

/-- Rocq: `ctx_refines_transitive` (a `Transitive` instance). -/
theorem ctx_refines_transitive (Γ : varmap type) (τ : type) (e1 e2 e3 : expr) :
    ctx_refines Γ e1 e2 τ → ctx_refines Γ e2 e3 τ → ctx_refines Γ e1 e3 τ :=
  fun Hctx1 Hctx2 K σ₀ b Hty => (Hctx1 K σ₀ b Hty).trans (Hctx2 K σ₀ b Hty)

instance ctx_refines_isRefl (Γ : varmap type) (τ : type) :
    Std.Refl (fun e1 e2 => ctx_refines Γ e1 e2 τ) :=
  ⟨ctx_refines_reflexive Γ τ⟩

instance ctx_refines_isTrans (Γ : varmap type) (τ : type) :
    IsTrans expr (fun e1 e2 => ctx_refines Γ e1 e2 τ) :=
  ⟨ctx_refines_transitive Γ τ⟩

instance ctx_refines_trans (Γ : varmap type) (τ : type) :
    Trans (fun e1 e2 => ctx_refines Γ e1 e2 τ) (fun e1 e2 => ctx_refines Γ e1 e2 τ)
      (fun e1 e2 => ctx_refines Γ e1 e2 τ) :=
  ⟨ctx_refines_transitive Γ τ _ _ _⟩

/-- Rocq: `fill_ctx_app`. -/
theorem fill_ctx_app (K K' : ctx) (e : expr) :
    fill_ctx K' (fill_ctx K e) = fill_ctx (K' ++ K) e := by
  simp [fill_ctx, List.foldr_append]

/-- Rocq: `typed_ctx_compose`. -/
theorem typed_ctx_compose (K K' : ctx) (Γ1 Γ2 Γ3 : varmap type) (τ1 τ2 τ3 : type) :
    typed_ctx K Γ1 τ1 Γ2 τ2 →
    typed_ctx K' Γ2 τ2 Γ3 τ3 →
    typed_ctx (K' ++ K) Γ1 τ1 Γ3 τ3 := by
  intro HK HK'
  induction HK' with
  | TPCTX_nil => exact HK
  | TPCTX_cons _ _ _ _ _ _ k K' Hk _ ih =>
    exact typed_ctx.TPCTX_cons _ _ _ _ _ _ k (K' ++ K) Hk (ih HK)

/-- Rocq: `ctx_refines_congruence`. -/
theorem ctx_refines_congruence (Γ : varmap type) (e1 e2 : expr) (τ : type) (Γ' : varmap type)
    (τ' : type) (K : ctx) :
    typed_ctx K Γ τ Γ' τ' →
    (Γ ⊨ e1 ≤ctx≤ e2 : τ) →
    Γ' ⊨ fill_ctx K e1 ≤ctx≤ fill_ctx K e2 : τ' := by
  intro HK Hctx K' σ₀ b Hty
  rw [fill_ctx_app, fill_ctx_app]
  exact Hctx (K' ++ K) σ₀ b (typed_ctx_compose _ _ _ _ _ _ _ _ HK Hty)

/-- Rocq: `ctx_equiv`. -/
def ctx_equiv (Γ : varmap type) (e1 e2 : expr) (τ : type) : Prop :=
  (Γ ⊨ e1 ≤ctx≤ e2 : τ) ∧ (Γ ⊨ e2 ≤ctx≤ e1 : τ)

@[inherit_doc] scoped notation:100 Γ:100 " ⊨ " e:101 " =ctx= " e':101 " : " τ:200 =>
  ctx_equiv Γ e e' τ

/-- Rocq: `ctx_equiv_transitive` (a `Transitive` instance). -/
theorem ctx_equiv_transitive (Γ : varmap type) (τ : type) (e1 e2 e3 : expr) :
    ctx_equiv Γ e1 e2 τ → ctx_equiv Γ e2 e3 τ → ctx_equiv Γ e1 e3 τ :=
  fun ⟨Hctx11, Hctx12⟩ ⟨Hctx21, Hctx22⟩ =>
    ⟨ctx_refines_transitive _ _ _ _ _ Hctx11 Hctx21, ctx_refines_transitive _ _ _ _ _ Hctx22 Hctx12⟩

instance ctx_equiv_isTrans (Γ : varmap type) (τ : type) :
    IsTrans expr (fun e1 e2 => ctx_equiv Γ e1 e2 τ) :=
  ⟨ctx_equiv_transitive Γ τ⟩

end con_prob_lang

end ConProbLang
