module

public import Metrology.ConProbLang.Metatheory
public import Metrology.ConProbLang.Notation

/-!
# Syntactic typing for System F_mu_ref_conc with tapes

Ported from clutch/theories/con_prob_lang/typing/types.v

## Rocq → Lean mapping
* `type` is a plain inductive with de Bruijn type variables `TVar : ℕ → type`; its
  constructors are exported into `ConProbLang.con_prob_lang`.
* Autosubst's derived instances `Ids_type`, `Rename_type`, `Subst_type`, `SubstLemmas_typer`
  are replaced by explicit definitions (all in namespace `ConProbLang.con_prob_lang.type`):
  - `ids` (`= TVar`), `upren`, `rename`, `ren ξ` (`= ids ∘ ξ`), `up`, `subst`, `scons`
    (notation `τ .: σ`, infixr 55);
  - Rocq `τ.[σ]` is `type.subst σ τ`, `τ.[τ'/]` is `τ.[τ'/]` (notation, `= subst (τ' .: ids) τ`);
  - `SubstLemmas` fields: `rename_subst`, `subst_id`, `id_subst`, `subst_comp`
    (plus auxiliaries `rename_rename`, `subst_rename`, `rename_subst_comm`, `up_ids`,
    `up_ren`, `up_comp`);
  - Rocq's `asimpl` is the Lean macro `asimpl` (a `simp` call with these lemmas).
* `stringmap type` is `varmap type` (from `Metatheory.lean`), `Γ !! x = Some τ` is
  `Γ[x]? = some τ`, `<[x:=τ]>Γ` with a binder `x` (the `insert_binder` instance) is
  `binder_insert x τ Γ`, and `dom Γ` is the new `dom Γ : stringset` (`= Γ.keys.toFinset`,
  membership lemma `mem_dom`).
* `⤉ Γ` (`subst (ren (+1)) <$> Γ`) is notation for `type_shift_ctx Γ`
  (`= Γ.map fun _ τ => τ.subst (ren (· + 1))`).
* The typing judgements `typed Γ e τ` (notation `Γ ⊢ₜ e : τ`) and `val_typed v τ`
  (notation `⊢ᵥ v : τ`) are a mutual inductive with the Rocq constructor names (exported).
  The Rocq notations `Λ: e` / `TApp e` / `unpack: x := e1 in e2` are unfolded in the
  constructor statements to `Rec BAnon BAnon e` (resp. `RecV BAnon BAnon e`),
  `App e (Val (LitV LitUnit))` and `App (App (Val unpack) e1) (Lam x e2)`; they are also
  provided as abbrevs `TLam`, `TLamV`, `TApp`, `Unpack`, `UnpackV`.
* `is_Some x` is written `∃ v, x = some v`.
* The type notations of `FType_scope` (`()`, `# x`, `*`, `+`, `→`, `μ:`, `∀:`, `∃:`, `ref`)
  are not provided: Lean terms write the constructors directly (these symbols would clash
  with core Lean notation).

## Omissions
* `Canonical Structure varO` (OFE plumbing, not needed).
* `FType_scope` notations (see above).
-/

@[expose] public section

namespace ConProbLang

namespace con_prob_lang

/-! ## Types -/

/-- Rocq: `type`. Type variables are de Bruijn indices. -/
inductive type : Type where
  | TUnit : type
  | TNat : type
  | TInt : type
  | TBool : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type
  | TRec : type → type
  | TForall : type → type
  | TExists : type → type
  | TVar : ℕ → type
  | TRef : type → type
  | TTape : type
deriving DecidableEq, Repr, Inhabited

export type (TUnit TNat TInt TBool TProd TSum TArrow TRec TForall TExists TVar TRef TTape)

/-- Rocq: `UnboxedType`. Which types are unboxed -- we can only do CAS on locations which hold
unboxed types. -/
inductive UnboxedType : type → Prop where
  | UnboxedTUnit : UnboxedType TUnit
  | UnboxedTNat : UnboxedType TNat
  | UnboxedTInt : UnboxedType TInt
  | UnboxedTBool : UnboxedType TBool
  | UnboxedTRef (τ : type) : UnboxedType (TRef τ)

export UnboxedType (UnboxedTUnit UnboxedTNat UnboxedTInt UnboxedTBool UnboxedTRef)

/-- Rocq: `EqType`. Types which support direct equality test (which coincides with ctx
equiv). This is an auxiliary notion. -/
inductive EqType : type → Prop where
  | EqTUnit : EqType TUnit
  | EqTNat : EqType TNat
  | EqTInt : EqType TInt
  | EqTBool : EqType TBool
  | EqTProd (τ τ' : type) : EqType τ → EqType τ' → EqType (TProd τ τ')
  | EqSum (τ τ' : type) : EqType τ → EqType τ' → EqType (TSum τ τ')

export EqType (EqTUnit EqTNat EqTInt EqTBool EqTProd EqSum)

/-- Rocq: `unboxed_type_ref_or_eqtype`. -/
theorem unboxed_type_ref_or_eqtype (τ : type) :
    UnboxedType τ → (EqType τ ∨ (∃ τ', τ = TRef τ')) := by
  intro h
  cases h with
  | UnboxedTRef τ' => exact Or.inr ⟨τ', rfl⟩
  | _ => left; constructor

/-! ## Substitution (replacing the Autosubst instances) -/

namespace type

/-- Autosubst `ids` (Rocq: `Ids_type`). -/
abbrev ids : ℕ → type := TVar

/-- Autosubst `upren`: lifting a renaming under a binder. -/
def upren (ξ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Autosubst `rename` (Rocq: `Rename_type`). -/
def rename (ξ : ℕ → ℕ) : type → type
  | TUnit => TUnit
  | TNat => TNat
  | TInt => TInt
  | TBool => TBool
  | TProd τ1 τ2 => TProd (rename ξ τ1) (rename ξ τ2)
  | TSum τ1 τ2 => TSum (rename ξ τ1) (rename ξ τ2)
  | TArrow τ1 τ2 => TArrow (rename ξ τ1) (rename ξ τ2)
  | TRec τ => TRec (rename (upren ξ) τ)
  | TForall τ => TForall (rename (upren ξ) τ)
  | TExists τ => TExists (rename (upren ξ) τ)
  | TVar x => TVar (ξ x)
  | TRef τ => TRef (rename ξ τ)
  | TTape => TTape

/-- Autosubst `ren ξ = ids ∘ ξ`: a renaming seen as a substitution. -/
abbrev ren (ξ : ℕ → ℕ) : ℕ → type := fun n => ids (ξ n)

/-- Autosubst `up`: lifting a substitution under a binder. -/
def up (σ : ℕ → type) : ℕ → type
  | 0 => TVar 0
  | n + 1 => rename Nat.succ (σ n)

/-- Autosubst `subst` (Rocq: `Subst_type`). Rocq `τ.[σ]` is `subst σ τ`. -/
def subst (σ : ℕ → type) : type → type
  | TUnit => TUnit
  | TNat => TNat
  | TInt => TInt
  | TBool => TBool
  | TProd τ1 τ2 => TProd (subst σ τ1) (subst σ τ2)
  | TSum τ1 τ2 => TSum (subst σ τ1) (subst σ τ2)
  | TArrow τ1 τ2 => TArrow (subst σ τ1) (subst σ τ2)
  | TRec τ => TRec (subst (up σ) τ)
  | TForall τ => TForall (subst (up σ) τ)
  | TExists τ => TExists (subst (up σ) τ)
  | TVar x => σ x
  | TRef τ => TRef (subst σ τ)
  | TTape => TTape

/-- Autosubst `scons` (`τ .: σ`). -/
def scons (τ : type) (σ : ℕ → type) : ℕ → type
  | 0 => τ
  | n + 1 => σ n

@[inherit_doc] scoped infixr:55 " .: " => scons

@[simp] theorem scons_zero (τ : type) (σ : ℕ → type) : scons τ σ 0 = τ := rfl
@[simp] theorem scons_succ (τ : type) (σ : ℕ → type) (n : ℕ) : scons τ σ (n + 1) = σ n := rfl
@[simp] theorem upren_zero (ξ : ℕ → ℕ) : upren ξ 0 = 0 := rfl
@[simp] theorem upren_succ (ξ : ℕ → ℕ) (n : ℕ) : upren ξ (n + 1) = ξ n + 1 := rfl
@[simp] theorem up_zero (σ : ℕ → type) : up σ 0 = TVar 0 := rfl
@[simp] theorem up_succ (σ : ℕ → type) (n : ℕ) : up σ (n + 1) = rename Nat.succ (σ n) := rfl

theorem up_ren (ξ : ℕ → ℕ) : up (ren ξ) = ren (upren ξ) := by
  funext n; cases n <;> rfl

/-- Autosubst `SubstLemmas.rename_subst`. -/
theorem rename_subst (ξ : ℕ → ℕ) (τ : type) : rename ξ τ = subst (ren ξ) τ := by
  induction τ generalizing ξ <;> simp_all [rename, subst, up_ren]

theorem up_ids : up ids = ids := by
  funext n; cases n <;> rfl

/-- Autosubst `SubstLemmas.subst_id`. -/
@[simp] theorem subst_id (τ : type) : subst ids τ = τ := by
  induction τ <;> simp_all [subst, up_ids]

/-- Autosubst `SubstLemmas.id_subst`. -/
@[simp] theorem id_subst (σ : ℕ → type) (x : ℕ) : subst σ (ids x) = σ x := rfl

theorem upren_comp (ξ ζ : ℕ → ℕ) : upren ξ ∘ upren ζ = upren (ξ ∘ ζ) := by
  funext n; cases n <;> rfl

theorem rename_rename (ξ ζ : ℕ → ℕ) (τ : type) :
    rename ξ (rename ζ τ) = rename (ξ ∘ ζ) τ := by
  induction τ generalizing ξ ζ <;> simp_all [rename, upren_comp]

theorem up_comp_upren (σ : ℕ → type) (ξ : ℕ → ℕ) : up σ ∘ upren ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem subst_rename (σ : ℕ → type) (ξ : ℕ → ℕ) (τ : type) :
    subst σ (rename ξ τ) = subst (σ ∘ ξ) τ := by
  induction τ generalizing σ ξ <;> simp_all [rename, subst, ← up_comp_upren]

theorem rename_up (ξ : ℕ → ℕ) (σ : ℕ → type) :
    rename (upren ξ) ∘ up σ = up (rename ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up_succ, rename_rename]
    rfl

theorem rename_subst_comm (ξ : ℕ → ℕ) (σ : ℕ → type) (τ : type) :
    rename ξ (subst σ τ) = subst (rename ξ ∘ σ) τ := by
  induction τ generalizing ξ σ <;> simp_all [rename, subst, ← rename_up]

theorem up_comp (σ θ : ℕ → type) : subst (up θ) ∘ up σ = up (subst θ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up_succ, subst_rename, rename_subst_comm]
    rfl

/-- Autosubst `SubstLemmas.subst_comp`: `τ.[σ].[θ] = τ.[σ >> θ]`. -/
theorem subst_comp (σ θ : ℕ → type) (τ : type) :
    subst θ (subst σ τ) = subst (subst θ ∘ σ) τ := by
  induction τ generalizing σ θ <;> simp_all [subst, ← up_comp]

@[simp] theorem subst_comp' (σ θ : ℕ → type) (τ : type) :
    subst θ (subst σ τ) = subst (fun x => subst θ (σ x)) τ :=
  subst_comp σ θ τ

@[simp] theorem subst_TUnit (σ : ℕ → type) : subst σ TUnit = TUnit := rfl
@[simp] theorem subst_TNat (σ : ℕ → type) : subst σ TNat = TNat := rfl
@[simp] theorem subst_TInt (σ : ℕ → type) : subst σ TInt = TInt := rfl
@[simp] theorem subst_TBool (σ : ℕ → type) : subst σ TBool = TBool := rfl
@[simp] theorem subst_TTape (σ : ℕ → type) : subst σ TTape = TTape := rfl
@[simp] theorem subst_TVar (σ : ℕ → type) (x : ℕ) : subst σ (TVar x) = σ x := rfl
@[simp] theorem subst_TProd (σ : ℕ → type) (τ1 τ2 : type) :
    subst σ (TProd τ1 τ2) = TProd (subst σ τ1) (subst σ τ2) := rfl
@[simp] theorem subst_TSum (σ : ℕ → type) (τ1 τ2 : type) :
    subst σ (TSum τ1 τ2) = TSum (subst σ τ1) (subst σ τ2) := rfl
@[simp] theorem subst_TArrow (σ : ℕ → type) (τ1 τ2 : type) :
    subst σ (TArrow τ1 τ2) = TArrow (subst σ τ1) (subst σ τ2) := rfl
@[simp] theorem subst_TRec (σ : ℕ → type) (τ : type) :
    subst σ (TRec τ) = TRec (subst (up σ) τ) := rfl
@[simp] theorem subst_TForall (σ : ℕ → type) (τ : type) :
    subst σ (TForall τ) = TForall (subst (up σ) τ) := rfl
@[simp] theorem subst_TExists (σ : ℕ → type) (τ : type) :
    subst σ (TExists τ) = TExists (subst (up σ) τ) := rfl
@[simp] theorem subst_TRef (σ : ℕ → type) (τ : type) :
    subst σ (TRef τ) = TRef (subst σ τ) := rfl

end type

open type in
/-- Rocq (Autosubst): `τ.[τ'/]`, i.e. `τ.[τ' .: ids]`. -/
scoped notation:max τ:max ".[" τ' "/]" => type.subst (type.scons τ' type.ids) τ

/-- Rocq's `asimpl` (Autosubst), as a `simp` call with the substitution lemmas. -/
macro "asimpl" : tactic =>
  `(tactic| simp only [type.subst_comp', type.rename_subst, type.id_subst, type.subst_id,
    type.subst_TUnit, type.subst_TNat, type.subst_TInt, type.subst_TBool, type.subst_TTape,
    type.subst_TVar, type.subst_TProd, type.subst_TSum, type.subst_TArrow, type.subst_TRec,
    type.subst_TForall, type.subst_TExists, type.subst_TRef, type.scons_zero, type.scons_succ,
    type.up_zero, type.up_succ, type.upren_zero, type.upren_succ])

/-! ## Result types of operators -/

/-- Rocq: `binop_int_res_type`. -/
def binop_int_res_type (op : bin_op) : Option type :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => some TInt
  | AndOp | OrOp | XorOp => none
  | ShiftLOp | ShiftROp => some TInt
  | LeOp | LtOp | EqOp => some TBool
  | OffsetOp => some TInt

/-- Rocq: `binop_bool_res_type`. -/
def binop_bool_res_type (op : bin_op) : Option type :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => none
  | AndOp | OrOp | XorOp => some TBool
  | ShiftLOp | ShiftROp => none
  | LeOp | LtOp => none
  | EqOp => some TBool
  | OffsetOp => none

/-- Rocq: `unop_int_res_type`. -/
def unop_int_res_type (op : un_op) : Option type :=
  match op with
  | NegOp => none
  | MinusUnOp => some TInt

/-- Rocq: `unop_bool_res_type`. -/
def unop_bool_res_type (op : un_op) : Option type :=
  match op with
  | NegOp => some TBool
  | MinusUnOp => none

/-! ## Typing contexts -/

/-- Rocq (stdpp): `dom` of a `stringmap`, as a `stringset`. -/
def dom {V : Type} (Γ : varmap V) : stringset := Γ.keys.toFinset

@[simp] theorem mem_dom {V : Type} (Γ : varmap V) (x : String) : x ∈ dom Γ ↔ x ∈ Γ := by
  simp [dom, Std.ExtTreeMap.mem_keys]

theorem dom_binder_insert {V : Type} (b : binder) (v : V) (Γ : varmap V) :
    dom (binder_insert b v Γ) = set_binder_insert b (dom Γ) := by
  ext y
  cases b with
  | BAnon => simp [binder_insert, set_binder_insert]
  | BNamed x =>
    simp only [binder_insert, set_binder_insert, Std.ExtTreeMap.mem_insert,
      Std.compare_eq_iff_eq, Finset.mem_insert, mem_dom]
    exact or_congr_left eq_comm

@[simp] theorem dom_empty {V : Type} : dom (∅ : varmap V) = ∅ := by
  ext y; simp

/-- Rocq: `⤉ Γ` (`subst (ren (+1)) <$> Γ`). Shift all the indices in the context by one,
used when inserting a new type interpretation in `Δ`. -/
def type_shift_ctx (Γ : varmap type) : varmap type :=
  Γ.map fun _ τ => type.subst (type.ren (· + 1)) τ

@[inherit_doc] scoped notation:max "⤉" Γ:max => type_shift_ctx Γ

@[simp] theorem dom_type_shift_ctx (Γ : varmap type) : dom (⤉Γ) = dom Γ := by
  ext y; simp [type_shift_ctx, Std.ExtTreeMap.mem_map]

@[simp] theorem lookup_type_shift_ctx (Γ : varmap type) (x : String) :
    (⤉Γ)[x]? = (Γ[x]?).map (type.subst (type.ren (· + 1))) := by
  simp [type_shift_ctx, Std.ExtTreeMap.getElem?_map]

/-! ## Derived forms -/

/-- Rocq: `Λ: e` (expression). We model type-level lambdas as thunks. -/
abbrev TLam (e : expr) : expr := Lam BAnon e
/-- Rocq: `Λ: e` (value). -/
abbrev TLamV (e : expr) : val := LamV BAnon e
/-- Rocq: `TApp e`. Type-level application. -/
abbrev TApp (e : expr) : expr := App e (Val (LitV LitUnit))

/-- Rocq: `rec_unfold`. To unfold a recursive type, we need to take a step. We thus define
the unfold operator to be the identity function. -/
def rec_unfold : val := LamV (BNamed "x") (Var "x")

/-- Rocq: `unpack`. -/
def unpack : val := LamV (BNamed "x") (Lam (BNamed "y") (App (Var "y") (Var "x")))

/-- Rocq: `unpack: x := e1 in e2` (expression). -/
abbrev Unpack (x : binder) (e1 e2 : expr) : expr := App (App (Val unpack) e1) (Lam x e2)

/-- Rocq: `unpack: x := e1 in e2` (value form, second notation in `types.v`, with `LamV`). -/
abbrev UnpackV (x : binder) (e1 e2 : expr) : expr :=
  App (App (Val unpack) e1) (Val (LamV x e2))

/-! ## Typing judgements -/

mutual
/-- Rocq: `typed` (notation `Γ ⊢ₜ e : τ`). -/
inductive typed : varmap type → expr → type → Prop where
  | Var_typed (Γ : varmap type) (x : String) (τ : type) :
      Γ[x]? = some τ →
      typed Γ (Var x) τ
  | Val_typed (Γ : varmap type) (v : val) (τ : type) :
      val_typed v τ →
      typed Γ (Val v) τ
  | BinOp_typed_int (Γ : varmap type) (op : bin_op) (e1 e2 : expr) (τ : type) :
      typed Γ e1 TInt → typed Γ e2 TInt →
      binop_int_res_type op = some τ →
      typed Γ (BinOp op e1 e2) τ
  | BinOp_typed_bool (Γ : varmap type) (op : bin_op) (e1 e2 : expr) (τ : type) :
      typed Γ e1 TBool → typed Γ e2 TBool →
      binop_bool_res_type op = some τ →
      typed Γ (BinOp op e1 e2) τ
  -- NB: The typing rule for Offsets is not safe (commented out in Rocq).
  | UnOp_typed_int (Γ : varmap type) (op : un_op) (e : expr) (τ : type) :
      typed Γ e TInt →
      unop_int_res_type op = some τ →
      typed Γ (UnOp op e) τ
  | UnOp_typed_bool (Γ : varmap type) (op : un_op) (e : expr) (τ : type) :
      typed Γ e TBool →
      unop_bool_res_type op = some τ →
      typed Γ (UnOp op e) τ
  | UnboxedEq_typed (Γ : varmap type) (e1 e2 : expr) (τ : type) :
      UnboxedType τ →
      typed Γ e1 τ → typed Γ e2 τ →
      typed Γ (BinOp EqOp e1 e2) TBool
  | Pair_typed (Γ : varmap type) (e1 e2 : expr) (τ1 τ2 : type) :
      typed Γ e1 τ1 → typed Γ e2 τ2 →
      typed Γ (Pair e1 e2) (TProd τ1 τ2)
  | Fst_typed (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
      typed Γ e (TProd τ1 τ2) →
      typed Γ (Fst e) τ1
  | Snd_typed (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
      typed Γ e (TProd τ1 τ2) →
      typed Γ (Snd e) τ2
  | InjL_typed (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
      typed Γ e τ1 →
      typed Γ (InjL e) (TSum τ1 τ2)
  | InjR_typed (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
      typed Γ e τ2 →
      typed Γ (InjR e) (TSum τ1 τ2)
  | Case_typed (Γ : varmap type) (e0 e1 e2 : expr) (τ1 τ2 τ3 : type) :
      typed Γ e0 (TSum τ1 τ2) →
      typed Γ e1 (TArrow τ1 τ3) →
      typed Γ e2 (TArrow τ2 τ3) →
      typed Γ (Case e0 e1 e2) τ3
  | If_typed (Γ : varmap type) (e0 e1 e2 : expr) (τ : type) :
      typed Γ e0 TBool →
      typed Γ e1 τ →
      typed Γ e2 τ →
      typed Γ (If e0 e1 e2) τ
  | Rec_typed (Γ : varmap type) (f x : binder) (e : expr) (τ1 τ2 : type) :
      typed (binder_insert f (TArrow τ1 τ2) (binder_insert x τ1 Γ)) e τ2 →
      typed Γ (Rec f x e) (TArrow τ1 τ2)
  | App_typed (Γ : varmap type) (e1 e2 : expr) (τ1 τ2 : type) :
      typed Γ e1 (TArrow τ1 τ2) →
      typed Γ e2 τ1 →
      typed Γ (App e1 e2) τ2
  | TLam_typed (Γ : varmap type) (e : expr) (τ : type) :
      typed (type_shift_ctx Γ) e τ →
      typed Γ (Rec BAnon BAnon e) (TForall τ)
  | TApp_typed (Γ : varmap type) (e : expr) (τ τ' : type) :
      typed Γ e (TForall τ) →
      typed Γ (App e (Val (LitV LitUnit))) (type.subst (type.scons τ' type.ids) τ)
  | TFold (Γ : varmap type) (e : expr) (τ : type) :
      typed Γ e (type.subst (type.scons (TRec τ) type.ids) τ) →
      typed Γ e (TRec τ)
  | TUnfold (Γ : varmap type) (e : expr) (τ : type) :
      typed Γ e (TRec τ) →
      typed Γ (App (Val rec_unfold) e) (type.subst (type.scons (TRec τ) type.ids) τ)
  | TPack (Γ : varmap type) (e : expr) (τ τ' : type) :
      typed Γ e (type.subst (type.scons τ' type.ids) τ) →
      typed Γ e (TExists τ)
  | TUnpack (Γ : varmap type) (e1 : expr) (x : binder) (e2 : expr) (τ τ2 : type) :
      typed Γ e1 (TExists τ) →
      typed (binder_insert x τ (type_shift_ctx Γ)) e2 (type.subst (type.ren (· + 1)) τ2) →
      typed Γ (App (App (Val unpack) e1) (Rec BAnon x e2)) τ2
  | TAlloc (Γ : varmap type) (e : expr) (τ : type) :
      typed Γ e τ → typed Γ (AllocN (Val (LitV (LitInt 1))) e) (TRef τ)
  | TLoad (Γ : varmap type) (e : expr) (τ : type) :
      typed Γ e (TRef τ) → typed Γ (Load e) τ
  | TStore (Γ : varmap type) (e e' : expr) (τ : type) :
      typed Γ e (TRef τ) → typed Γ e' τ → typed Γ (Store e e') TUnit
  | TAllocTape (e : expr) (Γ : varmap type) :
      typed Γ e TNat → typed Γ (AllocTape e) TTape
  | TRand (Γ : varmap type) (e1 e2 : expr) :
      typed Γ e1 TNat → typed Γ e2 TTape → typed Γ (Rand e1 e2) TNat
  | TRandU (Γ : varmap type) (e1 e2 : expr) :
      typed Γ e1 TNat → typed Γ e2 TUnit → typed Γ (Rand e1 e2) TNat
  | Subsume_int_nat (Γ : varmap type) (e : expr) :
      typed Γ e TNat → typed Γ e TInt
  | Fork_typed (Γ : varmap type) (e : expr) :
      typed Γ e TUnit → typed Γ (Fork e) TUnit
  | CmpXchg_typed (Γ : varmap type) (e1 e2 e3 : expr) (τ : type) :
      UnboxedType τ → typed Γ e1 (TRef τ) → typed Γ e2 τ → typed Γ e3 τ →
      typed Γ (CmpXchg e1 e2 e3) (TProd τ TBool)
  | Xchg_typed (Γ : varmap type) (e1 e2 : expr) (τ : type) :
      typed Γ e1 (TRef τ) → typed Γ e2 τ → typed Γ (Xchg e1 e2) τ
  | Faa_typed (Γ : varmap type) (e1 e2 : expr) :
      typed Γ e1 (TRef TNat) → typed Γ e2 TNat → typed Γ (FAA e1 e2) TNat

/-- Rocq: `val_typed` (notation `⊢ᵥ v : τ`). -/
inductive val_typed : val → type → Prop where
  | Unit_val_typed : val_typed (LitV LitUnit) TUnit
  | Int_val_typed (n : ℤ) : val_typed (LitV (LitInt n)) TInt
  | Nat_val_typed (n : ℕ) : val_typed (LitV (LitInt (n : ℤ))) TNat
  | Bool_val_typed (b : Bool) : val_typed (LitV (LitBool b)) TBool
  | Pair_val_typed (v1 v2 : val) (τ1 τ2 : type) :
      val_typed v1 τ1 →
      val_typed v2 τ2 →
      val_typed (PairV v1 v2) (TProd τ1 τ2)
  | InjL_val_typed (v : val) (τ1 τ2 : type) :
      val_typed v τ1 →
      val_typed (InjLV v) (TSum τ1 τ2)
  | InjR_val_typed (v : val) (τ1 τ2 : type) :
      val_typed v τ2 →
      val_typed (InjRV v) (TSum τ1 τ2)
  | Rec_val_typed (f x : binder) (e : expr) (τ1 τ2 : type) :
      typed (binder_insert f (TArrow τ1 τ2) (binder_insert x τ1 ∅)) e τ2 →
      val_typed (RecV f x e) (TArrow τ1 τ2)
  | TLam_val_typed (e : expr) (τ : type) :
      typed ∅ e τ →
      val_typed (RecV BAnon BAnon e) (TForall τ)
end

export typed (Var_typed Val_typed BinOp_typed_int BinOp_typed_bool UnOp_typed_int
  UnOp_typed_bool UnboxedEq_typed Pair_typed Fst_typed Snd_typed InjL_typed InjR_typed
  Case_typed If_typed Rec_typed App_typed TLam_typed TApp_typed TFold TUnfold TPack TUnpack
  TAlloc TLoad TStore TAllocTape TRand TRandU Subsume_int_nat Fork_typed CmpXchg_typed
  Xchg_typed Faa_typed)
export val_typed (Unit_val_typed Int_val_typed Nat_val_typed Bool_val_typed Pair_val_typed
  InjL_val_typed InjR_val_typed Rec_val_typed TLam_val_typed)

@[inherit_doc] scoped notation:74 Γ:75 " ⊢ₜ " e:75 " : " τ:75 => typed Γ e τ
@[inherit_doc] scoped notation:20 "⊢ᵥ " v:21 " : " τ:21 => val_typed v τ

/-! ## Safety of operators -/

/-- Rocq: `binop_int_typed_safe`. -/
theorem binop_int_typed_safe (op : bin_op) (n1 n2 : ℤ) (τ : type) :
    binop_int_res_type op = some τ →
    ∃ v, bin_op_eval op (LitV (LitInt n1)) (LitV (LitInt n2)) = some v := by
  intro h
  cases op <;> simp_all [binop_int_res_type, bin_op_eval]
  exact Or.inl trivial

/-- Rocq: `binop_bool_typed_safe`. -/
theorem binop_bool_typed_safe (op : bin_op) (b1 b2 : Bool) (τ : type) :
    binop_bool_res_type op = some τ →
    ∃ v, bin_op_eval op (LitV (LitBool b1)) (LitV (LitBool b2)) = some v := by
  intro h
  cases op <;> simp_all [binop_bool_res_type, bin_op_eval, bin_op_eval_bool]
  exact Or.inl trivial

/-- Rocq: `unop_int_typed_safe`. -/
theorem unop_int_typed_safe (op : un_op) (n : ℤ) (τ : type) :
    unop_int_res_type op = some τ → ∃ v, un_op_eval op (LitV (LitInt n)) = some v := by
  intro h
  cases op <;> simp_all [unop_int_res_type, un_op_eval]

/-- Rocq: `unop_bool_typed_safe`. -/
theorem unop_bool_typed_safe (op : un_op) (b : Bool) (τ : type) :
    unop_bool_res_type op = some τ → ∃ v, un_op_eval op (LitV (LitBool b)) = some v := by
  intro h
  cases op <;> simp_all [unop_bool_res_type, un_op_eval]

/-! ## Typed terms are closed -/

@[simp] theorem set_binder_BAnon (X : stringset) : set_binder_insert BAnon X = X := rfl

theorem rec_unfold_closed : is_closed_val rec_unfold = true := by
  simp [rec_unfold, is_closed_val, is_closed_expr, set_binder_insert]

theorem unpack_closed : is_closed_val unpack = true := by
  simp [unpack, is_closed_val, is_closed_expr, set_binder_insert]

mutual
/-- Rocq: `typed_is_closed_expr`. -/
theorem typed_is_closed_expr (Γ : varmap type) (τ : type) (x : expr) :
    typed Γ x τ → is_closed_expr (dom Γ) x = true
  | .Var_typed _ x τ h => by
    simp [is_closed_expr, Std.ExtTreeMap.mem_iff_isSome_getElem?, h]
  | .Val_typed _ v τ h => by
    simpa [is_closed_expr] using typed_is_closed_val _ _ h
  | .BinOp_typed_int _ op e1 e2 τ h1 h2 _ => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .BinOp_typed_bool _ op e1 e2 τ h1 h2 _ => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .UnOp_typed_int _ op e τ h1 _ => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .UnOp_typed_bool _ op e τ h1 _ => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .UnboxedEq_typed _ e1 e2 τ _ h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .Pair_typed _ e1 e2 τ1 τ2 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .Fst_typed _ e τ1 τ2 h1 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .Snd_typed _ e τ1 τ2 h1 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .InjL_typed _ e τ1 τ2 h1 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .InjR_typed _ e τ1 τ2 h1 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .Case_typed _ e0 e1 e2 τ1 τ2 τ3 h0 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h0, typed_is_closed_expr _ _ _ h1,
      typed_is_closed_expr _ _ _ h2]
  | .If_typed _ e0 e1 e2 τ h0 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h0, typed_is_closed_expr _ _ _ h1,
      typed_is_closed_expr _ _ _ h2]
  | .Rec_typed _ f x e τ1 τ2 h1 => by
    have := typed_is_closed_expr _ _ _ h1
    simpa [is_closed_expr, dom_binder_insert] using this
  | .App_typed _ e1 e2 τ1 τ2 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .TLam_typed _ e τ h1 => by
    have := typed_is_closed_expr _ _ _ h1
    simpa [is_closed_expr, set_binder_insert] using this
  | .TApp_typed _ e τ τ' h1 => by
    simp [is_closed_expr, is_closed_val, typed_is_closed_expr _ _ _ h1]
  | .TFold _ e τ h1 => typed_is_closed_expr _ _ _ h1
  | .TUnfold _ e τ h1 => by
    simp [is_closed_expr, rec_unfold_closed, typed_is_closed_expr _ _ _ h1]
  | .TPack _ e τ τ' h1 => typed_is_closed_expr _ _ _ h1
  | .TUnpack _ e1 x e2 τ τ2 h1 h2 => by
    have := typed_is_closed_expr _ _ _ h2
    simp only [dom_binder_insert, dom_type_shift_ctx] at this
    simp [is_closed_expr, unpack_closed, typed_is_closed_expr _ _ _ h1, set_binder_BAnon, this]
  | .TAlloc _ e τ h1 => by
    simp [is_closed_expr, is_closed_val, typed_is_closed_expr _ _ _ h1]
  | .TLoad _ e τ h1 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .TStore _ e1 e2 τ h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .TAllocTape e _ h1 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .TRand _ e1 e2 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .TRandU _ e1 e2 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .Subsume_int_nat _ e h1 => typed_is_closed_expr _ _ _ h1
  | .Fork_typed _ e h1 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1]
  | .CmpXchg_typed _ e0 e1 e2 τ _ h0 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h0, typed_is_closed_expr _ _ _ h1,
      typed_is_closed_expr _ _ _ h2]
  | .Xchg_typed _ e1 e2 τ h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]
  | .Faa_typed _ e1 e2 h1 h2 => by
    simp [is_closed_expr, typed_is_closed_expr _ _ _ h1, typed_is_closed_expr _ _ _ h2]

/-- Rocq: `typed_is_closed_val`. -/
theorem typed_is_closed_val (τ : type) (v : val) : val_typed v τ → is_closed_val v = true
  | .Unit_val_typed => rfl
  | .Int_val_typed _ => rfl
  | .Nat_val_typed _ => rfl
  | .Bool_val_typed _ => rfl
  | .Pair_val_typed v1 v2 τ1 τ2 h1 h2 => by
    simp [is_closed_val, typed_is_closed_val _ _ h1, typed_is_closed_val _ _ h2]
  | .InjL_val_typed v τ1 τ2 h1 => by
    simp [is_closed_val, typed_is_closed_val _ _ h1]
  | .InjR_val_typed v τ1 τ2 h1 => by
    simp [is_closed_val, typed_is_closed_val _ _ h1]
  | .Rec_val_typed f x e τ1 τ2 h1 => by
    have := typed_is_closed_expr _ _ _ h1
    simpa [is_closed_val, dom_binder_insert] using this
  | .TLam_val_typed e τ h1 => by
    have := typed_is_closed_expr _ _ _ h1
    simpa [is_closed_val, set_binder_insert] using this
end

end con_prob_lang

end ConProbLang
