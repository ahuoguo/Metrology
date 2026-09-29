module

public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart3

/-!
# The fundamental theorem of Foxtrot's binary logical relation (part 4)

Ported from clutch/theories/foxtrot/binary_rel/binary_fundamental.v (lines 617-864:
`fundamental`, `fundamental_val`, `refines_typed`, `bin_log_related_under_typed_ctx`).

## Rocq → Lean map
All Rocq names are kept (namespace `Foxtrot.BinaryRel`).

## Deviations
* `fundamental`/`fundamental_val` (Rocq: `Theorem .. with ..`, by `destruct` on the typing
  derivation) are a `mutual` pair of theorems defined by structural recursion on the typing
  derivations.
* The Iris-level applications `iApply lem; by iApply fundamental` are Lean-level compositions
  with the added helpers `fundamental_ent2`/`fundamental_ent3`.
* In `fundamental_val` the recursive-function and type-abstraction cases go through the added
  helper `bin_log_related_empty` (the empty-environment instance, Rocq: inlined `iPoseProof`
  with `env_ltyped2_empty` and `subst_map_empty`).
* `bin_log_related_under_typed_ctx` is proved by induction on the typed context derivation
  (Rocq: induction on `K` and inversion).

## Added helpers
* `varmap_map_empty`, `bin_log_related_empty`, `fundamental_ent2`, `fundamental_ent3`.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

/-- Added: mapping over the empty `varmap`. -/
theorem varmap_map_empty {A B : Type} (f : String → A → B) :
    (∅ : varmap A).map f = ∅ := by
  apply Std.ExtTreeMap.ext_getElem?
  intro y
  simp

section fundamental

variable {GF : BundledGFunctors} [foxtrotRGS GF]

omit [foxtrotRGS GF] in
/-- Added: composition of a binary compatibility lemma with two closed proofs. -/
theorem fundamental_ent2 {P Q R : IProp GF} (h : P ⊢ Q -∗ R) (hp : ⊢ P) (hq : ⊢ Q) : ⊢ R :=
  hq.trans (wand_entails (hp.trans h))

omit [foxtrotRGS GF] in
/-- Added: composition of a ternary compatibility lemma with three closed proofs. -/
theorem fundamental_ent3 {P Q R S : IProp GF} (h : P ⊢ Q -∗ R -∗ S) (hp : ⊢ P) (hq : ⊢ Q)
    (hr : ⊢ R) : ⊢ S :=
  fundamental_ent2 (wand_entails (hp.trans h)) hq hr

/-- Added: a semantic typing judgement in the empty environment gives a refinement. -/
theorem bin_log_related_empty (Δ : List (lrel GF)) (e e' : expr) (τ : type)
    (H : ⊢ 〈Δ;∅〉 ⊨ e ≤log≤ e' : τ) : ⊢ REL e << e' : interp τ Δ := by
  unfold bin_log_related at H
  have H2 := H.trans (forall_elim (∅ : varmap (val × val)))
  simp only [varmap_map_empty, subst_map_empty] at H2
  exact env_ltyped2_empty.trans (wand_entails H2)

mutual

/-- Rocq: `fundamental`. -/
theorem fundamental (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ : type) :
    Γ ⊢ₜ e : τ → ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e : τ
  | .Var_typed _ x τ h => bin_log_related_var Δ Γ x τ h
  | .Val_typed _ v τ h => by
    unfold bin_log_related
    iintro %vs #-
    simp only [subst_map]
    iapply refines_ret (Val v) (Val v) v v
    imodintro
    iapply fundamental_val Δ v τ h
  | .BinOp_typed_int _ op e1 e2 τ h1 h2 hop =>
    fundamental_ent2 (bin_log_related_int_binop Δ Γ op e1 e2 e1 e2 τ hop)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .BinOp_typed_bool _ op e1 e2 τ h1 h2 hop =>
    fundamental_ent2 (bin_log_related_bool_binop Δ Γ op e1 e2 e1 e2 τ hop)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .UnOp_typed_int _ op e τ h1 hop =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_int_unop Δ Γ op e e τ hop)
  | .UnOp_typed_bool _ op e τ h1 hop =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_bool_unop Δ Γ op e e τ hop)
  | .UnboxedEq_typed _ e1 e2 τ hu h1 h2 =>
    fundamental_ent2 (bin_log_related_unboxed_eq Δ Γ e1 e2 e1 e2 τ hu)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .Pair_typed _ e1 e2 τ1 τ2 h1 h2 =>
    fundamental_ent2 (bin_log_related_pair Δ Γ e1 e2 e1 e2 τ1 τ2)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .Fst_typed _ e τ1 τ2 h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_fst Δ Γ e e τ1 τ2)
  | .Snd_typed _ e τ1 τ2 h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_snd Δ Γ e e τ1 τ2)
  | .InjL_typed _ e τ1 τ2 h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_injl Δ Γ e e τ1 τ2)
  | .InjR_typed _ e τ1 τ2 h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_injr Δ Γ e e τ1 τ2)
  | .Case_typed _ e0 e1 e2 τ1 τ2 τ3 h0 h1 h2 =>
    fundamental_ent3 (bin_log_related_case Δ Γ e0 e1 e2 e0 e1 e2 τ1 τ2 τ3)
      (fundamental Δ Γ e0 _ h0) (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .If_typed _ e0 e1 e2 τ h0 h1 h2 =>
    fundamental_ent3 (bin_log_related_if Δ Γ e0 e1 e2 e0 e1 e2 τ)
      (fundamental Δ Γ e0 _ h0) (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .Rec_typed _ f x e τ1 τ2 h1 => by
    have IH := fundamental Δ _ e τ2 h1
    iapply bin_log_related_rec
    imodintro
    iapply IH
  | .App_typed _ e1 e2 τ1 τ2 h1 h2 =>
    fundamental_ent2 (bin_log_related_app Δ Γ e1 e2 e1 e2 τ1 τ2)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .TLam_typed _ e τ h1 => by
    have IH := fun A => fundamental (A :: Δ) _ e τ h1
    iapply bin_log_related_tlam
    iintro %A
    imodintro
    iapply IH A
  | .TApp_typed _ e τ τ' h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_tapp' Δ Γ e e τ τ')
  | .TFold _ e τ h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_fold Δ Γ e e τ)
  | .TUnfold _ e τ h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_unfold Δ Γ e e τ)
  | .TPack _ e τ τ' h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_pack' Δ Γ e e τ τ')
  | .TUnpack _ e1 x e2 τ τ2 h1 h2 => by
    have IH2 := fun A => fundamental (A :: Δ) _ e2 _ h2
    refine fundamental_ent2 (bin_log_related_unpack Δ Γ x e1 e1 e2 e2 τ τ2)
      (fundamental Δ Γ e1 _ h1) ?_
    iintro %A
    iapply IH2 A
  | .TAlloc _ e τ h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_alloc Δ Γ e e τ)
  | .TLoad _ e τ h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_load Δ Γ e e τ)
  | .TStore _ e1 e2 τ h1 h2 =>
    fundamental_ent2 (bin_log_related_store Δ Γ e1 e2 e1 e2 τ)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .TAllocTape e _ h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_alloctape Δ Γ e e)
  | .TRand _ e1 e2 h1 h2 =>
    fundamental_ent2 (bin_log_related_rand_tape Δ Γ e1 e1 e2 e2)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .TRandU _ e1 e2 h1 h2 =>
    fundamental_ent2 (bin_log_related_rand_unit Δ Γ e1 e1 e2 e2)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .Subsume_int_nat _ e h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_subsume_int_nat Δ Γ e e)
  | .Fork_typed _ e h1 =>
    (fundamental Δ Γ e _ h1).trans (bin_log_related_fork Δ Γ e e)
  | .CmpXchg_typed _ e1 e2 e3 τ hu h1 h2 h3 =>
    fundamental_ent3 (bin_log_related_CmpXchg Δ Γ e1 e2 e3 e1 e2 e3 τ hu)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2) (fundamental Δ Γ e3 _ h3)
  | .Xchg_typed _ e1 e2 τ h1 h2 =>
    fundamental_ent2 (bin_log_related_xchg Δ Γ e1 e2 e1 e2 τ)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)
  | .Faa_typed _ e1 e2 h1 h2 =>
    fundamental_ent2 (bin_log_related_FAA Δ Γ e1 e2 e1 e2)
      (fundamental Δ Γ e1 _ h1) (fundamental Δ Γ e2 _ h2)

/-- Rocq: `fundamental_val`. -/
theorem fundamental_val (Δ : List (lrel GF)) (v : val) (τ : type) :
    val_typed v τ → ⊢ interp τ Δ v v
  | .Unit_val_typed => by
    rw [interp_TUnit]
    dsimp only [lrel_unit]
    ipureintro
    exact ⟨rfl, rfl⟩
  | .Int_val_typed n => by
    rw [interp_TInt]
    dsimp only [lrel_int]
    iexists n
    ipureintro
    exact ⟨rfl, rfl⟩
  | .Nat_val_typed n => by
    rw [interp_TNat]
    dsimp only [lrel_nat]
    iexists n
    ipureintro
    exact ⟨rfl, rfl⟩
  | .Bool_val_typed b => by
    rw [interp_TBool]
    dsimp only [lrel_bool]
    iexists b
    ipureintro
    exact ⟨rfl, rfl⟩
  | .Pair_val_typed v1 v2 τ1 τ2 h1 h2 => by
    have IH1 := fundamental_val Δ v1 τ1 h1
    have IH2 := fundamental_val Δ v2 τ2 h2
    rw [interp_TProd]
    dsimp only [lrel_prod]
    iexists v1, v1, v2, v2
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply IH1
    · iapply IH2
  | .InjL_val_typed v τ1 τ2 h1 => by
    have IH := fundamental_val Δ v τ1 h1
    rw [interp_TSum]
    dsimp only [lrel_sum]
    iexists v, v
    ileft
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    iapply IH
  | .InjR_val_typed v τ1 τ2 h1 => by
    have IH := fundamental_val Δ v τ2 h1
    rw [interp_TSum]
    dsimp only [lrel_sum]
    iexists v, v
    iright
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    iapply IH
  | .Rec_val_typed f x e τ1 τ2 h1 => by
    have He := fundamental Δ _ e τ2 h1
    rw [interp_TArrow]
    dsimp only [lrel_arr]
    imodintro
    iloeb as IH
    iintro %v1 %v2 #Hv
    have hl : ▷^[1] (REL subst' x v1 (subst' f (RecV f x e) e) <<
          App (Val (RecV f x e)) (Val v2) : interp τ2 Δ) ⊢
        REL App (Val (RecV f x e)) (Val v1) << App (Val (RecV f x e)) (Val v2) :
          interp τ2 Δ :=
      refines_pure_l 1 [] _ _ _ _ True trivial
    have hr : (REL subst' x v1 (subst' f (RecV f x e) e) <<
          subst' x v2 (subst' f (RecV f x e) e) : interp τ2 Δ) ⊢
        REL subst' x v1 (subst' f (RecV f x e) e) << App (Val (RecV f x e)) (Val v2) :
          interp τ2 Δ :=
      refines_pure_r [] _ _ _ _ 1 True trivial
    iapply hl
    inext
    iapply hr
    let γ : varmap (val × val) :=
      binder_insert f (RecV f x e, RecV f x e) (binder_insert x (v1, v2) ∅)
    have h1 : subst' x v1 (subst' f (RecV f x e) e) =
        subst_map (γ.map fun _ p => p.1) e := by
      rw [binder_insert_fmap, binder_insert_fmap, varmap_map_empty,
        subst_map_binder_insert_2_empty]
    have h2 : subst' x v2 (subst' f (RecV f x e) e) =
        subst_map (γ.map fun _ p => p.2) e := by
      rw [binder_insert_fmap, binder_insert_fmap, varmap_map_empty,
        subst_map_binder_insert_2_empty]
    rw [h1, h2]
    unfold bin_log_related at He
    iapply He $$ %γ
    rw [binder_insert_fmap, binder_insert_fmap, varmap_map_empty]
    iapply env_ltyped2_insert $$ [IH]
    · rw [interp_TArrow]
      dsimp only [lrel_arr]
      imodintro
      iexact IH
    · iapply env_ltyped2_insert $$ Hv
      iapply env_ltyped2_empty
  | .TLam_val_typed e τ h1 => by
    have He := fun A => bin_log_related_empty (A :: Δ) e e τ (fundamental (A :: Δ) ∅ e τ h1)
    rw [interp_TForall]
    dsimp only [lrel_forall, lrel_arr]
    iintro %A
    imodintro
    iintro %v1 %v2 -
    rel_pures_l
    rel_pures_r
    iapply He A

end

/-- Rocq: `refines_typed`. -/
theorem refines_typed (τ : type) (Δ : List (lrel GF)) (e : expr) (Hty : ∅ ⊢ₜ e : τ) :
    ⊢ REL e << e : interp τ Δ :=
  bin_log_related_empty Δ e e τ (fundamental Δ ∅ e τ Hty)

end fundamental

end Foxtrot.BinaryRel
