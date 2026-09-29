module

public import Metrology.Foxtrot.UnaryRel.UnaryCompatibility
public import Metrology.Foxtrot.UnaryRel.UnaryInterp

/-!
# The fundamental theorem of the unary logical relation of Foxtrot

Ported from clutch/theories/foxtrot/unary_rel/unary_fundamental.v

Compatibility lemmas for the semantic typing judgement `〈 Δ ; Γ 〉 ⊨ e : τ` (namespace
`Foxtrot.UnaryRel`) and the fundamental theorem: well-typed terms are semantically well-typed
(and hence safe, `typed_safe`).

## Rocq → Lean map
`bin_log_related_var`, `bin_log_related_pair`, `bin_log_related_fst`, `bin_log_related_snd`,
`bin_log_related_app`, `bin_log_related_rec`, `bin_log_related_tlam`, `bin_log_related_tapp'`,
`bin_log_related_tapp`, `bin_log_related_seq`, `bin_log_related_seq'`, `bin_log_related_injl`,
`bin_log_related_injr`, `bin_log_related_case`, `bin_log_related_if`, `bin_log_related_load`,
`bin_log_related_store`, `bin_log_related_alloc`, `bin_log_related_alloctape`,
`bin_log_related_rand_tape`, `bin_log_related_rand_unit`, `bin_log_related_subsume_int_nat`,
`bin_log_related_unboxed_eq`, `bin_log_related_int_binop`, `bin_log_related_bool_binop`,
`bin_log_related_int_unop`, `bin_log_related_bool_unop`, `bin_log_related_unfold`,
`bin_log_related_fold`, `bin_log_related_pack'`, `bin_log_related_pack`,
`bin_log_related_unpack`, `bin_log_related_fork`, `bin_log_related_CmpXchg_EqType`,
`bin_log_related_CmpXchg`, `bin_log_related_xchg`, `bin_log_related_FAA`, `fundamental`,
`fundamental_val`, `refines_typed`, `typed_safe`: same names and argument order.
* Types are written with the constructors (`TProd τ1 τ2` for `τ1 * τ2`, `TArrow` for `→`,
  `TForall` for `∀:`, `TExists` for `∃:`, `TRec` for `μ:`, `TUnit` for `()`); `τ.[ren (+1)]` is
  `type.subst (type.ren (· + 1)) τ`. Expressions: `Λ: e` is `TLam e`, `unpack: x := e1 in e2` is
  `App (App (Val unpack) e1) (Lam x e2)`, `rec_unfold e` is `App (Val rec_unfold) e`,
  `ref e` is `Alloc e`, `alloc e` is `AllocTape e`.
* The local tactics `intro_clause` (`iIntros (vs) "#Hvs /="`) and `value_case` are inlined:
  `unfold bin_log_related; iintro .. %vs #Hvs; simp only [subst_map]` and
  `rel_pure_l; rel_values`. `rel_bind_ap` is a local macro (as in `UnaryCompatibility`).

## Deviations
* Rocq's `P -∗ Q` lemma statements are entailments `P ⊢ Q` (`⊢ P` for closed ones); side
  conditions come before the propositions.
* The Rocq `with` pair `fundamental`/`fundamental_val` is a Lean `mutual` block, by structural
  recursion on the (mutual) typing derivations.
* Where Rocq applies `rel_pure_l` to a β-redex `(rec f x := e) v` with an opaque body and
  binders, the proofs apply `refines_pure` with `pure_beta` directly (Rocq: `rel_pure_l` +
  `rewrite subst_map_binder_insert_2`), since `rel_pure_l` unfolds `subst'` on variable binders;
  the operator cases apply `refines_pure` with `pure_binop`/`pure_unop` (Rocq: `rel_pures_l`),
  and their result is interpreted by the added `binop_int_res_interp` etc. (Rocq:
  `destruct op; inversion Hopv'; ...`).
* `bin_log_related_tapp`, `bin_log_related_case`: instead of reusing `bin_log_related_app`
  (with a nested `iApply .. with "Hvs"`), the proofs apply `refines_app` / the `∀`-instance
  directly, which is the same argument.
* `bin_log_related_rand_tape`: the natural-number argument need not be destructed.
* `bin_log_related_unfold`/`fold` use the added `interp_TRec_unfold`
  (Rocq: `rewrite lrel_rec_unfold /lrel_car`).
* `bin_log_related_CmpXchg_EqType`, `bin_log_related_FAA`: as in `UnaryCompatibility`, the
  `iApply wp_pupd` detour of Rocq is omitted.
* `bin_log_related_unpack`: the final `refines_wand` with the equivalence
  `interp_ren_up [] Δ τ2 A` is a rewrite with that equation.

## Added (not in Rocq)
* `binder_insert_fmap` (stdpp's `binder_insert_fmap`), `varmap_map_empty` (stdpp's
  `fmap_empty`), `interp_TRec_unfold`, `binop_int_res_interp`, `binop_bool_res_interp`,
  `unop_int_res_interp`, `unop_bool_res_interp`, and `valid_entails`/`valid_entails2`/
  `valid_entails3` (to combine the compatibility lemmas in `fundamental`).

## Omitted
* `Hint Resolve to_of_val` (not needed) and the commented-out Rocq code (the commented RHS
  steps, `eq_type_sound`, `unboxed_type_eq`).
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.UnaryRel

/-- Added: `binder_insert` commutes with `map` (Rocq: `binder_insert_fmap`). -/
theorem binder_insert_fmap {A B : Type} (f : A → B) (x : binder) (a : A) (m : varmap A) :
    (binder_insert x a m).map (fun _ v => f v) = binder_insert x (f a) (m.map fun _ v => f v) := by
  cases x with
  | BAnon => rfl
  | BNamed x =>
    apply Std.ExtTreeMap.ext_getElem?
    intro y
    simp only [binder_insert, Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert]
    split <;> rfl

/-- Added: `map` of the empty `varmap` (Rocq: `fmap_empty`). -/
theorem varmap_map_empty {A B : Type} (f : String → A → B) :
    (∅ : varmap A).map f = ∅ := by
  apply Std.ExtTreeMap.ext_getElem?
  intro y
  simp

section fundamental

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: the local tactic `rel_bind_ap e1 IH v Hv`. -/
local macro "rel_bind_ap " e:term:max ppSpace IH:ident ppSpace v:ident ppSpace Hv:introPat :
    tactic => `(tactic| focus
      rel_bind_l $e
      iapply refines_bind $$ $IH:ident
      iintro %$v:ident $Hv:introPat
      rel_finish)

/-- Rocq: `bin_log_related_var`. -/
theorem bin_log_related_var (Δ : List (lrel GF)) (Γ : varmap type) (x : String) (τ : type)
    (Hx : Γ[x]? = some τ) : ⊢ 〈Δ;Γ〉 ⊨ Var x : τ := by
  unfold bin_log_related
  iintro %vs #Hvs
  icases env_ltyped2_lookup _ vs x (interp τ Δ) (by simp [Std.ExtTreeMap.getElem?_map, Hx])
    $$ Hvs with ⟨%v1, %hv, HA⟩
  rw [show subst_map vs (Var x) = Val v1 by simp [subst_map, hv]]
  iapply refines_ret (Val v1) v1
  imodintro
  iexact HA

/-- Rocq: `bin_log_related_pair`. -/
theorem bin_log_related_pair (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 : τ1) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ2) -∗ 〈Δ;Γ〉 ⊨ Pair e1 e2 : TProd τ1 τ2 := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  rw [interp_TProd]
  iapply refines_pair $$ H1 H2

/-- Rocq: `bin_log_related_fst`. -/
theorem bin_log_related_fst (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e : TProd τ1 τ2) ⊢ 〈Δ;Γ〉 ⊨ Fst e : τ1 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  rw [interp_TProd]; unfold lrel_prod
  icases IH with ⟨%v1, %v2, %hv, IHw, -⟩
  subst hv
  rel_pure_l
  rel_values

/-- Rocq: `bin_log_related_snd`. -/
theorem bin_log_related_snd (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e : TProd τ1 τ2) ⊢ 〈Δ;Γ〉 ⊨ Snd e : τ2 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  rw [interp_TProd]; unfold lrel_prod
  icases IH with ⟨%v1, %v2, %hv, -, IHw⟩
  subst hv
  rel_pure_l
  rel_values

/-- Rocq: `bin_log_related_app`. -/
theorem bin_log_related_app (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 : TArrow τ1 τ2) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ1) -∗ 〈Δ;Γ〉 ⊨ App e1 e2 : τ2 := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  rw [interp_TArrow]
  iapply refines_app $$ H1 H2

/-- Rocq: `bin_log_related_rec`. -/
theorem bin_log_related_rec (Δ : List (lrel GF)) (Γ : varmap type) (f x : binder) (e : expr)
    (τ1 τ2 : type) :
    □ (〈Δ;binder_insert f (TArrow τ1 τ2) (binder_insert x τ1 Γ)〉 ⊨ e : τ2) ⊢
      〈Δ;Γ〉 ⊨ Rec f x e : TArrow τ1 τ2 := by
  unfold bin_log_related
  iintro #Ht %vs #Hvs
  simp only [subst_map]
  rel_pure_l
  rw [interp_TArrow]
  iapply refines_arrow_val
  imodintro
  iloeb as IH
  iintro %v1 #Hτ1
  have h : ▷^[1] (REL subst' x v1 (subst' f
        (RecV f x (subst_map (binder_delete x (binder_delete f vs)) e))
        (subst_map (binder_delete x (binder_delete f vs)) e)) : interp τ2 Δ) ⊢
      REL App (Val (RecV f x (subst_map (binder_delete x (binder_delete f vs)) e))) (Val v1) :
        interp τ2 Δ :=
    refines_pure 1 _ _ _ True [] trivial
  iapply h
  inext
  rw [← subst_map_binder_insert_2]
  iapply Ht
  rw [binder_insert_fmap, binder_insert_fmap]
  iapply env_ltyped2_insert $$ [IH]
  · rw [interp_TArrow]
    unfold lrel_arr
    imodintro
    iexact IH
  · iapply env_ltyped2_insert $$ Hτ1 Hvs

/-- Rocq: `bin_log_related_tlam`. -/
theorem bin_log_related_tlam (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ : type) :
    (∀ A : lrel GF, □ (〈A :: Δ;⤉Γ〉 ⊨ e : τ)) ⊢ 〈Δ;Γ〉 ⊨ TLam e : TForall τ := by
  unfold bin_log_related
  iintro #H %vs #Hvs
  simp only [subst_map, binder_delete]
  rel_pure_l
  rw [interp_TForall]
  iapply refines_forall
  imodintro
  iintro %A
  iapply H $$ %A %vs
  rw [interp_ren]
  iexact Hvs

/-- Rocq: `bin_log_related_tapp'`. -/
theorem bin_log_related_tapp' (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ τ' : type) :
    (〈Δ;Γ〉 ⊨ e : TForall τ) ⊢ 〈Δ;Γ〉 ⊨ TApp e : τ.[τ'/] := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  rw [interp_TForall]
  unfold lrel_forall lrel_arr
  ispecialize IH $$ %(interp τ' Δ)
  icases IH with #IH
  rw [← interp_subst]
  iapply IH
  unfold lrel_unit
  ipureintro
  rfl

/-- Rocq: `bin_log_related_tapp`. -/
theorem bin_log_related_tapp (τi : lrel GF) (Δ : List (lrel GF)) (Γ : varmap type) (e : expr)
    (τ : type) :
    (〈Δ;Γ〉 ⊨ e : TForall τ) ⊢ 〈τi :: Δ;⤉Γ〉 ⊨ TApp e : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  rw [interp_ren]
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  rw [interp_TForall]
  unfold lrel_forall lrel_arr
  ispecialize IH $$ %τi
  icases IH with #IH
  iapply IH
  unfold lrel_unit
  ipureintro
  rfl

/-- Rocq: `bin_log_related_seq`. -/
theorem bin_log_related_seq (R : lrel GF) (Δ : List (lrel GF)) (Γ : varmap type)
    (e1 e2 : expr) (τ1 τ2 : type) :
    (〈R :: Δ;⤉Γ〉 ⊨ e1 : τ1) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ2) -∗ 〈Δ;Γ〉 ⊨ Seq e1 e2 : τ2 := by
  unfold bin_log_related
  iintro He1 He2 %vs #Hvs
  simp only [subst_map, binder_delete]
  ihave H1 := He1 $$ %vs [Hvs]
  · rw [interp_ren]
    iexact Hvs
  ihave H2 := He2 $$ %vs Hvs
  iapply refines_seq (interp τ1 (R :: Δ)) $$ H1 H2

/-- Rocq: `bin_log_related_seq'`. -/
theorem bin_log_related_seq' (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 : τ1) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ2) -∗ 〈Δ;Γ〉 ⊨ Seq e1 e2 : τ2 := by
  iintro He1 He2
  iapply bin_log_related_seq lrel_true Δ Γ e1 e2 (type.subst (type.ren (· + 1)) τ1) τ2 $$
    [He1] He2
  unfold bin_log_related
  iintro %vs #Hvs
  rw [interp_ren]
  have h := interp_ren_up [] Δ τ1 lrel_true
  simp only [List.nil_append, List.length_nil, upn_zero] at h
  rw [← h]
  iapply He1 $$ Hvs

/-- Rocq: `bin_log_related_injl`. -/
theorem bin_log_related_injl (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e : τ1) ⊢ 〈Δ;Γ〉 ⊨ InjL e : TSum τ1 τ2 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TSum]
  iapply refines_injl
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_injr`. -/
theorem bin_log_related_injr (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e : τ2) ⊢ 〈Δ;Γ〉 ⊨ InjR e : TSum τ1 τ2 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TSum]
  iapply refines_injr
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_case`. -/
theorem bin_log_related_case (Δ : List (lrel GF)) (Γ : varmap type) (e0 e1 e2 : expr)
    (τ1 τ2 τ3 : type) :
    (〈Δ;Γ〉 ⊨ e0 : TSum τ1 τ2) ⊢ (〈Δ;Γ〉 ⊨ e1 : TArrow τ1 τ3) -∗
      (〈Δ;Γ〉 ⊨ e2 : TArrow τ2 τ3) -∗ 〈Δ;Γ〉 ⊨ Case e0 e1 e2 : τ3 := by
  unfold bin_log_related
  iintro IH1 IH2 IH3 %vs #Hvs
  simp only [subst_map]
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e0) IH1 v0 IH1
  rw [interp_TSum]
  unfold lrel_sum
  icases IH1 with ⟨%w, ⟨%hw, #Hw⟩ | ⟨%hw, #Hw⟩⟩
  · subst hw
    rel_pures_l
    rw [interp_TArrow Δ τ1 τ3]
    ihave IH2 := IH2 $$ %vs Hvs
    iapply refines_app $$ IH2
    rel_values
  · subst hw
    rel_pures_l
    rw [interp_TArrow Δ τ2 τ3]
    ihave IH3 := IH3 $$ %vs Hvs
    iapply refines_app $$ IH3
    rel_values

/-- Rocq: `bin_log_related_if`. -/
theorem bin_log_related_if (Δ : List (lrel GF)) (Γ : varmap type) (e0 e1 e2 : expr)
    (τ : type) :
    (〈Δ;Γ〉 ⊨ e0 : TBool) ⊢ (〈Δ;Γ〉 ⊨ e1 : τ) -∗ (〈Δ;Γ〉 ⊨ e2 : τ) -∗
      〈Δ;Γ〉 ⊨ If e0 e1 e2 : τ := by
  unfold bin_log_related
  iintro IH1 IH2 IH3 %vs #Hvs
  simp only [subst_map]
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e0) IH1 v0 IH1
  rw [interp_TBool]
  unfold lrel_bool
  icases IH1 with ⟨%b, %hb⟩
  subst hb
  cases b
  · rel_pures_l
    iapply IH3 $$ Hvs
  · rel_pures_l
    iapply IH2 $$ Hvs

/-- Rocq: `bin_log_related_load`. -/
theorem bin_log_related_load (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e : TRef τ) ⊢ 〈Δ;Γ〉 ⊨ Load e : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef]
  iapply refines_load
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_store`. -/
theorem bin_log_related_store (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr)
    (τ : type) :
    (〈Δ;Γ〉 ⊨ e1 : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ) -∗ 〈Δ;Γ〉 ⊨ Store e1 e2 : TUnit := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef, interp_TUnit]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  iapply refines_store $$ H1 H2

/-- Rocq: `bin_log_related_alloc`. -/
theorem bin_log_related_alloc (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e : τ) ⊢ 〈Δ;Γ〉 ⊨ Alloc e : TRef τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  rel_alloc_l l as Hl
  imod inv_alloc (logN.@ l) ⊤ iprop(∃ w1, l ↦ w1 ∗ interp τ Δ w1) $$ [Hl IH] with #HN
  · inext
    iexists v
    iframe Hl IH
  rel_values
  imodintro
  rw [interp_TRef]
  unfold lrel_ref
  iexists l
  isplitr
  · ipureintro; rfl
  · iexact HN

/-- Rocq: `bin_log_related_alloctape`. -/
theorem bin_log_related_alloctape (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) :
    (〈Δ;Γ〉 ⊨ e : TNat) ⊢ 〈Δ;Γ〉 ⊨ AllocTape e : TTape := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  rw [interp_TNat]
  unfold lrel_nat
  icases IH with ⟨%N, %H2⟩
  subst H2
  rel_alloctape_l α as Hα
  ihave Hα := tapeN_to_empty α _ $$ Hα
  imod inv_alloc (logN.@ α) ⊤ iprop(α ↪ (⟨N, []⟩ : tape)) $$ [Hα] with #HN
  · inext
    iexact Hα
  rel_values
  imodintro
  rw [interp_TTape]
  unfold lrel_tape
  iexists α, N
  isplitr
  · ipureintro; rfl
  · iexact HN

/-- Rocq: `bin_log_related_rand_tape`. -/
theorem bin_log_related_rand_tape (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr) :
    (〈Δ;Γ〉 ⊨ e1 : TNat) ⊢ (〈Δ;Γ〉 ⊨ e2 : TTape) -∗ 〈Δ;Γ〉 ⊨ Rand e1 e2 : TNat := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TNat, interp_TTape]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map vs e2) IH2 v2 #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v1 #IH1
  iapply refines_rand_tape $$ [] [IH2]
  · rel_values
  · rel_values

/-- Rocq: `bin_log_related_rand_unit`. -/
theorem bin_log_related_rand_unit (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr) :
    (〈Δ;Γ〉 ⊨ e1 : TNat) ⊢ (〈Δ;Γ〉 ⊨ e2 : TUnit) -∗ 〈Δ;Γ〉 ⊨ Rand e1 e2 : TNat := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TNat, interp_TUnit]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map vs e2) IH2 v2 #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v1 #IH1
  unfold lrel_unit
  icases IH2 with %H
  subst H
  iapply refines_rand_unit
  rel_values

/-- Rocq: `bin_log_related_subsume_int_nat`. -/
theorem bin_log_related_subsume_int_nat (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) :
    (〈Δ;Γ〉 ⊨ e : TNat) ⊢ 〈Δ;Γ〉 ⊨ e : TInt := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs Hvs
  have h : (REL subst_map vs e : interp TNat Δ) ⊢
      (∀ v, interp TNat Δ v -∗ REL Val v : interp TInt Δ) -∗ REL subst_map vs e : interp TInt Δ :=
    refines_bind [] _ _ _
  iapply h $$ IH
  iintro %v #IH
  rw [interp_TNat]
  unfold lrel_nat
  icases IH with ⟨%N, %H⟩
  subst H
  rel_values
  imodintro
  rw [interp_TInt]
  unfold lrel_int
  iexists (N : ℤ)
  ipureintro; rfl

/-- Added: the result of a well-typed integer binary operation is in the interpretation of its
result type. -/
theorem binop_int_res_interp (Δ : List (lrel GF)) (op : bin_op) (n n' : ℤ) (τ : type) (v' : val)
    (h1 : binop_int_res_type op = some τ)
    (h2 : bin_op_eval op (LitV (LitInt n)) (LitV (LitInt n')) = some v') :
    ⊢ interp τ Δ v' := by
  cases op <;> simp [binop_int_res_type] at h1 <;> subst h1 <;>
    simp [bin_op_eval, bin_op_eval_int] at h2
  all_goals
    first | subst h2 | (obtain ⟨-, h2⟩ := h2; subst h2)
    first
      | (rw [interp_TInt]; unfold lrel_int)
      | (rw [interp_TBool]; unfold lrel_bool)
    iexists _
    ipureintro
    rfl

/-- Added: the result of a well-typed Boolean binary operation is in the interpretation of its
result type. -/
theorem binop_bool_res_interp (Δ : List (lrel GF)) (op : bin_op) (b b' : Bool) (τ : type)
    (v' : val) (h1 : binop_bool_res_type op = some τ)
    (h2 : bin_op_eval op (LitV (LitBool b)) (LitV (LitBool b')) = some v') :
    ⊢ interp τ Δ v' := by
  cases op <;> simp [binop_bool_res_type] at h1 <;> subst h1 <;>
    simp [bin_op_eval, bin_op_eval_bool] at h2
  all_goals
    first | subst h2 | (obtain ⟨-, h2⟩ := h2; subst h2)
    rw [interp_TBool]; unfold lrel_bool
    iexists _
    ipureintro
    rfl

/-- Added: the result of a well-typed integer unary operation is in the interpretation of its
result type. -/
theorem unop_int_res_interp (Δ : List (lrel GF)) (op : un_op) (n : ℤ) (τ : type) (v' : val)
    (h1 : unop_int_res_type op = some τ) (h2 : un_op_eval op (LitV (LitInt n)) = some v') :
    ⊢ interp τ Δ v' := by
  cases op <;> simp [unop_int_res_type] at h1
  subst h1
  simp [un_op_eval] at h2
  subst h2
  rw [interp_TInt]; unfold lrel_int
  iexists _
  ipureintro
  rfl

/-- Added: the result of a well-typed Boolean unary operation is in the interpretation of its
result type. -/
theorem unop_bool_res_interp (Δ : List (lrel GF)) (op : un_op) (b : Bool) (τ : type) (v' : val)
    (h1 : unop_bool_res_type op = some τ) (h2 : un_op_eval op (LitV (LitBool b)) = some v') :
    ⊢ interp τ Δ v' := by
  cases op <;> simp [unop_bool_res_type] at h1
  subst h1
  simp [un_op_eval] at h2
  subst h2
  rw [interp_TBool]; unfold lrel_bool
  iexists _
  ipureintro
  rfl

/-- Rocq: `bin_log_related_unboxed_eq`. -/
theorem bin_log_related_unboxed_eq (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr)
    (τ : type) (Hτ : UnboxedType τ) :
    (〈Δ;Γ〉 ⊨ e1 : τ) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ) -∗ 〈Δ;Γ〉 ⊨ BinOp EqOp e1 e2 : TBool := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map vs e2) IH2 v2 #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v1 #IH1
  ihave %hv1 := unboxed_type_sound τ Δ v1 Hτ $$ IH1
  have hv' : bin_op_eval EqOp v1 v2 = some (LitV (LitBool (decide (v1 = v2)))) := by
    have hs : vals_compare_safe v1 v2 := Or.inl hv1
    simp [bin_op_eval, hs]
  have h : ▷^[1] (REL Val (LitV (LitBool (decide (v1 = v2)))) : interp TBool Δ) ⊢
      REL BinOp EqOp (Val v1) (Val v2) : interp TBool Δ :=
    refines_pure 1 _ _ _ _ [] (Hpure := pure_binop EqOp v1 v2 _) hv'
  iapply h
  inext
  rel_values
  imodintro
  rw [interp_TBool]
  unfold lrel_bool
  iexists _
  ipureintro
  rfl

/-- Rocq: `bin_log_related_int_binop`. -/
theorem bin_log_related_int_binop (Δ : List (lrel GF)) (Γ : varmap type) (op : bin_op)
    (e1 e2 : expr) (τ : type) (Hopτ : binop_int_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e1 : TInt) ⊢ (〈Δ;Γ〉 ⊨ e2 : TInt) -∗ 〈Δ;Γ〉 ⊨ BinOp op e1 e2 : τ := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TInt]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map vs e2) IH2 v2 IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v1 IH1
  unfold lrel_int
  icases IH1 with ⟨%n, %hn⟩
  icases IH2 with ⟨%n', %hn'⟩
  subst hn hn'
  obtain ⟨v', Hopv'⟩ := binop_int_typed_safe op n n' τ Hopτ
  have h : ▷^[1] (REL Val v' : interp τ Δ) ⊢
      REL BinOp op (Val (LitV (LitInt n))) (Val (LitV (LitInt n'))) : interp τ Δ :=
    refines_pure 1 _ _ _ _ [] (Hpure := pure_binop op _ _ v') Hopv'
  iapply h
  inext
  rel_values
  imodintro
  iapply binop_int_res_interp Δ op n n' τ v' Hopτ Hopv'

/-- Rocq: `bin_log_related_bool_binop`. -/
theorem bin_log_related_bool_binop (Δ : List (lrel GF)) (Γ : varmap type) (op : bin_op)
    (e1 e2 : expr) (τ : type) (Hopτ : binop_bool_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e1 : TBool) ⊢ (〈Δ;Γ〉 ⊨ e2 : TBool) -∗ 〈Δ;Γ〉 ⊨ BinOp op e1 e2 : τ := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TBool]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map vs e2) IH2 v2 IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v1 IH1
  unfold lrel_bool
  icases IH1 with ⟨%n, %hn⟩
  icases IH2 with ⟨%n', %hn'⟩
  subst hn hn'
  obtain ⟨v', Hopv'⟩ := binop_bool_typed_safe op n n' τ Hopτ
  have h : ▷^[1] (REL Val v' : interp τ Δ) ⊢
      REL BinOp op (Val (LitV (LitBool n))) (Val (LitV (LitBool n'))) : interp τ Δ :=
    refines_pure 1 _ _ _ _ [] (Hpure := pure_binop op _ _ v') Hopv'
  iapply h
  inext
  rel_values
  imodintro
  iapply binop_bool_res_interp Δ op n n' τ v' Hopτ Hopv'

/-- Rocq: `bin_log_related_int_unop`. -/
theorem bin_log_related_int_unop (Δ : List (lrel GF)) (Γ : varmap type) (op : un_op)
    (e : expr) (τ : type) (Hopτ : unop_int_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e : TInt) ⊢ 〈Δ;Γ〉 ⊨ UnOp op e : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TInt]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  unfold lrel_int
  icases IH with ⟨%n, %hn⟩
  subst hn
  obtain ⟨v', Hopv'⟩ := unop_int_typed_safe op n τ Hopτ
  have h : ▷^[1] (REL Val v' : interp τ Δ) ⊢
      REL UnOp op (Val (LitV (LitInt n))) : interp τ Δ :=
    refines_pure 1 _ _ _ _ [] (Hpure := pure_unop op _ v') Hopv'
  iapply h
  inext
  rel_values
  imodintro
  iapply unop_int_res_interp Δ op n τ v' Hopτ Hopv'

/-- Rocq: `bin_log_related_bool_unop`. -/
theorem bin_log_related_bool_unop (Δ : List (lrel GF)) (Γ : varmap type) (op : un_op)
    (e : expr) (τ : type) (Hopτ : unop_bool_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e : TBool) ⊢ 〈Δ;Γ〉 ⊨ UnOp op e : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TBool]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  unfold lrel_bool
  icases IH with ⟨%n, %hn⟩
  subst hn
  obtain ⟨v', Hopv'⟩ := unop_bool_typed_safe op n τ Hopτ
  have h : ▷^[1] (REL Val v' : interp τ Δ) ⊢
      REL UnOp op (Val (LitV (LitBool n))) : interp τ Δ :=
    refines_pure 1 _ _ _ _ [] (Hpure := pure_unop op _ v') Hopv'
  iapply h
  inext
  rel_values
  imodintro
  iapply unop_bool_res_interp Δ op n τ v' Hopτ Hopv'

/-- Added: unfolding the interpretation of a recursive type. -/
theorem interp_TRec_unfold (Δ : List (lrel GF)) (τ : type) (v : val) :
    interp (TRec τ) Δ v ⊣⊢ ▷ interp τ (interp (TRec τ) Δ :: Δ) v := by
  rw [interp_TRec]
  nth_rw 1 [lrel_rec_unfold]
  exact .rfl

/-- Rocq: `bin_log_related_unfold`. -/
theorem bin_log_related_unfold (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e : TRec τ) ⊢ 〈Δ;Γ〉 ⊨ App (Val rec_unfold) e : τ.[TRec τ/] := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map vs e) IH v IH
  ihave IH := (interp_TRec_unfold Δ τ v).1 $$ IH
  rel_rec_l
  rel_values
  imodintro
  rw [← interp_subst]
  iexact IH

/-- Rocq: `bin_log_related_fold`. -/
theorem bin_log_related_fold (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e : τ.[TRec τ/]) ⊢ 〈Δ;Γ〉 ⊨ e : TRec τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs Hvs
  have h : (REL subst_map vs e : interp (τ.[TRec τ/]) Δ) ⊢
      (∀ v, interp (τ.[TRec τ/]) Δ v -∗ REL Val v : interp (TRec τ) Δ) -∗
        REL subst_map vs e : interp (TRec τ) Δ :=
    refines_bind [] _ _ _
  iapply h $$ IH
  iintro %v IH
  rel_values
  imodintro
  iapply (interp_TRec_unfold Δ τ v).2
  inext
  rw [interp_subst]
  iexact IH

/-- Rocq: `bin_log_related_pack'`. -/
theorem bin_log_related_pack' (Δ : List (lrel GF)) (Γ : varmap type) (e : expr)
    (τ τ' : type) :
    (〈Δ;Γ〉 ⊨ e : τ.[τ'/]) ⊢ 〈Δ;Γ〉 ⊨ e : TExists τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs Hvs
  have h : (REL subst_map vs e : interp (τ.[τ'/]) Δ) ⊢
      (∀ v, interp (τ.[τ'/]) Δ v -∗ REL Val v : interp (TExists τ) Δ) -∗
        REL subst_map vs e : interp (TExists τ) Δ :=
    refines_bind [] _ _ _
  iapply h $$ IH
  iintro %v #IH
  rel_values
  imodintro
  rw [interp_TExists]
  unfold lrel_exists
  iexists interp τ' Δ
  rw [← interp_subst]
  iexact IH

/-- Rocq: `bin_log_related_pack`. -/
theorem bin_log_related_pack (τi : lrel GF) (Δ : List (lrel GF)) (Γ : varmap type) (e : expr)
    (τ : type) :
    (〈τi :: Δ;⤉Γ〉 ⊨ e : τ) ⊢ 〈Δ;Γ〉 ⊨ e : TExists τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs [Hvs]
  · rw [interp_ren]
    iexact Hvs
  have h : (REL subst_map vs e : interp τ (τi :: Δ)) ⊢
      (∀ v, interp τ (τi :: Δ) v -∗ REL Val v : interp (TExists τ) Δ) -∗
        REL subst_map vs e : interp (TExists τ) Δ :=
    refines_bind [] _ _ _
  iapply h $$ IH
  iintro %v #IH
  rel_values
  imodintro
  rw [interp_TExists]
  unfold lrel_exists
  iexists τi
  iexact IH

/-- Rocq: `bin_log_related_unpack`. -/
theorem bin_log_related_unpack (Δ : List (lrel GF)) (Γ : varmap type) (x : binder)
    (e1 e2 : expr) (τ τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 : TExists τ) ⊢
      (∀ τi : lrel GF,
        〈τi :: Δ;binder_insert x τ (⤉Γ)〉 ⊨ e2 : type.subst (type.ren (· + 1)) τ2) -∗
      〈Δ;Γ〉 ⊨ App (App (Val unpack) e1) (Lam x e2) : τ2 := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rel_pure_l
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v #IH1
  rw [interp_TExists]
  unfold lrel_exists
  icases IH1 with ⟨%A, #IH⟩
  rel_rec_l
  rel_pure_l
  rel_pure_l
  have h : ▷^[1] (REL subst' x v (subst_map (binder_delete x vs) e2) : interp τ2 Δ) ⊢
      REL App (Val (RecV BAnon x (subst_map (binder_delete x vs) e2))) (Val v) : interp τ2 Δ :=
    refines_pure 1 _ _ _ True [] trivial
  rw [show binder_delete BAnon vs = vs from rfl]
  iapply h
  inext
  rw [← subst_map_binder_insert]
  have hren := interp_ren_up [] Δ τ2 A
  simp only [List.nil_append, List.length_nil, upn_zero] at hren
  rw [hren]
  iapply IH2 $$ %A %(binder_insert x v vs)
  rw [binder_insert_fmap, interp_ren]
  iapply env_ltyped2_insert $$ IH Hvs

/-- Rocq: `bin_log_related_fork`. -/
theorem bin_log_related_fork (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) :
    (〈Δ;Γ〉 ⊨ e : TUnit) ⊢ 〈Δ;Γ〉 ⊨ Fork e : TUnit := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TUnit]
  iapply refines_fork
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_CmpXchg_EqType`. -/
theorem bin_log_related_CmpXchg_EqType (Δ : List (lrel GF)) (Γ : varmap type)
    (e1 e2 e3 : expr) (τ : type) (_Hτ : EqType τ) (Hτ' : UnboxedType τ) :
    (〈Δ;Γ〉 ⊨ e1 : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ) -∗ (〈Δ;Γ〉 ⊨ e3 : τ) -∗
      〈Δ;Γ〉 ⊨ CmpXchg e1 e2 e3 : TProd τ TBool := by
  unfold bin_log_related
  iintro IH1 IH2 IH3 %vs #Hvs
  simp only [subst_map]
  ihave IH3 := IH3 $$ %vs Hvs
  rel_bind_ap (subst_map vs e3) IH3 v3 #IH3
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map vs e2) IH2 v2 #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v1 #IH1
  rw [interp_TRef]
  unfold lrel_ref
  icases IH1 with ⟨%l, %hl, #Hinv⟩
  subst hl
  ihave %hv2 := unboxed_type_sound τ Δ v2 Hτ' $$ IH2
  have h : _ ⊢ REL CmpXchg (Val (LitV (LitLoc l))) (Val v2) (Val v3) : interp (TProd τ TBool) Δ :=
    refines_atomic_l (⊤ \ ↑(logN.@ l)) []
      (CmpXchg (Val (LitV (LitLoc l))) (Val v2) (Val v3)) (interp (TProd τ TBool) Δ)
  iapply h
  iinv Hinv with ⟨%v1, >Hv1, #Hv⟩ Hclose
  imodintro
  by_cases hv : v1 = v2
  · subst hv
    wp_cmpxchg_suc
    · exact Or.inr hv2
    imod Hclose $$ [Hv1]
    · inext
      iexists v3
      iframe Hv1 IH3
    imodintro
    rel_finish
    rel_values
    rw [interp_TProd, interp_TBool]
    unfold lrel_prod lrel_bool
    iexists v1, (LitV (LitBool true))
    isplitr
    · ipureintro; rfl
    isplitl
    · iexact Hv
    · iexists true
      ipureintro; rfl
  · wp_cmpxchg_fail
    · exact Or.inr hv2
    imod Hclose $$ [Hv1]
    · inext
      iexists v1
      iframe Hv1 Hv
    imodintro
    rel_finish
    rel_values
    rw [interp_TProd, interp_TBool]
    unfold lrel_prod lrel_bool
    iexists v1, (LitV (LitBool false))
    isplitr
    · ipureintro; rfl
    isplitl
    · iexact Hv
    · iexists false
      ipureintro; rfl

/-- Rocq: `bin_log_related_CmpXchg`. -/
theorem bin_log_related_CmpXchg (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 e3 : expr)
    (τ : type) (Hτ : UnboxedType τ) :
    (〈Δ;Γ〉 ⊨ e1 : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ) -∗ (〈Δ;Γ〉 ⊨ e3 : τ) -∗
      〈Δ;Γ〉 ⊨ CmpXchg e1 e2 e3 : TProd τ TBool := by
  rcases unboxed_type_ref_or_eqtype τ Hτ with Hτ'' | ⟨τ', rfl⟩
  · exact bin_log_related_CmpXchg_EqType Δ Γ e1 e2 e3 τ Hτ'' Hτ
  · unfold bin_log_related
    iintro H1 H2 H3 %vs #Hvs
    ihave H1 := H1 $$ %vs Hvs
    ihave H2 := H2 $$ %vs Hvs
    ihave H3 := H3 $$ %vs Hvs
    simp only [subst_map]
    rw [interp_TProd, interp_TRef, interp_TRef, interp_TBool]
    iapply refines_cmpxchg_ref $$ H1 H2 H3

/-- Rocq: `bin_log_related_xchg`. -/
theorem bin_log_related_xchg (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr)
    (τ : type) :
    (〈Δ;Γ〉 ⊨ e1 : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 : τ) -∗ 〈Δ;Γ〉 ⊨ Xchg e1 e2 : τ := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  iapply refines_xchg $$ H1 H2

/-- Rocq: `bin_log_related_FAA`. -/
theorem bin_log_related_FAA (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 : expr) :
    (〈Δ;Γ〉 ⊨ e1 : TRef TNat) ⊢ (〈Δ;Γ〉 ⊨ e2 : TNat) -∗ 〈Δ;Γ〉 ⊨ FAA e1 e2 : TNat := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef, interp_TNat]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map vs e2) IH2 v2 #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map vs e1) IH1 v1 #IH1
  unfold lrel_ref lrel_nat
  icases IH1 with ⟨%l, %hl, #Hinv⟩
  subst hl
  icases IH2 with ⟨%n, %hn⟩
  subst hn
  have h : _ ⊢ REL FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt (n : ℤ)))) : lrel_nat :=
    refines_atomic_l (⊤ \ ↑(logN.@ l)) []
      (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt (n : ℤ))))) lrel_nat
  unfold lrel_nat at h
  iapply h
  iinv Hinv with ⟨%v1, >Hv1, >⟨%n1, %hn1⟩⟩ Hclose
  subst hn1
  imodintro
  wp_faa
  imod Hclose $$ [Hv1]
  · inext
    iexists _
    iframe Hv1
    iexists (n1 + n)
    ipureintro
    simp
  imodintro
  rel_finish
  rel_values

omit [foxtrotGS GF] in
/-- Added: `P ⊢ Q` and `⊢ P` give `⊢ Q`. -/
theorem valid_entails {P Q : IProp GF} (h : P ⊢ Q) (hp : ⊢ P) : ⊢ Q := hp.trans h

omit [foxtrotGS GF] in
/-- Added: `P ⊢ Q -∗ R`, `⊢ P` and `⊢ Q` give `⊢ R`. -/
theorem valid_entails2 {P Q R : IProp GF} (h : P ⊢ Q -∗ R) (hp : ⊢ P) (hq : ⊢ Q) : ⊢ R := by
  iapply h
  · iapply hp
  · iapply hq

omit [foxtrotGS GF] in
/-- Added: `P ⊢ Q -∗ R -∗ S`, `⊢ P`, `⊢ Q` and `⊢ R` give `⊢ S`. -/
theorem valid_entails3 {P Q R S : IProp GF} (h : P ⊢ Q -∗ R -∗ S) (hp : ⊢ P) (hq : ⊢ Q)
    (hr : ⊢ R) : ⊢ S := by
  iapply h
  · iapply hp
  · iapply hq
  · iapply hr

mutual

/-- Rocq: `fundamental`. -/
theorem fundamental (Δ : List (lrel GF)) (Γ : varmap type) (e : expr) (τ : type) :
    Γ ⊢ₜ e : τ → ⊢ 〈Δ;Γ〉 ⊨ e : τ
  | .Var_typed _ x τ h => bin_log_related_var Δ Γ x τ h
  | .Val_typed _ v τ h => by
    have Hv := fundamental_val Δ v τ h
    unfold bin_log_related
    iintro %vs #_
    simp only [subst_map]
    rel_values
    imodintro
    iapply Hv
  | .BinOp_typed_int _ op e1 e2 τ h1 h2 hop =>
    valid_entails2 (bin_log_related_int_binop Δ Γ op e1 e2 τ hop)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .BinOp_typed_bool _ op e1 e2 τ h1 h2 hop =>
    valid_entails2 (bin_log_related_bool_binop Δ Γ op e1 e2 τ hop)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .UnOp_typed_int _ op e τ h1 hop =>
    valid_entails (bin_log_related_int_unop Δ Γ op e τ hop) (fundamental Δ _ _ _ h1)
  | .UnOp_typed_bool _ op e τ h1 hop =>
    valid_entails (bin_log_related_bool_unop Δ Γ op e τ hop) (fundamental Δ _ _ _ h1)
  | .UnboxedEq_typed _ e1 e2 τ hτ h1 h2 =>
    valid_entails2 (bin_log_related_unboxed_eq Δ Γ e1 e2 τ hτ)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .Pair_typed _ e1 e2 τ1 τ2 h1 h2 =>
    valid_entails2 (bin_log_related_pair Δ Γ e1 e2 τ1 τ2)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .Fst_typed _ e τ1 τ2 h1 =>
    valid_entails (bin_log_related_fst Δ Γ e τ1 τ2) (fundamental Δ _ _ _ h1)
  | .Snd_typed _ e τ1 τ2 h1 =>
    valid_entails (bin_log_related_snd Δ Γ e τ1 τ2) (fundamental Δ _ _ _ h1)
  | .InjL_typed _ e τ1 τ2 h1 =>
    valid_entails (bin_log_related_injl Δ Γ e τ1 τ2) (fundamental Δ _ _ _ h1)
  | .InjR_typed _ e τ1 τ2 h1 =>
    valid_entails (bin_log_related_injr Δ Γ e τ1 τ2) (fundamental Δ _ _ _ h1)
  | .Case_typed _ e0 e1 e2 τ1 τ2 τ3 h0 h1 h2 =>
    valid_entails3 (bin_log_related_case Δ Γ e0 e1 e2 τ1 τ2 τ3)
      (fundamental Δ _ _ _ h0) (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .If_typed _ e0 e1 e2 τ h0 h1 h2 =>
    valid_entails3 (bin_log_related_if Δ Γ e0 e1 e2 τ)
      (fundamental Δ _ _ _ h0) (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .Rec_typed _ f x e τ1 τ2 h1 => by
    have H := fundamental Δ _ _ _ h1
    iapply bin_log_related_rec
    imodintro
    iapply H
  | .App_typed _ e1 e2 τ1 τ2 h1 h2 =>
    valid_entails2 (bin_log_related_app Δ Γ e1 e2 τ1 τ2)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .TLam_typed _ e τ h1 => by
    have H := fun A => fundamental (A :: Δ) _ _ _ h1
    iapply bin_log_related_tlam
    iintro %A !>
    iapply H A
  | .TApp_typed _ e τ τ' h1 =>
    valid_entails (bin_log_related_tapp' Δ Γ e τ τ') (fundamental Δ _ _ _ h1)
  | .TFold _ e τ h1 =>
    valid_entails (bin_log_related_fold Δ Γ e τ) (fundamental Δ _ _ _ h1)
  | .TUnfold _ e τ h1 =>
    valid_entails (bin_log_related_unfold Δ Γ e τ) (fundamental Δ _ _ _ h1)
  | .TPack _ e τ τ' h1 =>
    valid_entails (bin_log_related_pack' Δ Γ e τ τ') (fundamental Δ _ _ _ h1)
  | .TUnpack _ e1 x e2 τ τ2 h1 h2 => by
    have H1 := fundamental Δ _ _ _ h1
    have H2 := fun A => fundamental (A :: Δ) _ _ _ h2
    iapply bin_log_related_unpack
    · iapply H1
    · iintro %A
      iapply H2 A
  | .TAlloc _ e τ h1 =>
    valid_entails (bin_log_related_alloc Δ Γ e τ) (fundamental Δ _ _ _ h1)
  | .TLoad _ e τ h1 =>
    valid_entails (bin_log_related_load Δ Γ e τ) (fundamental Δ _ _ _ h1)
  | .TStore _ e1 e2 τ h1 h2 =>
    valid_entails2 (bin_log_related_store Δ Γ e1 e2 τ)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .TAllocTape e _ h1 =>
    valid_entails (bin_log_related_alloctape Δ Γ e) (fundamental Δ _ _ _ h1)
  | .TRand _ e1 e2 h1 h2 =>
    valid_entails2 (bin_log_related_rand_tape Δ Γ e1 e2)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .TRandU _ e1 e2 h1 h2 =>
    valid_entails2 (bin_log_related_rand_unit Δ Γ e1 e2)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .Subsume_int_nat _ e h1 =>
    valid_entails (bin_log_related_subsume_int_nat Δ Γ e) (fundamental Δ _ _ _ h1)
  | .Fork_typed _ e h1 =>
    valid_entails (bin_log_related_fork Δ Γ e) (fundamental Δ _ _ _ h1)
  | .CmpXchg_typed _ e1 e2 e3 τ hτ h1 h2 h3 =>
    valid_entails3 (bin_log_related_CmpXchg Δ Γ e1 e2 e3 τ hτ)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2) (fundamental Δ _ _ _ h3)
  | .Xchg_typed _ e1 e2 τ h1 h2 =>
    valid_entails2 (bin_log_related_xchg Δ Γ e1 e2 τ)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)
  | .Faa_typed _ e1 e2 h1 h2 =>
    valid_entails2 (bin_log_related_FAA Δ Γ e1 e2)
      (fundamental Δ _ _ _ h1) (fundamental Δ _ _ _ h2)

/-- Rocq: `fundamental_val`. -/
theorem fundamental_val (Δ : List (lrel GF)) (v : val) (τ : type) :
    val_typed v τ → ⊢ interp τ Δ v
  | .Unit_val_typed => by
    rw [interp_TUnit]
    unfold lrel_unit
    ipureintro
    rfl
  | .Int_val_typed n => by
    rw [interp_TInt]
    unfold lrel_int
    iexists n
    ipureintro
    rfl
  | .Nat_val_typed n => by
    rw [interp_TNat]
    unfold lrel_nat
    iexists n
    ipureintro
    rfl
  | .Bool_val_typed b => by
    rw [interp_TBool]
    unfold lrel_bool
    iexists b
    ipureintro
    rfl
  | .Pair_val_typed v1 v2 τ1 τ2 h1 h2 => by
    have H1 := fundamental_val Δ _ _ h1
    have H2 := fundamental_val Δ _ _ h2
    rw [interp_TProd]
    unfold lrel_prod
    iexists v1, v2
    isplitr
    · ipureintro; rfl
    isplitl
    · iapply H1
    · iapply H2
  | .InjL_val_typed v τ1 τ2 h1 => by
    have H1 := fundamental_val Δ _ _ h1
    rw [interp_TSum]
    unfold lrel_sum
    iexists v
    ileft
    isplitr
    · ipureintro; rfl
    · iapply H1
  | .InjR_val_typed v τ1 τ2 h1 => by
    have H1 := fundamental_val Δ _ _ h1
    rw [interp_TSum]
    unfold lrel_sum
    iexists v
    iright
    isplitr
    · ipureintro; rfl
    · iapply H1
  | .Rec_val_typed f x e τ1 τ2 h1 => by
    have H := fundamental Δ _ _ _ h1
    unfold bin_log_related at H
    iloeb as IH
    rw [interp_TArrow]
    unfold lrel_arr
    imodintro
    iintro %v1 #Hv
    have hb : ▷^[1] (REL subst' x v1 (subst' f (RecV f x e) e) : interp τ2 Δ) ⊢
        REL App (Val (RecV f x e)) (Val v1) : interp τ2 Δ :=
      refines_pure 1 _ _ _ True [] trivial
    iapply hb
    inext
    rw [← subst_map_binder_insert_2_empty]
    iapply H $$ %(binder_insert f (RecV f x e) (binder_insert x v1 ∅))
    rw [binder_insert_fmap, binder_insert_fmap, varmap_map_empty]
    iapply env_ltyped2_insert $$ [IH]
    · rw [interp_TArrow]
      unfold lrel_arr
      iexact IH
    · iapply env_ltyped2_insert $$ Hv
      iapply env_ltyped2_empty
  | .TLam_val_typed e τ h1 => by
    have H := fun A => fundamental (A :: Δ) _ _ _ h1
    rw [interp_TForall]
    unfold lrel_forall lrel_arr lrel_unit
    iintro %A !> %v1 %_
    have hb : ▷^[1] (REL e : interp τ (A :: Δ)) ⊢
        REL App (Val (RecV BAnon BAnon e)) (Val v1) : interp τ (A :: Δ) :=
      refines_pure 1 _ _ _ True [] trivial
    iapply hb
    inext
    have H' := H A
    unfold bin_log_related at H'
    have H'' : ⊢ REL subst_map ∅ e : interp τ (A :: Δ) := by
      iapply H' $$ %∅
      rw [varmap_map_empty]
      iapply env_ltyped2_empty
    rw [subst_map_empty] at H''
    iapply H''

end

/-- Rocq: `refines_typed`. -/
theorem refines_typed (τ : type) (Δ : List (lrel GF)) (e : expr) (h : ∅ ⊢ₜ e : τ) :
    ⊢ REL e : interp τ Δ := by
  have Hty := fundamental Δ _ _ _ h
  unfold bin_log_related at Hty
  have H : ⊢ REL subst_map ∅ e : interp τ Δ := by
    iapply Hty $$ %∅
    rw [varmap_map_empty]
    iapply env_ltyped2_empty
  rw [subst_map_empty] at H
  exact H

/-- Rocq: `typed_safe`. -/
theorem typed_safe (τ : type) (Δ : List (lrel GF)) (e : expr) (h : ∅ ⊢ₜ e : τ) :
    ⊢ WP e {{ v, interp τ Δ v }} :=
  refines_typed τ Δ e h

end fundamental

end Foxtrot.UnaryRel
