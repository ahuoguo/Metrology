module

public import Metrology.Foxtrot.BinaryRel.BinaryFundamental

/-!
# The fundamental theorem of Foxtrot's binary logical relation (part 2)

Ported from clutch/theories/foxtrot/binary_rel/binary_fundamental.v (lines 234-418: the
compatibility lemmas `bin_log_related_load` .. `bin_log_related_bool_unop`).

## Rocq → Lean map
All Rocq names are kept (namespace `Foxtrot.BinaryRel`).

## Deviations
* `ref e` is `Alloc e` (`= AllocN (Val (LitV (LitInt 1))) e`), `alloc e` is `AllocTape e`,
  `rand(e2) e1` is `Rand e1 e2`, `()` is `TUnit`.
* The pure steps of the operator cases (Rocq: `rel_pures_l; eauto`) use `refines_pure_l`/
  `refines_pure_r` with the non-instance `pure_binop`/`pure_unop` (whose result value is an
  output) and the evaluation fact given by `*_typed_safe`.
* The final case analyses on the operators (Rocq: `destruct op; inversion Hopv'; ...`) are the
  added helpers `binop_int_res_interp`, `binop_bool_res_interp`, `unop_int_res_interp`,
  `unop_bool_res_interp`.

## Added helpers
* `binop_int_res_interp`, `binop_bool_res_interp`, `unop_int_res_interp`,
  `unop_bool_res_interp`.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

section fundamental

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: the local tactic `rel_bind_ap e1 e2 IH v w Hv`. -/
local macro "rel_bind_ap " e1:term:max ppSpace e2:term:max ppSpace IH:ident ppSpace v:ident
    ppSpace w:ident ppSpace Hv:introPat : tactic => `(tactic| focus
      rel_bind_l $e1
      rel_bind_r $e2
      iapply refines_bind $$ $IH:ident
      iintro %$v:ident %$w:ident $Hv:introPat
      rel_finish)

/-- Rocq: `bin_log_related_load`. -/
theorem bin_log_related_load (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TRef τ) ⊢ 〈Δ;Γ〉 ⊨ Load e ≤log≤ Load e' : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef]
  iapply refines_load
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_store`. -/
theorem bin_log_related_store (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 e1' e2' : expr)
    (τ : type) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
      〈Δ;Γ〉 ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef, interp_TUnit]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  iapply refines_store $$ H1 H2

/-- Rocq: `bin_log_related_alloc`. -/
theorem bin_log_related_alloc (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ) ⊢ 〈Δ;Γ〉 ⊨ Alloc e ≤log≤ Alloc e' : TRef τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v v' IH
  rel_alloc_l l as Hl
  rel_alloc_r k as Hk
  imod inv_alloc (logN.@ (l, k)) ⊤
    iprop(∃ w1 w2, l ↦ w1 ∗ k ↦ₛ w2 ∗ interp τ Δ w1 w2) $$ [Hl Hk IH] with #HN
  · inext
    iexists v, v'
    iframe Hl Hk IH
  rel_values
  imodintro
  rw [interp_TRef]
  dsimp only [lrel_ref]
  iexists l, k
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  iexact HN

/-- Rocq: `bin_log_related_alloctape`. -/
theorem bin_log_related_alloctape (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TNat) ⊢ 〈Δ;Γ〉 ⊨ AllocTape e ≤log≤ AllocTape e' : TTape := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v v' IH
  rw [interp_TNat]
  dsimp only [lrel_nat]
  icases IH with ⟨%N, %H2⟩
  obtain ⟨rfl, rfl⟩ := H2
  rel_alloctape_l α as Hα
  rel_alloctape_r β as Hβ
  ihave Hα := tapeN_to_empty α N $$ Hα
  ihave Hβ := spec_tapeN_to_empty β N $$ Hβ
  imod inv_alloc (logN.@ (α, β)) ⊤
    iprop((α ↪ (⟨N, []⟩ : tape)) ∗ β ↪ₛ (⟨N, []⟩ : tape)) $$ [Hα Hβ] with #HN
  · inext
    iframe Hα Hβ
  rel_values
  imodintro
  rw [interp_TTape]
  dsimp only [lrel_tape]
  iexists α, β, N
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  iexact HN

/-- Rocq: `bin_log_related_rand_tape`. -/
theorem bin_log_related_rand_tape (Δ : List (lrel GF)) (Γ : varmap type) (e1 e1' e2 e2' : expr) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TNat) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TTape) -∗
      〈Δ;Γ〉 ⊨ Rand e1 e2 ≤log≤ Rand e1' e2' : TNat := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TNat, interp_TTape]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map _ e2) (subst_map _ e2') IH2 v2 v2' #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v1 v1' #IH1
  iapply refines_rand_tape $$ [] [IH2]
  · rel_values
  · rel_values

/-- Rocq: `bin_log_related_rand_unit`. -/
theorem bin_log_related_rand_unit (Δ : List (lrel GF)) (Γ : varmap type) (e1 e1' e2 e2' : expr) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TNat) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TUnit) -∗
      〈Δ;Γ〉 ⊨ Rand e1 e2 ≤log≤ Rand e1' e2' : TNat := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TNat, interp_TUnit]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map _ e2) (subst_map _ e2') IH2 v2 v2' #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v1 v1' #IH1
  dsimp only [lrel_unit]
  icases IH2 with %H
  obtain ⟨rfl, rfl⟩ := H
  iapply refines_rand_unit
  rel_values

/-- Rocq: `bin_log_related_subsume_int_nat`. -/
theorem bin_log_related_subsume_int_nat (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TNat) ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e' : TInt := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs Hvs
  have h : (REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
        interp TNat Δ) ⊢
      (∀ v v', interp TNat Δ v v' -∗ REL Val v << Val v' : interp TInt Δ) -∗
        REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
          interp TInt Δ :=
    refines_bind [] [] _ _ _ _
  iapply h $$ IH
  iintro %v %v' #IH
  rw [interp_TNat]
  dsimp only [lrel_nat]
  icases IH with ⟨%N, %H⟩
  obtain ⟨rfl, rfl⟩ := H
  rel_values
  imodintro
  rw [interp_TInt]
  dsimp only [lrel_int]
  iexists (N : ℤ)
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Added (Rocq: the final `destruct op; ...` of `bin_log_related_int_binop`): the result of a
well-typed integer binary operation is in the interpretation of its result type. -/
theorem binop_int_res_interp (Δ : List (lrel GF)) (op : bin_op) (n n' : ℤ) (τ : type)
    (v' : val) (h1 : binop_int_res_type op = some τ)
    (h2 : bin_op_eval op (LitV (LitInt n)) (LitV (LitInt n')) = some v') :
    ⊢ interp τ Δ v' v' := by
  cases op <;> simp [binop_int_res_type] at h1 <;> subst h1 <;>
    simp [bin_op_eval, bin_op_eval_int] at h2
  all_goals
    first | subst h2 | (obtain ⟨-, h2⟩ := h2; subst h2)
    first
      | (rw [interp_TInt]; dsimp only [lrel_int])
      | (rw [interp_TBool]; dsimp only [lrel_bool])
    iexists _
    ipureintro
    exact ⟨rfl, rfl⟩

/-- Added (Rocq: the final `destruct op; ...` of `bin_log_related_bool_binop`). -/
theorem binop_bool_res_interp (Δ : List (lrel GF)) (op : bin_op) (b b' : Bool) (τ : type)
    (v' : val) (h1 : binop_bool_res_type op = some τ)
    (h2 : bin_op_eval op (LitV (LitBool b)) (LitV (LitBool b')) = some v') :
    ⊢ interp τ Δ v' v' := by
  cases op <;> simp [binop_bool_res_type] at h1 <;> subst h1 <;>
    simp [bin_op_eval, bin_op_eval_bool] at h2
  all_goals
    first | subst h2 | (obtain ⟨-, h2⟩ := h2; subst h2)
    rw [interp_TBool]; dsimp only [lrel_bool]
    iexists _
    ipureintro
    exact ⟨rfl, rfl⟩

/-- Added (Rocq: the final `destruct op; ...` of `bin_log_related_int_unop`). -/
theorem unop_int_res_interp (Δ : List (lrel GF)) (op : un_op) (n : ℤ) (τ : type) (v' : val)
    (h1 : unop_int_res_type op = some τ) (h2 : un_op_eval op (LitV (LitInt n)) = some v') :
    ⊢ interp τ Δ v' v' := by
  cases op <;> simp [unop_int_res_type] at h1
  subst h1
  simp [un_op_eval] at h2
  subst h2
  rw [interp_TInt]; dsimp only [lrel_int]
  iexists _
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Added (Rocq: the final `destruct op; ...` of `bin_log_related_bool_unop`). -/
theorem unop_bool_res_interp (Δ : List (lrel GF)) (op : un_op) (b : Bool) (τ : type) (v' : val)
    (h1 : unop_bool_res_type op = some τ) (h2 : un_op_eval op (LitV (LitBool b)) = some v') :
    ⊢ interp τ Δ v' v' := by
  cases op <;> simp [unop_bool_res_type] at h1
  subst h1
  simp [un_op_eval] at h2
  subst h2
  rw [interp_TBool]; dsimp only [lrel_bool]
  iexists _
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: `bin_log_related_unboxed_eq`. -/
theorem bin_log_related_unboxed_eq (Δ : List (lrel GF)) (Γ : varmap type)
    (e1 e2 e1' e2' : expr) (τ : type) (Hτ : UnboxedType τ) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
      〈Δ;Γ〉 ⊨ BinOp EqOp e1 e2 ≤log≤ BinOp EqOp e1' e2' : TBool := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map _ e2) (subst_map _ e2') IH2 v2 v2' #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v1 v1' #IH1
  ihave %hv1 := unboxed_type_sound τ Δ v1 v1' Hτ $$ IH1
  imod unboxed_type_eq τ Δ v1 v1' v2 v2' Hτ $$ IH1 IH2 with %heq
  have hl : bin_op_eval EqOp v1 v2 = some (LitV (LitBool (decide (v1 = v2)))) := by
    have hs : vals_compare_safe v1 v2 := Or.inl hv1.1
    simp [bin_op_eval, hs]
  have hr : bin_op_eval EqOp v1' v2' = some (LitV (LitBool (decide (v1' = v2')))) := by
    have hs : vals_compare_safe v1' v2' := Or.inl hv1.2
    simp [bin_op_eval, hs]
  have h1 : ▷^[1] (REL Val (LitV (LitBool (decide (v1 = v2)))) <<
        BinOp EqOp (Val v1') (Val v2') : interp TBool Δ) ⊢
      REL BinOp EqOp (Val v1) (Val v2) << BinOp EqOp (Val v1') (Val v2') : interp TBool Δ :=
    refines_pure_l 1 [] _ _ _ _ _ (Hpure := pure_binop EqOp v1 v2 _) hl
  have h2 : (REL Val (LitV (LitBool (decide (v1 = v2)))) <<
        Val (LitV (LitBool (decide (v1' = v2')))) : interp TBool Δ) ⊢
      REL Val (LitV (LitBool (decide (v1 = v2)))) << BinOp EqOp (Val v1') (Val v2') :
        interp TBool Δ :=
    refines_pure_r [] _ _ _ _ 1 _ (Hpure := pure_binop EqOp v1' v2' _) hr
  iapply h1
  inext
  iapply h2
  rel_values
  imodintro
  rw [interp_TBool]
  dsimp only [lrel_bool]
  iexists decide (v1 = v2)
  ipureintro
  refine ⟨rfl, ?_⟩
  simp only [heq]

/-- Rocq: `bin_log_related_int_binop`. -/
theorem bin_log_related_int_binop (Δ : List (lrel GF)) (Γ : varmap type) (op : bin_op)
    (e1 e2 e1' e2' : expr) (τ : type) (Hopτ : binop_int_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TInt) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TInt) -∗
      〈Δ;Γ〉 ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TInt]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map _ e2) (subst_map _ e2') IH2 v2 v2' IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v1 v1' IH1
  dsimp only [lrel_int]
  icases IH1 with ⟨%n, %hn⟩
  icases IH2 with ⟨%n', %hn'⟩
  obtain ⟨rfl, rfl⟩ := hn
  obtain ⟨rfl, rfl⟩ := hn'
  obtain ⟨v', Hopv'⟩ := binop_int_typed_safe op n n' τ Hopτ
  have h1 : ▷^[1] (REL Val v' << BinOp op (Val (LitV (LitInt n))) (Val (LitV (LitInt n'))) :
        interp τ Δ) ⊢
      REL BinOp op (Val (LitV (LitInt n))) (Val (LitV (LitInt n'))) <<
        BinOp op (Val (LitV (LitInt n))) (Val (LitV (LitInt n'))) : interp τ Δ :=
    refines_pure_l 1 [] _ _ _ _ _ (Hpure := pure_binop op _ _ v') Hopv'
  have h2 : (REL Val v' << Val v' : interp τ Δ) ⊢
      REL Val v' << BinOp op (Val (LitV (LitInt n))) (Val (LitV (LitInt n'))) : interp τ Δ :=
    refines_pure_r [] _ _ _ _ 1 _ (Hpure := pure_binop op _ _ v') Hopv'
  iapply h1
  inext
  iapply h2
  rel_values
  imodintro
  iapply binop_int_res_interp Δ op n n' τ v' Hopτ Hopv'

/-- Rocq: `bin_log_related_bool_binop`. -/
theorem bin_log_related_bool_binop (Δ : List (lrel GF)) (Γ : varmap type) (op : bin_op)
    (e1 e2 e1' e2' : expr) (τ : type) (Hopτ : binop_bool_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TBool) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TBool) -∗
      〈Δ;Γ〉 ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TBool]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map _ e2) (subst_map _ e2') IH2 v2 v2' IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v1 v1' IH1
  dsimp only [lrel_bool]
  icases IH1 with ⟨%n, %hn⟩
  icases IH2 with ⟨%n', %hn'⟩
  obtain ⟨rfl, rfl⟩ := hn
  obtain ⟨rfl, rfl⟩ := hn'
  obtain ⟨v', Hopv'⟩ := binop_bool_typed_safe op n n' τ Hopτ
  have h1 : ▷^[1] (REL Val v' << BinOp op (Val (LitV (LitBool n))) (Val (LitV (LitBool n'))) :
        interp τ Δ) ⊢
      REL BinOp op (Val (LitV (LitBool n))) (Val (LitV (LitBool n'))) <<
        BinOp op (Val (LitV (LitBool n))) (Val (LitV (LitBool n'))) : interp τ Δ :=
    refines_pure_l 1 [] _ _ _ _ _ (Hpure := pure_binop op _ _ v') Hopv'
  have h2 : (REL Val v' << Val v' : interp τ Δ) ⊢
      REL Val v' << BinOp op (Val (LitV (LitBool n))) (Val (LitV (LitBool n'))) :
        interp τ Δ :=
    refines_pure_r [] _ _ _ _ 1 _ (Hpure := pure_binop op _ _ v') Hopv'
  iapply h1
  inext
  iapply h2
  rel_values
  imodintro
  iapply binop_bool_res_interp Δ op n n' τ v' Hopτ Hopv'

/-- Rocq: `bin_log_related_int_unop`. -/
theorem bin_log_related_int_unop (Δ : List (lrel GF)) (Γ : varmap type) (op : un_op)
    (e e' : expr) (τ : type) (Hopτ : unop_int_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TInt) ⊢ 〈Δ;Γ〉 ⊨ UnOp op e ≤log≤ UnOp op e' : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TInt]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v v' IH
  dsimp only [lrel_int]
  icases IH with ⟨%n, %hn⟩
  obtain ⟨rfl, rfl⟩ := hn
  obtain ⟨w, Hopv'⟩ := unop_int_typed_safe op n τ Hopτ
  have h1 : ▷^[1] (REL Val w << UnOp op (Val (LitV (LitInt n))) : interp τ Δ) ⊢
      REL UnOp op (Val (LitV (LitInt n))) << UnOp op (Val (LitV (LitInt n))) : interp τ Δ :=
    refines_pure_l 1 [] _ _ _ _ _ (Hpure := pure_unop op _ w) Hopv'
  have h2 : (REL Val w << Val w : interp τ Δ) ⊢
      REL Val w << UnOp op (Val (LitV (LitInt n))) : interp τ Δ :=
    refines_pure_r [] _ _ _ _ 1 _ (Hpure := pure_unop op _ w) Hopv'
  iapply h1
  inext
  iapply h2
  rel_values
  imodintro
  iapply unop_int_res_interp Δ op n τ w Hopτ Hopv'

/-- Rocq: `bin_log_related_bool_unop`. -/
theorem bin_log_related_bool_unop (Δ : List (lrel GF)) (Γ : varmap type) (op : un_op)
    (e e' : expr) (τ : type) (Hopτ : unop_bool_res_type op = some τ) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TBool) ⊢ 〈Δ;Γ〉 ⊨ UnOp op e ≤log≤ UnOp op e' : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TBool]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v v' IH
  dsimp only [lrel_bool]
  icases IH with ⟨%n, %hn⟩
  obtain ⟨rfl, rfl⟩ := hn
  obtain ⟨w, Hopv'⟩ := unop_bool_typed_safe op n τ Hopτ
  have h1 : ▷^[1] (REL Val w << UnOp op (Val (LitV (LitBool n))) : interp τ Δ) ⊢
      REL UnOp op (Val (LitV (LitBool n))) << UnOp op (Val (LitV (LitBool n))) : interp τ Δ :=
    refines_pure_l 1 [] _ _ _ _ _ (Hpure := pure_unop op _ w) Hopv'
  have h2 : (REL Val w << Val w : interp τ Δ) ⊢
      REL Val w << UnOp op (Val (LitV (LitBool n))) : interp τ Δ :=
    refines_pure_r [] _ _ _ _ 1 _ (Hpure := pure_unop op _ w) Hopv'
  iapply h1
  inext
  iapply h2
  rel_values
  imodintro
  iapply unop_bool_res_interp Δ op n τ w Hopτ Hopv'

end fundamental

end Foxtrot.BinaryRel
