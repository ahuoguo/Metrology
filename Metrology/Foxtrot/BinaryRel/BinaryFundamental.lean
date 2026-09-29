module

public import Metrology.Foxtrot.BinaryRel.BinaryCompatibility
public import Metrology.Foxtrot.BinaryRel.BinaryInterp

/-!
# The fundamental theorem of Foxtrot's binary logical relation (part 1)

Ported from clutch/theories/foxtrot/binary_rel/binary_fundamental.v (lines 1-232: the
compatibility lemmas `bin_log_related_var` .. `bin_log_related_if`). Continued in
`BinaryFundamentalPart2.lean` .. `BinaryFundamentalPart5.lean` (import the last one for the
whole port).

## Rocq → Lean map
All Rocq names are kept (namespace `Foxtrot.BinaryRel`). The local Ltacs `intro_clause`
(`iIntros (vs) "#Hvs /="`) and `value_case` are inlined (`unfold bin_log_related`,
`iintro %vs #Hvs`, `simp only [subst_map]`; `rel_pure_l; rel_pure_r; rel_values`); the local
`rel_bind_ap e1 e2 IH v w Hv` is a local macro (as in `BinaryCompatibility`).

## Deviations
* `fst <$> vs` / `snd <$> vs` are `vs.map fun _ p => p.1` / `vs.map fun _ p => p.2`.
* The FType notations are spelled out: `τ1 * τ2` is `TProd τ1 τ2`, `τ1 + τ2` is `TSum τ1 τ2`,
  `τ1 → τ2` is `TArrow τ1 τ2`, `∀: τ` is `TForall τ`, `Λ: e` is `TLam e`, `e1;; e2` is
  `Seq e1 e2`, `<[x:=τ]>Γ` is `binder_insert x τ Γ`, `τ.[ren (+1)]` is
  `type.subst (type.ren (· + 1)) τ`.
* The binder-insertion lemmas `binder_insert_fmap`/`binder_delete_fmap` (Rocq: stdpp's
  `binder_insert_fmap` and `fmap_delete`) are proved locally.
* In `bin_log_related_rec` the Rocq case analysis on the binders (`destruct x, f`, rewriting
  with `subst_map_insert`, `delete_insert_*`, `subst_subst(_ne)`) is replaced by
  `subst_map_binder_insert_2`.
* `bin_log_related_tapp` (Rocq: via `bin_log_related_app` applied to `#()`) is proved
  directly by binding and instantiating the polymorphic value.

## Added helpers
* `binder_insert_fmap`, `binder_delete_fmap`, `subst_map_var_lookup`.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

/-- Added: `binder_insert` commutes with `map` (Rocq: stdpp's `binder_insert_fmap`). -/
theorem binder_insert_fmap {A B : Type} (f : A → B) (x : binder) (a : A) (m : varmap A) :
    (binder_insert x a m).map (fun _ v => f v) =
      binder_insert x (f a) (m.map fun _ v => f v) := by
  cases x with
  | BAnon => rfl
  | BNamed x =>
    apply Std.ExtTreeMap.ext_getElem?
    intro y
    simp only [binder_insert, Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert]
    split <;> rfl

/-- Added: `binder_delete` commutes with `map` (Rocq: stdpp's `fmap_delete`). -/
theorem binder_delete_fmap {A B : Type} (f : A → B) (x : binder) (m : varmap A) :
    binder_delete x (m.map fun _ v => f v) = (binder_delete x m).map (fun _ v => f v) := by
  cases x with
  | BAnon => rfl
  | BNamed x =>
    apply Std.ExtTreeMap.ext_getElem?
    intro y
    simp only [binder_delete, Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_erase]
    split <;> rfl

/-- Added: substituting a variable bound in the map. -/
theorem subst_map_var_lookup (vs : varmap val) (x : String) (v : val) (h : vs[x]? = some v) :
    subst_map vs (Var x) = Val v := by
  simp [subst_map, h]

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

/-- Rocq: `bin_log_related_var`. -/
theorem bin_log_related_var (Δ : List (lrel GF)) (Γ : varmap type) (x : String) (τ : type)
    (Hx : Γ[x]? = some τ) : ⊢ 〈Δ;Γ〉 ⊨ Var x ≤log≤ Var x : τ := by
  unfold bin_log_related
  iintro %vs #Hvs
  icases env_ltyped2_lookup _ vs x (interp τ Δ) (by simp [Std.ExtTreeMap.getElem?_map, Hx])
    $$ Hvs with ⟨%v1, %v2, %hv, HA⟩
  rw [subst_map_var_lookup _ x v1 (by simp [Std.ExtTreeMap.getElem?_map, hv]),
    subst_map_var_lookup _ x v2 (by simp [Std.ExtTreeMap.getElem?_map, hv])]
  iapply refines_ret (Val v1) (Val v2) v1 v2
  imodintro
  iexact HA

/-- Rocq: `bin_log_related_pair`. -/
theorem bin_log_related_pair (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 e1' e2' : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ1) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ2) -∗
      〈Δ;Γ〉 ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2 := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  rw [interp_TProd]
  iapply refines_pair $$ H1 H2

/-- Rocq: `bin_log_related_fst`. -/
theorem bin_log_related_fst (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TProd τ1 τ2) ⊢ 〈Δ;Γ〉 ⊨ Fst e ≤log≤ Fst e' : τ1 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v w IH
  rw [interp_TProd]; dsimp only [lrel_prod]
  icases IH with ⟨%v1, %v2, %w1, %w2, %h1, %h2, IHw, -⟩
  subst h1 h2
  rel_pure_l
  rel_pure_r
  rel_values

/-- Rocq: `bin_log_related_snd`. -/
theorem bin_log_related_snd (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TProd τ1 τ2) ⊢ 〈Δ;Γ〉 ⊨ Snd e ≤log≤ Snd e' : τ2 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v w IH
  rw [interp_TProd]; dsimp only [lrel_prod]
  icases IH with ⟨%v1, %v2, %w1, %w2, %h1, %h2, -, IHw⟩
  subst h1 h2
  rel_pure_l
  rel_pure_r
  rel_values

/-- Rocq: `bin_log_related_app`. -/
theorem bin_log_related_app (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 e1' e2' : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ1) -∗
      〈Δ;Γ〉 ⊨ App e1 e2 ≤log≤ App e1' e2' : τ2 := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  rw [interp_TArrow]
  iapply refines_app $$ H1 H2

/-- Rocq: `bin_log_related_rec`. -/
theorem bin_log_related_rec (Δ : List (lrel GF)) (Γ : varmap type) (f x : binder) (e e' : expr)
    (τ1 τ2 : type) :
    □ (〈Δ;binder_insert f (TArrow τ1 τ2) (binder_insert x τ1 Γ)〉 ⊨ e ≤log≤ e' : τ2) ⊢
      〈Δ;Γ〉 ⊨ Rec f x e ≤log≤ Rec f x e' : TArrow τ1 τ2 := by
  unfold bin_log_related
  iintro #Ht %vs #Hvs
  simp only [subst_map]
  rel_pure_l
  rel_pure_r
  rw [interp_TArrow]
  iapply refines_arrow_val
  imodintro
  iloeb as IH
  iintro %v1 %v2 #Hτ1
  let b1 := subst_map (binder_delete x (binder_delete f (vs.map fun _ p => p.1))) e
  let b2 := subst_map (binder_delete x (binder_delete f (vs.map fun _ p => p.2))) e'
  have hl : ▷^[1] (REL subst' x v1 (subst' f (RecV f x b1) b1) <<
        App (Val (RecV f x b2)) (Val v2) : interp τ2 Δ) ⊢
      REL App (Val (RecV f x b1)) (Val v1) << App (Val (RecV f x b2)) (Val v2) :
        interp τ2 Δ :=
    refines_pure_l 1 [] _ _ _ _ True trivial
  have hr : (REL subst' x v1 (subst' f (RecV f x b1) b1) <<
        subst' x v2 (subst' f (RecV f x b2) b2) : interp τ2 Δ) ⊢
      REL subst' x v1 (subst' f (RecV f x b1) b1) << App (Val (RecV f x b2)) (Val v2) :
        interp τ2 Δ :=
    refines_pure_r [] _ _ _ _ 1 True trivial
  iapply hl
  inext
  iapply hr
  have h1 : subst' x v1 (subst' f (RecV f x b1) b1) = subst_map
      ((binder_insert f (RecV f x b1, RecV f x b2) (binder_insert x (v1, v2) vs)).map
        fun _ p => p.1) e := by
    rw [binder_insert_fmap, binder_insert_fmap, subst_map_binder_insert_2]
  have h2 : subst' x v2 (subst' f (RecV f x b2) b2) = subst_map
      ((binder_insert f (RecV f x b1, RecV f x b2) (binder_insert x (v1, v2) vs)).map
        fun _ p => p.2) e' := by
    rw [binder_insert_fmap, binder_insert_fmap, subst_map_binder_insert_2]
  rw [h1, h2]
  iapply Ht
  rw [binder_insert_fmap, binder_insert_fmap]
  iapply env_ltyped2_insert $$ [IH]
  · rw [interp_TArrow]
    dsimp only [lrel_arr]
    imodintro
    iexact IH
  · iapply env_ltyped2_insert $$ Hτ1 Hvs

/-- Rocq: `bin_log_related_tlam`. -/
theorem bin_log_related_tlam (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) (τ : type) :
    (∀ A : lrel GF, □ (〈A :: Δ;⤉Γ〉 ⊨ e ≤log≤ e' : τ)) ⊢
      〈Δ;Γ〉 ⊨ TLam e ≤log≤ TLam e' : TForall τ := by
  unfold bin_log_related
  iintro #H %vs #Hvs
  simp only [subst_map, binder_delete]
  rel_pure_l
  rel_pure_r
  rw [interp_TForall]
  iapply refines_forall
  imodintro
  iintro %A
  iapply H $$ %A %vs
  rw [interp_ren]
  iexact Hvs

/-- Rocq: `bin_log_related_tapp'`. -/
theorem bin_log_related_tapp' (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr)
    (τ τ' : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TForall τ) ⊢ 〈Δ;Γ〉 ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/] := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v v' IH
  rw [interp_TForall]
  dsimp only [lrel_forall, lrel_arr]
  ispecialize IH $$ %(interp τ' Δ)
  icases IH with #IH
  rw [← interp_subst]
  iapply IH
  dsimp only [lrel_unit]
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: `bin_log_related_tapp`. -/
theorem bin_log_related_tapp (τi : lrel GF) (Δ : List (lrel GF)) (Γ : varmap type)
    (e e' : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TForall τ) ⊢ 〈τi :: Δ;⤉Γ〉 ⊨ TApp e ≤log≤ TApp e' : τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  rw [interp_ren]
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v v' IH
  rw [interp_TForall]
  dsimp only [lrel_forall, lrel_arr]
  ispecialize IH $$ %τi
  icases IH with #IH
  iapply IH
  dsimp only [lrel_unit]
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: `bin_log_related_seq`. -/
theorem bin_log_related_seq (R : lrel GF) (Δ : List (lrel GF)) (Γ : varmap type)
    (e1 e2 e1' e2' : expr) (τ1 τ2 : type) :
    (〈R :: Δ;⤉Γ〉 ⊨ e1 ≤log≤ e1' : τ1) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ2) -∗
      〈Δ;Γ〉 ⊨ Seq e1 e2 ≤log≤ Seq e1' e2' : τ2 := by
  unfold bin_log_related
  iintro He1 He2 %vs #Hvs
  simp only [subst_map, binder_delete]
  ihave H1 := He1 $$ %vs [Hvs]
  · rw [interp_ren]
    iexact Hvs
  ihave H2 := He2 $$ %vs Hvs
  iapply refines_seq (interp τ1 (R :: Δ)) $$ H1 H2

/-- Rocq: `bin_log_related_seq'`. -/
theorem bin_log_related_seq' (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 e1' e2' : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ1) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ2) -∗
      〈Δ;Γ〉 ⊨ Seq e1 e2 ≤log≤ Seq e1' e2' : τ2 := by
  iintro He1 He2
  iapply bin_log_related_seq lrel_true Δ Γ e1 e2 e1' e2' (type.subst (type.ren (· + 1)) τ1)
    τ2 $$ [He1] He2
  unfold bin_log_related
  iintro %vs #Hvs
  rw [interp_ren]
  have h := interp_ren_up [] Δ τ1 lrel_true
  simp only [List.nil_append, List.length_nil, upn_zero] at h
  rw [← h]
  iapply He1 $$ Hvs

/-- Rocq: `bin_log_related_injl`. -/
theorem bin_log_related_injl (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ1) ⊢ 〈Δ;Γ〉 ⊨ InjL e ≤log≤ InjL e' : TSum τ1 τ2 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TSum]
  iapply refines_injl
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_injr`. -/
theorem bin_log_related_injr (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr)
    (τ1 τ2 : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ2) ⊢ 〈Δ;Γ〉 ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2 := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TSum]
  iapply refines_injr
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_case`. -/
theorem bin_log_related_case (Δ : List (lrel GF)) (Γ : varmap type)
    (e0 e1 e2 e0' e1' e2' : expr) (τ1 τ2 τ3 : type) :
    (〈Δ;Γ〉 ⊨ e0 ≤log≤ e0' : TSum τ1 τ2) ⊢ (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TArrow τ1 τ3) -∗
      (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TArrow τ2 τ3) -∗
      〈Δ;Γ〉 ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3 := by
  unfold bin_log_related
  iintro IH1 IH2 IH3 %vs #Hvs
  simp only [subst_map]
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e0) (subst_map _ e0') IH1 v0 v0' IH1
  rw [interp_TSum]
  dsimp only [lrel_sum]
  icases IH1 with ⟨%w, %w', ⟨%hw, %hw', #Hw⟩ | ⟨%hw, %hw', #Hw⟩⟩
  · subst hw hw'
    rel_pures_l
    rel_pures_r
    rw [interp_TArrow Δ τ1 τ3]
    ihave IH2 := IH2 $$ %vs Hvs
    iapply refines_app $$ IH2
    rel_values
  · subst hw hw'
    rel_pures_l
    rel_pures_r
    rw [interp_TArrow Δ τ2 τ3]
    ihave IH3 := IH3 $$ %vs Hvs
    iapply refines_app $$ IH3
    rel_values

/-- Rocq: `bin_log_related_if`. -/
theorem bin_log_related_if (Δ : List (lrel GF)) (Γ : varmap type)
    (e0 e1 e2 e0' e1' e2' : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e0 ≤log≤ e0' : TBool) ⊢ (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : τ) -∗
      (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗ 〈Δ;Γ〉 ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ := by
  unfold bin_log_related
  iintro IH1 IH2 IH3 %vs #Hvs
  simp only [subst_map]
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e0) (subst_map _ e0') IH1 v0 v0' IH1
  rw [interp_TBool]
  dsimp only [lrel_bool]
  icases IH1 with ⟨%b, %hb⟩
  obtain ⟨rfl, rfl⟩ := hb
  cases b
  · rel_pures_l
    rel_pures_r
    iapply IH3 $$ Hvs
  · rel_pures_l
    rel_pures_r
    iapply IH2 $$ Hvs

end fundamental

end Foxtrot.BinaryRel
