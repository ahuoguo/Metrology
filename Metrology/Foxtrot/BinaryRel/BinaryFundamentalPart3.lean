module

public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart2

/-!
# The fundamental theorem of Foxtrot's binary logical relation (part 3)

Ported from clutch/theories/foxtrot/binary_rel/binary_fundamental.v (lines 420-615: the
compatibility lemmas `bin_log_related_unfold` .. `bin_log_related_FAA`).

## Rocq → Lean map
All Rocq names are kept (namespace `Foxtrot.BinaryRel`).

## Deviations
* `μ: τ` is `TRec τ`, `∃: τ` is `TExists τ`, `τ.[(TRec τ)/]` is `τ.[TRec τ/]`,
  `unpack: x := e1 in e2` is `App (App (Val unpack) e1) (Lam x e2)`.
* The one-step unfolding of the recursive interpretation (Rocq:
  `rewrite lrel_rec_unfold /lrel_car /=` and `change`) is the added `interp_TRec_unfold`.
* In `bin_log_related_CmpXchg_EqType` the case split is on `w1 = v2` (the value stored on the
  LHS against the expected value) instead of Rocq's `v1 = v2'`.
* The atomic steps (Rocq: `rewrite -(fill_empty ..); iApply refines_atomic_l`) instantiate
  `refines_atomic_l` with the empty context through a `have`, as in `BinaryCompatibility`.

## Added helpers
* `interp_TRec_unfold`.
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

/-- Added: unfolding the interpretation of a recursive type. -/
theorem interp_TRec_unfold (Δ : List (lrel GF)) (τ : type) (v v' : val) :
    interp (TRec τ) Δ v v' ⊣⊢ ▷ interp τ (interp (TRec τ) Δ :: Δ) v v' := by
  rw [interp_TRec]
  nth_rw 1 [lrel_rec_unfold]
  exact .rfl

/-- Rocq: `bin_log_related_unfold`. -/
theorem bin_log_related_unfold (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr)
    (τ : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TRec τ) ⊢
      〈Δ;Γ〉 ⊨ App (Val rec_unfold) e ≤log≤ App (Val rec_unfold) e' : τ.[TRec τ/] := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  ihave IH := IH $$ %vs Hvs
  rel_bind_ap (subst_map _ e) (subst_map _ e') IH v v' IH
  ihave IH := (interp_TRec_unfold Δ τ v v').1 $$ IH
  rel_rec_l
  rel_rec_r
  rel_values
  imodintro
  rw [← interp_subst]
  iexact IH

/-- Rocq: `bin_log_related_fold`. -/
theorem bin_log_related_fold (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) (τ : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ.[TRec τ/]) ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e' : TRec τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs Hvs
  have h : (REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
        interp (τ.[TRec τ/]) Δ) ⊢
      (∀ v v', interp (τ.[TRec τ/]) Δ v v' -∗ REL Val v << Val v' : interp (TRec τ) Δ) -∗
        REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
          interp (TRec τ) Δ :=
    refines_bind [] [] _ _ _ _
  iapply h $$ IH
  iintro %v %v' IH
  rel_values
  imodintro
  iapply (interp_TRec_unfold Δ τ v v').2
  inext
  rw [interp_subst]
  iexact IH

/-- Rocq: `bin_log_related_pack'`. -/
theorem bin_log_related_pack' (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr)
    (τ τ' : type) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : τ.[τ'/]) ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e' : TExists τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs Hvs
  have h : (REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
        interp (τ.[τ'/]) Δ) ⊢
      (∀ v v', interp (τ.[τ'/]) Δ v v' -∗ REL Val v << Val v' : interp (TExists τ) Δ) -∗
        REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
          interp (TExists τ) Δ :=
    refines_bind [] [] _ _ _ _
  iapply h $$ IH
  iintro %v %v' #IH
  rel_values
  imodintro
  rw [interp_TExists]
  dsimp only [lrel_exists]
  iexists interp τ' Δ
  rw [interp_subst]
  iexact IH

/-- Rocq: `bin_log_related_pack`. -/
theorem bin_log_related_pack (τi : lrel GF) (Δ : List (lrel GF)) (Γ : varmap type)
    (e e' : expr) (τ : type) :
    (〈τi :: Δ;⤉Γ〉 ⊨ e ≤log≤ e' : τ) ⊢ 〈Δ;Γ〉 ⊨ e ≤log≤ e' : TExists τ := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH := IH $$ %vs [Hvs]
  · rw [interp_ren]
    iexact Hvs
  have h : (REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
        interp τ (τi :: Δ)) ⊢
      (∀ v v', interp τ (τi :: Δ) v v' -∗ REL Val v << Val v' : interp (TExists τ) Δ) -∗
        REL subst_map (vs.map fun _ p => p.1) e << subst_map (vs.map fun _ p => p.2) e' :
          interp (TExists τ) Δ :=
    refines_bind [] [] _ _ _ _
  iapply h $$ IH
  iintro %v %v' #IH
  rel_values
  imodintro
  rw [interp_TExists]
  dsimp only [lrel_exists]
  iexists τi
  iexact IH

/-- Rocq: `bin_log_related_unpack`. -/
theorem bin_log_related_unpack (Δ : List (lrel GF)) (Γ : varmap type) (x : binder)
    (e1 e1' e2 e2' : expr) (τ τ2 : type) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TExists τ) ⊢
      (∀ τi : lrel GF,
        〈τi :: Δ;binder_insert x τ (⤉Γ)〉 ⊨ e2 ≤log≤ e2' : type.subst (type.ren (· + 1)) τ2) -∗
      〈Δ;Γ〉 ⊨ App (App (Val unpack) e1) (Lam x e2) ≤log≤
        App (App (Val unpack) e1') (Lam x e2') : τ2 := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rel_pure_l
  rel_pure_r
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v v' #IH1
  rw [interp_TExists]
  dsimp only [lrel_exists]
  icases IH1 with ⟨%A, #IH⟩
  rel_rec_l
  rel_pure_l
  rel_pure_l
  rel_rec_r
  rel_pure_r
  rel_pure_r
  let b1 := subst_map (binder_delete x (binder_delete BAnon (vs.map fun _ p => p.1))) e2
  let b2 := subst_map (binder_delete x (binder_delete BAnon (vs.map fun _ p => p.2))) e2'
  have hl : ▷^[1] (REL subst' x v b1 << App (Val (RecV BAnon x b2)) (Val v') : interp τ2 Δ) ⊢
      REL App (Val (RecV BAnon x b1)) (Val v) << App (Val (RecV BAnon x b2)) (Val v') :
        interp τ2 Δ :=
    refines_pure_l 1 [] _ _ _ _ True trivial
  have hr : (REL subst' x v b1 << subst' x v' b2 : interp τ2 Δ) ⊢
      REL subst' x v b1 << App (Val (RecV BAnon x b2)) (Val v') : interp τ2 Δ :=
    refines_pure_r [] _ _ _ _ 1 True trivial
  iapply hl
  inext
  iapply hr
  have h1 : subst' x v b1 =
      subst_map ((binder_insert x (v, v') vs).map fun _ p => p.1) e2 := by
    rw [binder_insert_fmap, subst_map_binder_insert]
    try rfl
  have h2 : subst' x v' b2 =
      subst_map ((binder_insert x (v, v') vs).map fun _ p => p.2) e2' := by
    rw [binder_insert_fmap, subst_map_binder_insert]
    try rfl
  rw [h1, h2]
  have hren := interp_ren_up [] Δ τ2 A
  simp only [List.nil_append, List.length_nil, upn_zero] at hren
  rw [hren]
  iapply IH2 $$ %A %(binder_insert x (v, v') vs)
  rw [binder_insert_fmap, interp_ren]
  iapply env_ltyped2_insert $$ IH Hvs

/-- Rocq: `bin_log_related_fork`. -/
theorem bin_log_related_fork (Δ : List (lrel GF)) (Γ : varmap type) (e e' : expr) :
    (〈Δ;Γ〉 ⊨ e ≤log≤ e' : TUnit) ⊢ 〈Δ;Γ〉 ⊨ Fork e ≤log≤ Fork e' : TUnit := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  simp only [subst_map]
  rw [interp_TUnit]
  iapply refines_fork
  iapply IH $$ Hvs

/-- Rocq: `bin_log_related_CmpXchg_EqType`. -/
theorem bin_log_related_CmpXchg_EqType (Δ : List (lrel GF)) (Γ : varmap type)
    (e1 e2 e3 e1' e2' e3' : expr) (τ : type) (Hτ : EqType τ) (Hτ' : UnboxedType τ) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
      (〈Δ;Γ〉 ⊨ e3 ≤log≤ e3' : τ) -∗
      〈Δ;Γ〉 ⊨ CmpXchg e1 e2 e3 ≤log≤ CmpXchg e1' e2' e3' : TProd τ TBool := by
  unfold bin_log_related
  iintro IH1 IH2 IH3 %vs #Hvs
  simp only [subst_map]
  ihave IH3 := IH3 $$ %vs Hvs
  rel_bind_ap (subst_map _ e3) (subst_map _ e3') IH3 v3 v3' #IH3
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map _ e2) (subst_map _ e2') IH2 v2 v2' #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v1 v1' #IH1
  rw [interp_TRef]
  dsimp only [lrel_ref]
  icases IH1 with ⟨%l, %l', %h1, %h1', #Hinv⟩
  subst h1 h1'
  ihave %hub := unboxed_type_sound τ Δ v2 v2' Hτ' $$ IH2
  ihave %h2 := eq_type_sound τ Δ v2 v2' Hτ $$ IH2
  ihave %h3 := eq_type_sound τ Δ v3 v3' Hτ $$ IH3
  subst h2 h3
  have hsafe : vals_compare_safe v2 v2 := Or.inl hub.1
  have h : _ ⊢ REL CmpXchg (Val (LitV (LitLoc l))) (Val v2) (Val v3) <<
      CmpXchg (Val (LitV (LitLoc l'))) (Val v2) (Val v3) : interp (TProd τ TBool) Δ :=
    refines_atomic_l (⊤ \ ↑(logN.@ (l, l'))) []
      (CmpXchg (Val (LitV (LitLoc l))) (Val v2) (Val v3)) _ _
  iapply h
  iintro %K' %j Hspec
  iinv Hinv with ⟨%w1, %w2, >Hv1, >Hv2, #Hv⟩ Hclose
  imodintro
  ihave Hw : iprop(▷ ⌜w1 = w2⌝) $$ [Hv]
  · inext
    iapply eq_type_sound τ Δ w1 w2 Hτ $$ Hv
  imod Hw with %hw
  subst hw
  have hsafe' : vals_compare_safe w1 v2 := Or.inr hub.1
  by_cases hs : w1 = v2
  · subst hs
    iapply wp_pupd
    wp_cmpxchg_suc
    tp_cmpxchg_suc j
    imodintro
    imod Hclose $$ [Hv1 Hv2]
    · inext
      iexists v3, v3
      iframe Hv1 Hv2 IH3
    imodintro
    iexists Val (PairV w1 (LitV (LitBool true)))
    iframe Hspec
    rel_values
    imodintro
    rw [interp_TProd, interp_TBool]
    dsimp only [lrel_prod, lrel_bool]
    iexists w1, w1, LitV (LitBool true), LitV (LitBool true)
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitl
    · iexact Hv
    · iexists true
      ipureintro; exact ⟨rfl, rfl⟩
  · iapply wp_pupd
    wp_cmpxchg_fail
    tp_cmpxchg_fail j
    imodintro
    imod Hclose $$ [Hv1 Hv2]
    · inext
      iexists w1, w1
      iframe Hv1 Hv2 Hv
    imodintro
    iexists Val (PairV w1 (LitV (LitBool false)))
    iframe Hspec
    rel_values
    imodintro
    rw [interp_TProd, interp_TBool]
    dsimp only [lrel_prod, lrel_bool]
    iexists w1, w1, LitV (LitBool false), LitV (LitBool false)
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitl
    · iexact Hv
    · iexists false
      ipureintro; exact ⟨rfl, rfl⟩

/-- Rocq: `bin_log_related_CmpXchg`. -/
theorem bin_log_related_CmpXchg (Δ : List (lrel GF)) (Γ : varmap type)
    (e1 e2 e3 e1' e2' e3' : expr) (τ : type) (Hτ : UnboxedType τ) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
      (〈Δ;Γ〉 ⊨ e3 ≤log≤ e3' : τ) -∗
      〈Δ;Γ〉 ⊨ CmpXchg e1 e2 e3 ≤log≤ CmpXchg e1' e2' e3' : TProd τ TBool := by
  rcases unboxed_type_ref_or_eqtype τ Hτ with hτ | ⟨τ', rfl⟩
  · exact bin_log_related_CmpXchg_EqType Δ Γ e1 e2 e3 e1' e2' e3' τ hτ Hτ
  · unfold bin_log_related
    iintro H1 H2 H3 %vs #Hvs
    ispecialize H1 $$ %vs Hvs
    ispecialize H2 $$ %vs Hvs
    ispecialize H3 $$ %vs Hvs
    simp only [subst_map]
    rw [interp_TProd, interp_TRef, interp_TRef, interp_TBool]
    iapply refines_cmpxchg_ref $$ H1 H2 H3

/-- Rocq: `bin_log_related_xchg`. -/
theorem bin_log_related_xchg (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 e1' e2' : expr)
    (τ : type) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TRef τ) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : τ) -∗
      〈Δ;Γ〉 ⊨ Xchg e1 e2 ≤log≤ Xchg e1' e2' : τ := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef]
  ihave H1 := IH1 $$ %vs Hvs
  ihave H2 := IH2 $$ %vs Hvs
  iapply refines_xchg $$ H1 H2

/-- Rocq: `bin_log_related_FAA`. -/
theorem bin_log_related_FAA (Δ : List (lrel GF)) (Γ : varmap type) (e1 e2 e1' e2' : expr) :
    (〈Δ;Γ〉 ⊨ e1 ≤log≤ e1' : TRef TNat) ⊢ (〈Δ;Γ〉 ⊨ e2 ≤log≤ e2' : TNat) -∗
      〈Δ;Γ〉 ⊨ FAA e1 e2 ≤log≤ FAA e1' e2' : TNat := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  simp only [subst_map]
  rw [interp_TRef, interp_TNat]
  ihave IH2 := IH2 $$ %vs Hvs
  rel_bind_ap (subst_map _ e2) (subst_map _ e2') IH2 v2 v2' #IH2
  ihave IH1 := IH1 $$ %vs Hvs
  rel_bind_ap (subst_map _ e1) (subst_map _ e1') IH1 v1 v1' #IH1
  dsimp only [lrel_ref]
  icases IH1 with ⟨%l, %l', %h1, %h1', #Hinv⟩
  subst h1 h1'
  icases (show lrel_nat v2 v2' ⊢@{IProp GF}
      iprop(∃ n : ℕ, ⌜v2 = LitV (LitInt (n : ℤ)) ∧ v2' = LitV (LitInt (n : ℤ))⌝) from .rfl)
    $$ IH2 with ⟨%n, %hn⟩
  obtain ⟨rfl, rfl⟩ := hn
  have h : _ ⊢ REL FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt (n : ℤ)))) <<
      FAA (Val (LitV (LitLoc l'))) (Val (LitV (LitInt (n : ℤ)))) : lrel_nat (GF := GF) :=
    refines_atomic_l (⊤ \ ↑(logN.@ (l, l'))) []
      (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt (n : ℤ))))) _ _
  iapply h
  iintro %K' %j Hspec
  iinv Hinv with ⟨%w1, %w2, >Hv1, >Hv2, Hv⟩ Hclose
  ihave Hw : iprop(▷ ⌜∃ n1 : ℕ, w1 = LitV (LitInt (n1 : ℤ)) ∧ w2 = LitV (LitInt (n1 : ℤ))⌝)
    $$ [Hv]
  · inext
    icases (show lrel_nat w1 w2 ⊢@{IProp GF}
        iprop(∃ n : ℕ, ⌜w1 = LitV (LitInt (n : ℤ)) ∧ w2 = LitV (LitInt (n : ℤ))⌝) from .rfl)
      $$ Hv with ⟨%n1, %hn1⟩
    ipureintro
    exact ⟨n1, hn1⟩
  imod Hw with %⟨n1, hn1⟩
  obtain ⟨rfl, rfl⟩ := hn1
  imodintro
  iapply wp_pupd
  wp_faa
  tp_faa j
  imodintro
  imod Hclose $$ [Hv1 Hv2]
  · inext
    iexists LitV (LitInt ((n1 : ℤ) + (n : ℤ))), LitV (LitInt ((n1 : ℤ) + (n : ℤ)))
    iframe Hv1 Hv2
    dsimp only [lrel_nat]
    iexists n1 + n
    ipureintro
    push_cast
    exact ⟨rfl, rfl⟩
  imodintro
  iexists Val (LitV (LitInt (n1 : ℤ)))
  iframe Hspec
  rel_values
  imodintro
  dsimp only [lrel_nat]
  iexists n1
  ipureintro
  exact ⟨rfl, rfl⟩

end fundamental

end Foxtrot.BinaryRel
