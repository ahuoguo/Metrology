module

public import Metrology.Foxtrot.BinaryRel.BinaryRelTactics
public import Metrology.Foxtrot.CouplingRules
public import Metrology.Foxtrot.CouplingRulesMisc

/-!
# Compatibility rules of Foxtrot's binary logical relation

Ported from clutch/theories/foxtrot/binary_rel/binary_compatibility.v

## Rocq → Lean map
All Rocq names are kept (namespace `Foxtrot.BinaryRel`): `refines_pair`, `refines_injl`,
`refines_injr`, `refines_app`, `refines_seq`, `refines_pack`, `refines_forall`,
`refines_store`, `refines_load`, `refines_rand_tape`, `refines_rand_unit`,
`refines_cmpxchg_ref`, `refines_xchg`. The local Ltac `rel_bind_ap` is a local macro
(`rel_bind_ap e1 e2 IH v w Hvs`); Rocq's local `unfold_rel` is the `unfold_rel` macro of
`BinaryModel`.

## Deviations
* The `lrel_scope` notations are spelled out: `A * B` is `lrel_prod A B`, `τ1 + τ2` is
  `lrel_sum τ1 τ2`, `A → B` is `lrel_arr A B`, `ref A` is `lrel_ref A`, `()` is `lrel_unit`,
  `∃ A, C A` is `lrel_exists C`, `∀ A, C A` is `lrel_forall C`. Expressions: `(e1, e2)` is
  `Pair e1 e2`, `e1;; e2` is `Seq e1 e2`, `e1 <- e2` is `Store e1 e2`, `!e` is `Load e`,
  `rand(e2) e1` is `Rand e1 e2`, `rand e` is `Rand e (Val (LitV LitUnit))`,
  `(λ: <>, e)%V` is `Val (RecV BAnon BAnon e)`.
* The coupling rules `wp_couple_rand_lbl_rand_lbl(_wrong)`/`wp_couple_rand_rand` are applied
  with the bijection `f := id` (Rocq: inferred).
* The impossible cases of `refines_cmpxchg_ref` (Rocq: nested `destruct (decide ..)` with
  `iInv`s) go through the added helper `compat_inv_clash`; the case split is on the
  observed values (`w1 = #r1`, `w2 = #r2`) instead of `(v1, v2) = (#r1, #r2)`.
* In `refines_forall` the final beta-steps are done with `rel_pures_l`/`rel_pures_r`
  instead of unfolding and `wp_pures`/`tp_pures`.

## Omitted
* Commented-out Rocq code (`value_case`, `rel_store_l_atomic`, the commented `iMod`s).

## Added helpers
* `compat_spec_heap_frag_timeless`, `compat_spec_tapes_frag_timeless` (instances: the spec
  points-tos are timeless; Rocq infers them by unfolding), `compat_pointsto_excl`,
  `compat_spec_pointsto_excl`, `compat_inv_clash`.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

/-! ## Helpers -/

section helpers

variable {GF : BundledGFunctors} [specG_con_prob_lang GF]

attribute [local instance] specG_con_prob_lang.specG_con_prob_lang_heap in
/-- Helper (Rocq: inferred by unfolding `spec_heap_frag`): the spec points-to is timeless. -/
instance compat_spec_heap_frag_timeless (l : Loc) (v : val) (dq : DFrac) :
    Timeless (spec_heap_frag (GF := GF) l v dq) := by
  unfold spec_heap_frag
  infer_instance

attribute [local instance] specG_con_prob_lang.specG_con_prob_lang_tapes in
/-- Helper (Rocq: inferred by unfolding `spec_tapes_frag`): the spec tape points-to is
timeless. -/
instance compat_spec_tapes_frag_timeless (l : Loc) (t : tape) (dq : DFrac) :
    Timeless (spec_tapes_frag (GF := GF) l t dq) := by
  unfold spec_tapes_frag
  infer_instance

end helpers

section helpers2

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Helper: the (full) points-to of the LHS heap is exclusive. -/
theorem compat_pointsto_excl (l : Loc) (v w : val) :
    ⊢@{IProp GF} l ↦ v -∗ l ↦ w -∗ False := by
  iintro H1 H2
  ihave %Hne := ghost_map_elem_ne (H := locF) _ l l (DFrac.own 1) v w $$ H1 H2
  exact (Hne rfl).elim

/-- Helper: the (full) spec points-to is exclusive. -/
theorem compat_spec_pointsto_excl (l : Loc) (v w : val) :
    ⊢@{IProp GF} l ↦ₛ v -∗ l ↦ₛ w -∗ False := by
  iintro H1 H2
  unfold spec_heap_frag
  let _ : GhostMapG GF Loc val locF := specG_con_prob_lang.specG_con_prob_lang_heap
  ihave %Hne := ghost_map_elem_ne (H := locF) _ l l (DFrac.own 1) v w $$ H1 H2
  exact (Hne rfl).elim

/-- Helper (Rocq: the case analyses in the impossible cases of `refines_cmpxchg_ref`): with the
invariant `logN.@ p0` open (and the resource `R` taken from it), two invariants `logN.@ p` and
`logN.@ q` (`p ≠ q`) whose contents clash pairwise with each other and with `R` give a
contradiction. -/
theorem compat_inv_clash (p0 p q : Loc × Loc) (R Pp Pq : IProp GF) (hpq : p ≠ q)
    (h1 : p0 = p → ⊢ R -∗ Pq -∗ False) (h2 : p0 = q → ⊢ R -∗ Pp -∗ False)
    (h3 : ⊢ Pp -∗ Pq -∗ False) :
    ⊢ R -∗ inv (logN.@ p) Pp -∗ inv (logN.@ q) Pq -∗ |={⊤ \ ↑(logN.@ p0)}=> False := by
  have hsub : ∀ p' : Loc × Loc, p0 ≠ p' →
      (↑(logN.@ p') : CoPset) ⊆ ⊤ \ (↑(logN.@ p0) : CoPset) := fun p' hne x hx =>
    CoPset.in_diff.mpr ⟨CoPset.mem_full, fun hx0 => ndot_ne_disjoint _ hne x ⟨hx0, hx⟩⟩
  iintro HR Hp Hq
  by_cases hp : p0 = p
  · imod inv_acc (hsub q (hp ▸ hpq)) $$ Hq with ⟨HPq, -⟩
    ihave Hbot : iprop(▷ False) $$ [HR HPq]
    · inext
      iapply h1 hp $$ HR HPq
    imod Hbot with %h
    exact h.elim
  by_cases hq : p0 = q
  · imod inv_acc (hsub p hp) $$ Hp with ⟨HPp, -⟩
    ihave Hbot : iprop(▷ False) $$ [HR HPp]
    · inext
      iapply h2 hq $$ HR HPp
    imod Hbot with %h
    exact h.elim
  have hsub2 : (↑(logN.@ q) : CoPset) ⊆ (⊤ \ ↑(logN.@ p0)) \ ↑(logN.@ p) := fun x hx =>
    CoPset.in_diff.mpr ⟨hsub q hq x hx, fun hxp => ndot_ne_disjoint _ hpq x ⟨hxp, hx⟩⟩
  imod inv_acc (hsub p hp) $$ Hp with ⟨HPp, -⟩
  imod inv_acc hsub2 $$ Hq with ⟨HPq, -⟩
  ihave Hbot : iprop(▷ False) $$ [HPp HPq]
  · inext
    iapply h3 $$ HPp HPq
  imod Hbot with %h
  exact h.elim

end helpers2

section compatibility

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: the local tactic `rel_bind_ap e1 e2 IH v w Hvs`: bind `e1` on the LHS and `e2` on the
RHS, apply `refines_bind` with `IH` and introduce the resulting values `v`, `w` and their
interpretation `Hvs`. -/
local macro "rel_bind_ap " e1:term:max ppSpace e2:term:max ppSpace IH:ident ppSpace v:ident
    ppSpace w:ident ppSpace Hv:introPat : tactic => `(tactic| focus
      rel_bind_l $e1
      rel_bind_r $e2
      iapply refines_bind $$ $IH:ident
      iintro %$v:ident %$w:ident $Hv:introPat
      rel_finish)

/-- Rocq: `refines_pair`. -/
theorem refines_pair (e1 e2 e1' e2' : expr) (A B : lrel GF) :
    (REL e1 << e1' : A) ⊢ (REL e2 << e2' : B) -∗
      REL Pair e1 e2 << Pair e1' e2' : lrel_prod A B := by
  unfold_rel
  iintro IH1 IH2 %K %j Hspec
  tp_bind j e2'
  ispecialize IH2 $$ %_ %j Hspec
  wp_bind e2
  wp_apply wp_wand $$ IH2
  iintro %v2 ⟨%v2', Hspec, H2⟩
  wp_bind e1
  tp_bind j e1'
  ispecialize IH1 $$ %_ %j Hspec
  wp_apply wp_wand $$ IH1
  iintro %v1 ⟨%v1', Hspec, H1⟩
  tp_pures j
  wp_pures
  imodintro
  iexists PairV v1' v2'
  iframe Hspec
  dsimp only [lrel_prod]
  iexists v1, v1', v2, v2'
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  iframe H1 H2

/-- Rocq: `refines_injl`. -/
theorem refines_injl (e e' : expr) (τ1 τ2 : lrel GF) :
    (REL e << e' : τ1) ⊢ REL InjL e << InjL e' : lrel_sum τ1 τ2 := by
  unfold_rel
  iintro IH %K %j Hspec
  tp_bind j e'
  ispecialize IH $$ %_ %j Hspec
  wp_apply wp_wand $$ IH
  iintro %v ⟨%v', Hspec, Hv⟩
  tp_pures j
  wp_pures
  imodintro
  iexists InjLV v'
  iframe Hspec
  dsimp only [lrel_sum]
  iexists v, v'
  ileft
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  iexact Hv

/-- Rocq: `refines_injr`. -/
theorem refines_injr (e e' : expr) (τ1 τ2 : lrel GF) :
    (REL e << e' : τ2) ⊢ REL InjR e << InjR e' : lrel_sum τ1 τ2 := by
  unfold_rel
  iintro IH %K %j Hspec
  tp_bind j e'
  ispecialize IH $$ %_ %j Hspec
  wp_apply wp_wand $$ IH
  iintro %v ⟨%v', Hspec, Hv⟩
  tp_pures j
  wp_pures
  imodintro
  iexists InjRV v'
  iframe Hspec
  dsimp only [lrel_sum]
  iexists v, v'
  iright
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  iexact Hv

/-- Rocq: `refines_app`. -/
theorem refines_app (e1 e2 e1' e2' : expr) (A B : lrel GF) :
    (REL e1 << e1' : lrel_arr A B) ⊢ (REL e2 << e2' : A) -∗
      REL App e1 e2 << App e1' e2' : B := by
  unfold_rel
  iintro IH1 IH2 %K %j Hspec
  tp_bind j e2'
  ispecialize IH2 $$ %_ %j Hspec
  wp_bind e2
  wp_apply wp_wand $$ IH2
  iintro %v2 ⟨%v2', Hspec, H2⟩
  wp_bind e1
  tp_bind j e1'
  ispecialize IH1 $$ %_ %j Hspec
  wp_apply wp_wand $$ IH1
  iintro %v1 ⟨%v1', Hspec, H1⟩
  tp_normalise j
  dsimp only [lrel_arr]
  icases H1 with #H1
  ihave H := H1 $$ H2
  unfold_rel
  iapply H $$ %K %j Hspec

/-- Rocq: `refines_seq`. -/
theorem refines_seq (A : lrel GF) (e1 e2 e1' e2' : expr) (B : lrel GF) :
    (REL e1 << e1' : A) ⊢ (REL e2 << e2' : B) -∗
      REL Seq e1 e2 << Seq e1' e2' : B := by
  unfold_rel
  iintro IH1 IH2 %K %j Hspec
  wp_bind e1
  tp_bind j e1'
  ispecialize IH1 $$ %_ %j Hspec
  wp_apply wp_wand $$ IH1
  iintro %v ⟨%v', Hspec, -⟩
  wp_pures
  tp_pures j
  iapply IH2 $$ %K %j Hspec

/-- Rocq: `refines_pack`. -/
theorem refines_pack (A : lrel GF) (e e' : expr) (C : lrel GF → lrel GF) :
    (REL e << e' : C A) ⊢ REL e << e' : lrel_exists C := by
  unfold_rel
  iintro H %K %j Hspec
  ispecialize H $$ %K %j Hspec
  iapply wp_wand $$ H
  iintro %v ⟨%v', Hspec, Hv⟩
  iexists v'
  iframe Hspec
  dsimp only [lrel_exists]
  iexists A
  iexact Hv

/-- Rocq: `refines_forall`. -/
theorem refines_forall (e e' : expr) (C : lrel GF → lrel GF) :
    □ (∀ A, REL e << e' : C A) ⊢
      REL Val (RecV BAnon BAnon e) << Val (RecV BAnon BAnon e') : lrel_forall C := by
  iintro #H
  rel_values
  imodintro
  dsimp only [lrel_forall, lrel_arr, lrel_unit]
  iintro %A !> %v1 %v2 %⟨hv1, hv2⟩
  subst hv1 hv2
  rel_pures_l
  rel_pures_r
  iapply H

/-- Rocq: `refines_store`. -/
theorem refines_store (e1 e2 e1' e2' : expr) (A : lrel GF) :
    (REL e1 << e1' : lrel_ref A) ⊢ (REL e2 << e2' : A) -∗
      REL Store e1 e2 << Store e1' e2' : lrel_unit := by
  unfold_rel
  iintro IH1 IH2 %K %j Hspec
  tp_bind j e2'
  ispecialize IH2 $$ %_ %j Hspec
  wp_bind e2
  wp_apply wp_wand $$ IH2
  iintro %v2 ⟨%v2', Hspec, HA⟩
  wp_bind e1
  tp_bind j e1'
  ispecialize IH1 $$ %_ %j Hspec
  wp_apply wp_wand $$ IH1
  iintro %v1 ⟨%v1', Hspec, #H⟩
  dsimp only [lrel_ref]
  icases H with ⟨%l1, %l2, %h1, %h2, #Hinv⟩
  subst h1 h2
  iinv Hinv with ⟨%w1, %w2, >Hl1, >Hl2, -⟩ Hclose
  tp_store j
  wp_store
  imod Hclose $$ [HA Hl1 Hl2]
  · inext
    iexists v2, v2'
    iframe HA Hl1 Hl2
  imodintro
  iexists LitV LitUnit
  iframe Hspec
  dsimp only [lrel_unit]
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: `refines_load`. -/
theorem refines_load (e e' : expr) (A : lrel GF) :
    (REL e << e' : lrel_ref A) ⊢ REL Load e << Load e' : A := by
  iintro H
  unfold_rel
  iintro %K %j Hspec
  tp_bind j e'
  ispecialize H $$ %_ %j Hspec
  wp_apply wp_wand $$ H
  iintro %v ⟨%v', Hspec, #H⟩
  dsimp only [lrel_ref]
  icases H with ⟨%l1, %l2, %h1, %h2, #Hinv⟩
  subst h1 h2
  iinv Hinv with ⟨%w1, %w2, >Hl1, >Hl2, #Hw⟩ Hclose
  tp_load j
  wp_load
  imod Hclose $$ [Hl1 Hl2]
  · inext
    iexists w1, w2
    iframe Hl1 Hl2 Hw
  imodintro
  iexists w2
  iframe Hspec Hw

/-- Rocq: `refines_rand_tape`. -/
theorem refines_rand_tape (e1 e1' e2 e2' : expr) :
    (REL e1 << e1' : (lrel_nat : lrel GF)) ⊢ (REL e2 << e2' : lrel_tape) -∗
      REL Rand e1 e2 << Rand e1' e2' : lrel_nat := by
  unfold_rel
  iintro IH1 IH2 %K %j Hspec
  tp_bind j e2'
  ispecialize IH2 $$ %_ %j Hspec
  wp_apply wp_wand $$ IH2
  iintro %v2 ⟨%v2', Hspec, HA⟩
  tp_bind j e1'
  ispecialize IH1 $$ %_ %j Hspec
  wp_apply wp_wand $$ IH1
  iintro %v1 ⟨%v1', Hspec, HA'⟩
  dsimp only [lrel_nat, lrel_tape]
  icases HA' with ⟨%M, %h1, %h1'⟩
  subst h1 h1'
  icases HA with ⟨%α, %α', %N, %h2, %h2', #H⟩
  subst h2 h2'
  tp_normalise j
  iinv H with ⟨>Hα, >Hα'⟩ Hclose
  ihave Hα' := empty_to_spec_tapeN α' N $$ Hα'
  ihave Hα := empty_to_tapeN α N $$ Hα
  by_cases hNM : N = M
  · subst hNM
    wp_apply wp_couple_rand_lbl_rand_lbl N id Function.bijective_id (N : ℤ) K α α' j (by simp)
      (fun _ h => h) $$ [Hα Hα' Hspec] with %n ⟨Hα, Hα', Hspec, %hn⟩
    · isplitl [Hα]
      · inext; iexact Hα
      isplitl [Hα']
      · inext; iexact Hα'
      iexact Hspec
    ihave Hα' := spec_tapeN_to_empty α' N $$ Hα'
    ihave Hα := tapeN_to_empty α N $$ Hα
    imod Hclose $$ [Hα Hα']
    · inext
      iframe Hα Hα'
    imodintro
    iexists LitV (LitInt ((id n : ℕ) : ℤ))
    iframe Hspec
    iexists n
    ipureintro
    exact ⟨rfl, rfl⟩
  · wp_apply wp_couple_rand_lbl_rand_lbl_wrong M N id Function.bijective_id (M : ℤ) K α α' [] []
      j (by simp) (Ne.symm hNM) (fun _ h => h) $$ [Hα Hα' Hspec] with %n ⟨Hα, Hα', Hspec, %hn⟩
    · isplitl [Hα]
      · inext; iexact Hα
      isplitl [Hα']
      · inext; iexact Hα'
      iexact Hspec
    ihave Hα' := spec_tapeN_to_empty α' N $$ Hα'
    ihave Hα := tapeN_to_empty α N $$ Hα
    imod Hclose $$ [Hα Hα']
    · inext
      iframe Hα Hα'
    imodintro
    iexists LitV (LitInt ((id n : ℕ) : ℤ))
    iframe Hspec
    iexists n
    ipureintro
    exact ⟨rfl, rfl⟩

/-- Rocq: `refines_rand_unit`. -/
theorem refines_rand_unit (e e' : expr) :
    (REL e << e' : (lrel_nat : lrel GF)) ⊢
      REL Rand e (Val (LitV LitUnit)) << Rand e' (Val (LitV LitUnit)) : lrel_nat := by
  unfold_rel
  iintro H %K %j Hspec
  tp_bind j e'
  ispecialize H $$ %_ %j Hspec
  wp_apply wp_wand $$ H
  iintro %v ⟨%v', Hspec, HA⟩
  dsimp only [lrel_nat]
  icases HA with ⟨%M, %h1, %h2⟩
  subst h1 h2
  tp_normalise j
  wp_apply wp_couple_rand_rand M id Function.bijective_id j (M : ℤ) K (by simp) (fun _ h => h)
    $$ Hspec with %n ⟨%hn, Hspec⟩
  iexists LitV (LitInt ((id n : ℕ) : ℤ))
  iframe Hspec
  iexists n
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: `refines_xchg`. -/
theorem refines_xchg (e1 e2 e1' e2' : expr) (A : lrel GF) :
    (REL e1 << e1' : lrel_ref A) ⊢ (REL e2 << e2' : A) -∗
      REL Xchg e1 e2 << Xchg e1' e2' : A := by
  iintro IH1 IH2
  rel_bind_ap e2 e2' IH2 w w' IH2
  rel_bind_ap e1 e1' IH1 v v' IH1
  dsimp only [lrel_ref]
  icases IH1 with ⟨%l, %l', %h, %h', #Hinv⟩
  subst h h'
  have h : _ ⊢ REL Xchg (Val (LitV (LitLoc l))) (Val w) <<
      Xchg (Val (LitV (LitLoc l'))) (Val w') : A :=
    refines_atomic_l (⊤ \ ↑(logN.@ (l, l'))) [] (Xchg (Val (LitV (LitLoc l))) (Val w)) _ A
  iapply h
  iintro %K' %j Hspec
  iinv Hinv with ⟨%v, %v', Hv1, >Hv2, #Hv⟩ Hclose
  imodintro
  iapply wp_pupd
  wp_xchg
  tp_xchg j
  imodintro
  imod Hclose $$ [Hv1 Hv2 IH2]
  · inext
    iexists w, w'
    iframe Hv1 Hv2 IH2
  imodintro
  iexists Val v'
  iframe Hspec
  rel_values

/-- Rocq: `refines_cmpxchg_ref`. -/
theorem refines_cmpxchg_ref (A : lrel GF) (e1 e2 e3 e1' e2' e3' : expr) :
    (REL e1 << e1' : lrel_ref (lrel_ref A)) ⊢ (REL e2 << e2' : lrel_ref A) -∗
      (REL e3 << e3' : lrel_ref A) -∗
      REL CmpXchg e1 e2 e3 << CmpXchg e1' e2' e3' : lrel_prod (lrel_ref A) lrel_bool := by
  iintro IH1 IH2 IH3
  rel_bind_ap e3 e3' IH3 v3 v3' #IH3
  rel_bind_ap e2 e2' IH2 v2 v2' #IH2
  rel_bind_ap e1 e1' IH1 v1 v1' #IH1
  dsimp only [lrel_ref]
  icases IH1 with ⟨%l1, %l2, %h1, %h1', #Hinv⟩
  subst h1 h1'
  icases IH2 with ⟨%r1, %r2, %h2, %h2', #Hr⟩
  subst h2 h2'
  have h : _ ⊢ REL CmpXchg (Val (LitV (LitLoc l1))) (Val (LitV (LitLoc r1))) (Val v3) <<
      CmpXchg (Val (LitV (LitLoc l2))) (Val (LitV (LitLoc r2))) (Val v3') :
      lrel_prod (lrel_ref A) lrel_bool :=
    refines_atomic_l (⊤ \ ↑(logN.@ (l1, l2))) []
      (CmpXchg (Val (LitV (LitLoc l1))) (Val (LitV (LitLoc r1))) (Val v3)) _ _
  dsimp only [lrel_ref] at h
  iapply h
  iintro %K' %j Hspec
  iinv Hinv with ⟨%w1, %w2, Hl1, >Hl2, #Hv⟩ Hclose
  imodintro
  by_cases hs : w1 = LitV (LitLoc r1) ∧ w2 = LitV (LitLoc r2)
  · obtain ⟨rfl, rfl⟩ := hs
    iapply wp_pupd
    wp_cmpxchg_suc
    tp_cmpxchg_suc j
    imodintro
    imod Hclose $$ [Hl1 Hl2]
    · inext
      iexists v3, v3'
      iframe Hl1 Hl2 IH3
    imodintro
    iexists Val (PairV (LitV (LitLoc r2)) (LitV (LitBool true)))
    iframe Hspec
    rel_values
    imodintro
    dsimp only [lrel_prod, lrel_bool]
    iexists LitV (LitLoc r1), LitV (LitLoc r2), LitV (LitBool true), LitV (LitBool true)
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitl
    · iexists r1, r2
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; rfl
      iexact Hr
    · iexists true
      ipureintro; exact ⟨rfl, rfl⟩
  by_cases h1 : w1 = LitV (LitLoc r1)
  · -- impossible: the LHS locations agree but the RHS ones do not
    subst h1
    have h2 : w2 ≠ LitV (LitLoc r2) := fun h2 => hs ⟨rfl, h2⟩
    iapply wp_pupd
    wp_cmpxchg_suc
    icases Hv with ⟨%r1', %r2', %e1, %e2, #Hv⟩
    simp only [val.LitV.injEq, base_lit.LitLoc.injEq] at e1
    subst e1 e2
    have hr2 : r2' ≠ r2 := fun h => h2 (h ▸ rfl)
    imod compat_inv_clash (l1, l2) (r1, r2) (r1, r2') (l1 ↦ v3) _ _
      (fun h => hr2 (Prod.mk.inj h).2.symm)
      (fun h => by
        obtain ⟨rfl, -⟩ := Prod.mk.inj h
        iintro HR ⟨%a, %b, Ha, -⟩
        iapply compat_pointsto_excl $$ HR Ha)
      (fun h => by
        obtain ⟨rfl, -⟩ := Prod.mk.inj h
        iintro HR ⟨%a, %b, Ha, -⟩
        iapply compat_pointsto_excl $$ HR Ha)
      (by
        iintro ⟨%a, %b, Ha, -⟩ ⟨%c, %d, Hc, -⟩
        iapply compat_pointsto_excl $$ Ha Hc) $$ Hl1 Hr Hv with %hf
    exact hf.elim
  · iapply wp_pupd
    wp_cmpxchg_fail
    by_cases h2 : w2 = LitV (LitLoc r2)
    · -- impossible: the RHS locations agree but the LHS ones do not
      subst h2
      icases Hv with ⟨%r1', %r2', %e1, %e2, #Hv⟩
      simp only [val.LitV.injEq, base_lit.LitLoc.injEq] at e2
      subst e1 e2
      have hr1 : r1' ≠ r1 := fun h => h1 (h ▸ rfl)
      imod compat_inv_clash (l1, l2) (r1, r2) (r1', r2) (l2 ↦ₛ LitV (LitLoc r2)) _ _
        (fun h => hr1 (Prod.mk.inj h).1.symm)
        (fun h => by
          obtain ⟨-, rfl⟩ := Prod.mk.inj h
          iintro HR ⟨%a, %b, -, Hb, -⟩
          iapply compat_spec_pointsto_excl $$ HR Hb)
        (fun h => by
          obtain ⟨-, rfl⟩ := Prod.mk.inj h
          iintro HR ⟨%a, %b, -, Hb, -⟩
          iapply compat_spec_pointsto_excl $$ HR Hb)
        (by
          iintro ⟨%a, %b, -, Hb, -⟩ ⟨%c, %d, -, Hd, -⟩
          iapply compat_spec_pointsto_excl $$ Hb Hd) $$ Hl2 Hr Hv with %hf
      exact hf.elim
    · tp_cmpxchg_fail j
      imodintro
      imod Hclose $$ [Hl1 Hl2]
      · inext
        iexists w1, w2
        iframe Hl1 Hl2 Hv
      imodintro
      iexists Val (PairV w2 (LitV (LitBool false)))
      iframe Hspec
      rel_values
      imodintro
      dsimp only [lrel_prod, lrel_bool]
      iexists w1, w2, LitV (LitBool false), LitV (LitBool false)
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; rfl
      isplitl
      · iexact Hv
      · iexists false
        ipureintro; exact ⟨rfl, rfl⟩

end compatibility

end Foxtrot.BinaryRel
