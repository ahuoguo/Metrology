module

public import Metrology.Foxtrot.PrimitiveLaws
public import Metrology.Foxtrot.SpecProofMode
public import Iris.Instances.Lib.Invariants

/-!
# A binary logical relation for System F_mu_ref_fork with tapes (Foxtrot)

Ported from clutch/theories/foxtrot/binary_rel/binary_model.v

## Rocq → Lean map
Everything lives in namespace `Foxtrot.BinaryRel` (the unary relation of
`foxtrot/unary_rel` reuses the names `logN`, `lrel`, `refines`, ...).
* `logN`, `foxtrotRGS` (constructor `FoxtrotRGS`, field `foxtrotRGS_foxtrotGS`, an instance),
  `lrel` (constructor `LRel`, fields `lrel_car`, `lrel_persistent`; `lrel_car` is also a
  coercion to functions), `lrel_equiv`/`lrel_dist`/`lrel_ofe_mixin`/`lrelC` ↦ the `OFE`
  instance `lrel_ofe`, `lrel_cofe` ↦ the `IsCOFE` instance `lrel_cofe`, `lrel_inhabited`,
  `lrel_car_ne`, `refines_def`, `refines`, `refines_eq`, `refines_ne`, `refines_proper`,
  `lrel_unit`, `lrel_bool`, `lrel_nat`, `lrel_int`, `lrel_arr`, `lrel_ref`, `lrel_tape`,
  `lrel_prod`, `lrel_sum`, `lrel_rec1`, `lrel_rec1_contractive`, `lrel_rec`, `lrel_exists`,
  `lrel_forall`, `lrel_true`, `lrel_prod_ne`, `lrel_sum_ne`, `lrel_arr_ne`, `lrel_rec_ne`,
  `lrel_rec_unfold`, `interp_ref_funct`, `interp_ref_inj`, `interp_tape_funct`,
  `interp_tape_inj`, `fupd_refines`, `elim_fupd_refines`, `elim_bupd_logrel`, `refines_bind`,
  `refines_ret`, `unfold_rel` (a tactic macro).
* Notation `REL e1 << t : A` is `refines e1 t A` (scoped in `Foxtrot.BinaryRel`).

## Deviations
* Sealing is mimicked as for `pupd` (see `Metrology.Foxtrot.Pupd`): `refines_def` and
  `refines := refines_def`, with the `rfl` equation `refines_eq`. Downstream, Rocq's
  `rewrite refines_eq /refines_def` (the tactic `unfold_rel`) is `unfold refines refines_def`.
* iris-lean's OFEs are setoid-free (`≡` is `=`), so the Rocq `≡` statements
  (`refines_proper`, `lrel_rec_unfold`) are equalities, and the `Proper (dist n ==> ..)`
  instances are theorems/`NonExpansive` instances on `≡{n}≡`.
* `lrel_rec` takes `C : lrel GF -n> lrel GF` (Rocq: `lrelC Σ -n> lrelC Σ`).
* Rocq's `#n` for `n : nat` is `LitV (LitInt (n : ℤ))`, `(v1, v2)%V` is `PairV v1 v2`,
  the tape `(N; [])` is `(⟨N, []⟩ : tape)`, `#lbl:α` is `LitV (LitLbl α)`.
* The namespace `logN .@ (l1, l2)` needs `Pos.Countable (Loc × Loc)`: the local instance
  `pos_countable_loc_prod` (added helper).
* `IntoVal e v` hypotheses of `refines_ret` are instance-implicit.
* `elim_fupd_refines`/`elim_bupd_logrel` carry iris-lean's extra `InOut` parameter.

## Omitted
* The `lrel_scope` notations (`()`, `A1 → A2`, `A * B`, `A + B`, `ref A`, `∃ A, C`,
  `∀ A, C`): the constructors are used directly.
* `lrel_car_proper` (setoid plumbing, subsumed by `=`), `ectx_itemO` (Rocq canonical
  structure `leibnizO ectx_item`, not needed).
* Commented-out Rocq code (`na_ownP`, `na_invP`, `na_closeP`, the masked `fupd_refines` and
  `elim_fupd_refines`, `is_except_0_logrel`, `refines_ret_na`, `refines_ret_na'`).

## Added helpers
`pos_countable_loc_prod`, `lrel.ext`, `lrel.toFunChain`, `lrel.appAt`, `lrel.appAt_ne`,
`lrel_rec1Hom`, `fupd_of_inv_disj`.
* `pupd_refines` and the instance `elim_pupd_refines : ElimModal True p io false (pupd ⊤ ⊤ P) P
  (REL e << t : A) (REL e << t : A)` (not in Rocq, which has no such instance): with it the
  `tp_*` tactics of `Metrology.ConProbLang.Spec.SpecTactics` (found by `findUpd`) fire directly
  on `REL` goals, without first `unfold_rel` or `refines_step_r`. A test at the end of the file.
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

/-- Helper: countability of pairs of locations (for the namespaces `logN .@ (l1, l2)`). -/
instance pos_countable_loc_prod : Pos.Countable (Loc × Loc) where
  encode p := Pos.Countable.encode [p.1.loc_car, p.2.loc_car]
  decode q := (Pos.Countable.decode q : Option (List ℤ)).bind fun
    | [a, b] => some (⟨a⟩, ⟨b⟩)
    | _ => none
  decode_encode p := by
    obtain ⟨⟨a⟩, ⟨b⟩⟩ := p
    simp [Pos.Countable.decode_encode]

/-- Rocq: `logN`. -/
def logN : Namespace := nroot.@ "logN"

/-- Rocq: `foxtrotRGS`. -/
class foxtrotRGS (GF : BundledGFunctors) where
  FoxtrotRGS ::
  foxtrotRGS_foxtrotGS : foxtrotGS GF

attribute [reducible, instance] foxtrotRGS.foxtrotRGS_foxtrotGS

/-! ## Semantic interpretation of types -/

/-- Rocq: `lrel`. -/
structure lrel (GF : BundledGFunctors) where
  LRel ::
  lrel_car : val → val → IProp GF
  [lrel_persistent : ∀ v1 v2, Persistent (lrel_car v1 v2)]

attribute [instance] lrel.lrel_persistent

export lrel (LRel lrel_car)

instance {GF : BundledGFunctors} : CoeFun (lrel GF) (fun _ => val → val → IProp GF) :=
  ⟨lrel.lrel_car⟩

/-! ### The COFE structure on semantic types -/

section lrel_ofe

variable {GF : BundledGFunctors}

theorem lrel.ext {A B : lrel GF} (h : ∀ v1 v2, A v1 v2 = B v1 v2) : A = B := by
  obtain ⟨carA⟩ := A
  obtain ⟨carB⟩ := B
  have hcar : carA = carB := by funext v1 v2; exact h v1 v2
  subst hcar; rfl

/-- Rocq: `lrel_equiv`, `lrel_dist`, `lrel_ofe_mixin`, `lrelC`. -/
instance lrel_ofe : OFE (lrel GF) where
  Dist n A B := ∀ w1 w2, A w1 w2 ≡{n}≡ B w1 w2
  dist_eqv := {
    refl _ _ _ := dist_eqv.refl _
    symm h w1 w2 := dist_eqv.symm (h w1 w2)
    trans h1 h2 w1 w2 := dist_eqv.trans (h1 w1 w2) (h2 w1 w2)
  }
  eq_dist' {A B} := by
    refine ⟨fun h _ _ _ => h ▸ .rfl, fun h => ?_⟩
    exact lrel.ext fun w1 w2 => OFE.eq_dist.mpr fun _ => h _ _ _
  dist_lt hd hmn w1 w2 := OFE.dist_lt (hd w1 w2) hmn

/-- Helper: an `lrel` chain as a chain of functions. -/
def lrel.toFunChain (c : Chain (lrel GF)) : Chain (val → val → IProp GF) where
  chain k := (c.chain k).lrel_car
  cauchy h := (c.cauchy h : _)

/-- Helper: application at fixed arguments. -/
abbrev lrel.appAt (v1 v2 : val) : (val → val → IProp GF) → IProp GF := (· v1 v2)

instance lrel.appAt_ne (v1 v2 : val) : OFE.NonExpansive (lrel.appAt (GF := GF) v1 v2) :=
  ⟨fun _ _ _ h => h v1 v2⟩

/-- Rocq: `lrel_cofe`. -/
instance lrel_cofe : IsCOFE (lrel GF) where
  compl c :=
    { lrel_car := IsCOFE.compl (lrel.toFunChain c)
      lrel_persistent v1 v2 :=
        (limitPreserving_persistent (lrel.appAt v1 v2)).compl
          (lrel.toFunChain c) fun k => (c.chain k).lrel_persistent v1 v2 }
  conv_compl {_ c} v1 v2 := IsCOFE.conv_compl (c := lrel.toFunChain c) v1 v2

/-- Rocq: `lrel_inhabited`. -/
instance lrel_inhabited : Inhabited (lrel GF) := ⟨⟨fun _ _ => iprop(True)⟩⟩

/-- Rocq: `lrel_car_ne`. -/
instance lrel_car_ne (w1 w2 : val) : OFE.NonExpansive (fun A : lrel GF => A w1 w2) where
  ne {_ _ _} h := h w1 w2

end lrel_ofe

/-! ## The refinement judgement and the type constructors -/

section semtypes

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `refines_def`. -/
def refines_def (e e' : expr) (A : lrel GF) : IProp GF :=
  iprop(∀ (K : List ectx_item) (j : ℕ), j ⤇ fill K e' -∗
    WP e {{ v, ∃ v', j ⤇ fill K (Val v') ∗ A v v' }})

/-- Rocq: `refines` (sealed). -/
def refines (e e' : expr) (A : lrel GF) : IProp GF := refines_def e e' A

/-- Rocq: `refines_eq`. -/
theorem refines_eq : @refines GF _ = @refines_def GF _ := rfl

/-- Rocq: `refines_ne`. -/
theorem refines_ne {n : ℕ} (e e' : expr) {A B : lrel GF} (h : A ≡{n}≡ B) :
    refines e e' A ≡{n}≡ refines e e' B := by
  unfold refines refines_def
  refine forall_ne fun K => forall_ne fun j => wand_ne.ne .rfl ?_
  refine NonExpansive.ne (f := Wp.wp (PROP := IProp GF) (Expr := expr) Stuckness.NotStuck ⊤ e) ?_
  intro v
  exact exists_ne fun v' => sep_ne.ne .rfl (h v v')

/-- Rocq: `refines_proper`. -/
theorem refines_proper (e e' : expr) {A B : lrel GF} (h : A = B) :
    refines e e' A = refines e e' B := h ▸ rfl

/-- Rocq: `lrel_unit`. -/
def lrel_unit : lrel GF :=
  LRel (fun w1 w2 => iprop(⌜w1 = LitV LitUnit ∧ w2 = LitV LitUnit⌝))

/-- Rocq: `lrel_bool`. -/
def lrel_bool : lrel GF :=
  LRel (fun w1 w2 => iprop(∃ b : Bool, ⌜w1 = LitV (LitBool b) ∧ w2 = LitV (LitBool b)⌝))

/-- Rocq: `lrel_nat`. -/
def lrel_nat : lrel GF :=
  LRel (fun w1 w2 =>
    iprop(∃ n : ℕ, ⌜w1 = LitV (LitInt (n : ℤ)) ∧ w2 = LitV (LitInt (n : ℤ))⌝))

/-- Rocq: `lrel_int`. -/
def lrel_int : lrel GF :=
  LRel (fun w1 w2 => iprop(∃ n : ℤ, ⌜w1 = LitV (LitInt n) ∧ w2 = LitV (LitInt n)⌝))

/-- Rocq: `lrel_arr`. -/
def lrel_arr (A1 A2 : lrel GF) : lrel GF :=
  LRel (fun w1 w2 =>
    iprop(□ ∀ v1 v2, A1 v1 v2 -∗ refines (App (Val w1) (Val v1)) (App (Val w2) (Val v2)) A2))

/-- Rocq: `lrel_ref`. -/
def lrel_ref (A : lrel GF) : lrel GF :=
  LRel (fun w1 w2 =>
    iprop(∃ l1 l2 : Loc, ⌜w1 = LitV (LitLoc l1)⌝ ∧ ⌜w2 = LitV (LitLoc l2)⌝ ∧
      inv (logN.@ (l1, l2)) iprop(∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ₛ v2 ∗ A v1 v2)))

/-- Rocq: `lrel_tape`. Both tapes are empty and are sampled from the same distribution. -/
def lrel_tape : lrel GF :=
  LRel (fun w1 w2 =>
    iprop(∃ (α1 α2 : Loc) (N : ℕ), ⌜w1 = LitV (LitLbl α1)⌝ ∧ ⌜w2 = LitV (LitLbl α2)⌝ ∧
      inv (logN.@ (α1, α2)) iprop((α1 ↪ (⟨N, []⟩ : tape)) ∗ α2 ↪ₛ (⟨N, []⟩ : tape))))

/-- Rocq: `lrel_prod`. -/
def lrel_prod (A B : lrel GF) : lrel GF :=
  LRel (fun w1 w2 =>
    iprop(∃ v1 v2 v1' v2', ⌜w1 = PairV v1 v1'⌝ ∧ ⌜w2 = PairV v2 v2'⌝ ∧
      A v1 v2 ∗ B v1' v2'))

/-- Rocq: `lrel_sum`. -/
def lrel_sum (A B : lrel GF) : lrel GF :=
  LRel (fun w1 w2 =>
    iprop(∃ v1 v2, (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ A v1 v2) ∨
      (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ B v1 v2)))

/-- Rocq: `lrel_rec1`. -/
def lrel_rec1 (C : lrel GF -n> lrel GF) (r : lrel GF) : lrel GF :=
  LRel (fun w1 w2 => iprop(▷ C r w1 w2))

/-- Rocq: `lrel_rec1_contractive`. -/
instance lrel_rec1_contractive (C : lrel GF -n> lrel GF) : OFE.Contractive (lrel_rec1 C) where
  distLater_dist {n P Q} hPQ w1 w2 := by
    refine Contractive.distLater_dist (f := (Iris.BI.later : IProp GF → IProp GF)) ?_
    intro k hk
    exact C.ne.ne (show P ≡{k}≡ Q from hPQ k hk) w1 w2

/-- Helper: `lrel_rec1 C` as a contractive map. -/
def lrel_rec1Hom (C : lrel GF -n> lrel GF) : lrel GF -c> lrel GF where
  f := lrel_rec1 C

/-- Rocq: `lrel_rec`. -/
def lrel_rec (C : lrel GF -n> lrel GF) : lrel GF := fixpoint (lrel_rec1 C)

/-- Rocq: `lrel_exists`. -/
def lrel_exists (C : lrel GF → lrel GF) : lrel GF :=
  LRel (fun w1 w2 => iprop(∃ A, C A w1 w2))

/-- Rocq: `lrel_forall`. -/
def lrel_forall (C : lrel GF → lrel GF) : lrel GF :=
  LRel (fun w1 w2 => iprop(∀ A : lrel GF, lrel_arr lrel_unit (C A) w1 w2))

/-- Rocq: `lrel_true`. -/
def lrel_true : lrel GF := LRel (fun _ _ => iprop(True))

/-! ### The lrel constructors are non-expansive -/

/-- Rocq: `lrel_prod_ne`. -/
instance lrel_prod_ne : OFE.NonExpansive₂ (lrel_prod (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB w1 w2 := by
    dsimp only [lrel_prod]
    refine exists_ne fun v1 => exists_ne fun v2 => exists_ne fun v1' => exists_ne fun v2' => ?_
    exact and_ne.ne .rfl (and_ne.ne .rfl (sep_ne.ne (hA v1 v2) (hB v1' v2')))

/-- Rocq: `lrel_sum_ne`. -/
instance lrel_sum_ne : OFE.NonExpansive₂ (lrel_sum (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB w1 w2 := by
    dsimp only [lrel_sum]
    refine exists_ne fun v1 => exists_ne fun v2 => or_ne.ne ?_ ?_
    · exact and_ne.ne .rfl (and_ne.ne .rfl (hA v1 v2))
    · exact and_ne.ne .rfl (and_ne.ne .rfl (hB v1 v2))

/-- Rocq: `lrel_arr_ne`. -/
instance lrel_arr_ne : OFE.NonExpansive₂ (lrel_arr (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB w1 w2 := by
    dsimp only [lrel_arr]
    refine intuitionistically_ne.ne ?_
    refine forall_ne fun v1 => forall_ne fun v2 => ?_
    exact wand_ne.ne (hA v1 v2) (refines_ne _ _ hB)

omit [foxtrotRGS GF] in
/-- Rocq: `lrel_rec_ne`. -/
theorem lrel_rec_ne {n : ℕ} {C1 C2 : lrel GF -n> lrel GF} (hC : C1 ≡{n}≡ C2) :
    lrel_rec C1 ≡{n}≡ lrel_rec C2 := by
  unfold lrel_rec
  exact fixpoint_dist fun r w1 w2 =>
    OFE.NonExpansive.ne (f := (Iris.BI.later : IProp GF → IProp GF)) (hC r w1 w2)

omit [foxtrotRGS GF] in
/-- Rocq: `lrel_rec_unfold`. -/
theorem lrel_rec_unfold (C : lrel GF -n> lrel GF) :
    lrel_rec C = lrel_rec1 C (lrel_rec C) :=
  fixpoint_unfold (lrel_rec1Hom C)

end semtypes

/-! ## Properties of the semantic types -/

section semtypes_properties

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Helper: two invariants with incompatible contents in different sub-namespaces of `logN`
cannot both be opened. -/
theorem fupd_of_inv_disj {E : CoPset} {P1 P2 Q : IProp GF} {p1 p2 : Loc × Loc}
    (HE : (↑logN : CoPset) ⊆ E) (hne : p1 ≠ p2) (hfalse : ⊢ P1 -∗ P2 -∗ False) :
    ⊢ inv (logN.@ p1) P1 -∗ inv (logN.@ p2) P2 -∗ |={E}=> Q := by
  have hN_disj : logN.@ p1 ## logN.@ p2 := ndot_ne_disjoint _ hne
  have h1 : (↑(logN.@ p1) : CoPset) ⊆ E := LawfulSet.subset_trans (nclose_subseteq _ _) HE
  have h2 : (↑(logN.@ p2) : CoPset) ⊆ E := LawfulSet.subset_trans (nclose_subseteq _ _) HE
  have h2' : (↑(logN.@ p2) : CoPset) ⊆ E \ (↑(logN.@ p1) : CoPset) :=
    fun p hp => CoPset.in_diff.mpr ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
  iintro Hinv1 Hinv2
  imod inv_acc h1 $$ Hinv1 with ⟨HP1, -⟩
  imod inv_acc h2' $$ Hinv2 with ⟨HP2, -⟩
  ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
  · inext
    iapply hfalse $$ HP1 HP2
  imod HbotLater with %h
  exact h.elim

/-- Rocq: `interp_ref_funct`. The reference type relation is functional. -/
theorem interp_ref_funct (E : CoPset) (A : lrel GF) (l l1 l2 : Loc) (HE : (↑logN : CoPset) ⊆ E) :
    lrel_ref A (LitV (LitLoc l)) (LitV (LitLoc l1)) ∗
      lrel_ref A (LitV (LitLoc l)) (LitV (LitLoc l2)) ⊢ |={E}=> ⌜l1 = l2⌝ := by
  dsimp only [lrel_ref, lrel_tape]
  iintro ⟨Hl1, Hl2⟩
  icases Hl1 with ⟨%l', %l1', %Heq1, %Heq1', #Hinv1⟩
  icases Hl2 with ⟨%l'', %l2', %Heq2, %Heq2', #Hinv2⟩
  simp only [val.LitV.injEq, base_lit.LitLoc.injEq] at Heq1 Heq1' Heq2 Heq2'
  subst Heq1 Heq1' Heq2 Heq2'
  by_cases h : l1 = l2
  · imodintro; ipureintro; exact h
  · iapply fupd_of_inv_disj HE (p1 := (l, l1)) (p2 := (l, l2))
      (fun heq => h (Prod.mk.inj heq).2) (by
        iintro ⟨%wa1, %ws1, Hl1L, -⟩ ⟨%wa2, %ws2, Hl2L, -⟩
        ihave %Hne := ghost_map_elem_ne (H := locF) _ l l (DFrac.own 1) wa1 wa2 $$ Hl1L Hl2L
        exact (Hne rfl).elim) $$ Hinv1 Hinv2

/-- Rocq: `interp_ref_inj`. The reference type relation is injective. -/
theorem interp_ref_inj (E : CoPset) (A : lrel GF) (l l1 l2 : Loc) (HE : (↑logN : CoPset) ⊆ E) :
    lrel_ref A (LitV (LitLoc l1)) (LitV (LitLoc l)) ∗
      lrel_ref A (LitV (LitLoc l2)) (LitV (LitLoc l)) ⊢ |={E}=> ⌜l1 = l2⌝ := by
  dsimp only [lrel_ref, lrel_tape]
  iintro ⟨Hl1, Hl2⟩
  icases Hl1 with ⟨%l1', %l', %Heq1, %Heq1', #Hinv1⟩
  icases Hl2 with ⟨%l2', %l'', %Heq2, %Heq2', #Hinv2⟩
  simp only [val.LitV.injEq, base_lit.LitLoc.injEq] at Heq1 Heq1' Heq2 Heq2'
  subst Heq1 Heq1' Heq2 Heq2'
  by_cases h : l1 = l2
  · imodintro; ipureintro; exact h
  · iapply fupd_of_inv_disj HE (p1 := (l1, l)) (p2 := (l2, l))
      (fun heq => h (Prod.mk.inj heq).1) (by
        iintro ⟨%wa1, %ws1, -, Hl1L, -⟩ ⟨%wa2, %ws2, -, Hl2L, -⟩
        unfold spec_heap_frag
        let _ : GhostMapG GF Loc val locF := specG_con_prob_lang.specG_con_prob_lang_heap
        ihave %Hne := ghost_map_elem_ne (H := locF) _ l l (DFrac.own 1) ws1 ws2 $$ Hl1L Hl2L
        exact (Hne rfl).elim) $$ Hinv1 Hinv2

/-- Rocq: `interp_tape_funct`. -/
theorem interp_tape_funct (E : CoPset) (l l1 l2 : Loc) (HE : (↑logN : CoPset) ⊆ E) :
    lrel_tape (GF := GF) (LitV (LitLbl l)) (LitV (LitLbl l1)) ∗
      lrel_tape (LitV (LitLbl l)) (LitV (LitLbl l2)) ⊢ |={E}=> ⌜l1 = l2⌝ := by
  dsimp only [lrel_ref, lrel_tape]
  iintro ⟨Hl1, Hl2⟩
  icases Hl1 with ⟨%l', %l1', %n1, %Heq1, %Heq1', #Hinv1⟩
  icases Hl2 with ⟨%l'', %l2', %n2, %Heq2, %Heq2', #Hinv2⟩
  simp only [val.LitV.injEq, base_lit.LitLbl.injEq] at Heq1 Heq1' Heq2 Heq2'
  subst Heq1 Heq1' Heq2 Heq2'
  by_cases h : l1 = l2
  · imodintro; ipureintro; exact h
  · iapply fupd_of_inv_disj HE (p1 := (l, l1)) (p2 := (l, l2))
      (fun heq => h (Prod.mk.inj heq).2) (by
        iintro ⟨Hl1L, -⟩ ⟨Hl2L, -⟩
        ihave %Hne := ghost_map_elem_ne (H := locF) _ l l (DFrac.own 1) _ _ $$ Hl1L Hl2L
        exact (Hne rfl).elim) $$ Hinv1 Hinv2

/-- Rocq: `interp_tape_inj` (the unused argument `A` is kept). -/
theorem interp_tape_inj (E : CoPset) (_A : lrel GF) (l l1 l2 : Loc) (HE : (↑logN : CoPset) ⊆ E) :
    lrel_tape (GF := GF) (LitV (LitLbl l1)) (LitV (LitLbl l)) ∗
      lrel_tape (LitV (LitLbl l2)) (LitV (LitLbl l)) ⊢ |={E}=> ⌜l1 = l2⌝ := by
  dsimp only [lrel_ref, lrel_tape]
  iintro ⟨Hl1, Hl2⟩
  icases Hl1 with ⟨%l1', %l', %n1, %Heq1, %Heq1', #Hinv1⟩
  icases Hl2 with ⟨%l2', %l'', %n2, %Heq2, %Heq2', #Hinv2⟩
  simp only [val.LitV.injEq, base_lit.LitLbl.injEq] at Heq1 Heq1' Heq2 Heq2'
  subst Heq1 Heq1' Heq2 Heq2'
  by_cases h : l1 = l2
  · imodintro; ipureintro; exact h
  · iapply fupd_of_inv_disj HE (p1 := (l1, l)) (p2 := (l2, l))
      (fun heq => h (Prod.mk.inj heq).1) (by
        iintro ⟨-, Hl1L⟩ ⟨-, Hl2L⟩
        unfold spec_tapes_frag
        let _ : GhostMapG GF Loc tape locF := specG_con_prob_lang.specG_con_prob_lang_tapes
        ihave %Hne := ghost_map_elem_ne (H := locF) _ l l (DFrac.own 1) _ _ $$ Hl1L Hl2L
        exact (Hne rfl).elim) $$ Hinv1 Hinv2

end semtypes_properties

/-- Rocq: `REL e1 << t : A`. -/
scoped notation:100 "REL " e1:99 " << " t:99 " : " A:200 => refines e1 t A

/-- Rocq: `unfold_rel` (`rewrite refines_eq /refines_def`). -/
macro "unfold_rel" : tactic => `(tactic| unfold refines refines_def)

/-! ## Properties of the relational interpretation -/

section related_facts

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `fupd_refines`. -/
theorem fupd_refines (e t : expr) (A : lrel GF) :
    (|={⊤}=> refines e t A) ⊢ refines e t A := by
  unfold refines refines_def
  iintro H %K %j Hr
  imod H
  iapply H $$ Hr

/-- Rocq: `elim_fupd_refines`. -/
instance elim_fupd_refines {p : Bool} {io : InOut} (e t : expr) (P : IProp GF) (A : lrel GF) :
    ElimModal True p io false iprop(|={⊤}=> P) P (refines e t A) (refines e t A) where
  elim_modal _ := calc
    _ ⊢ (|={⊤}=> P) ∗ (P -∗ refines e t A) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |={⊤}=> P ∗ (P -∗ refines e t A) := fupd_frame_right
    _ ⊢ |={⊤}=> refines e t A := BIFUpdate.mono wand_elim_right
    _ ⊢ refines e t A := fupd_refines e t A

/-- Rocq: `elim_bupd_logrel`. -/
instance elim_bupd_logrel {p : Bool} {io : InOut} (e t : expr) (P : IProp GF) (A : lrel GF) :
    ElimModal True p io false iprop(|==> P) P (refines e t A) (refines e t A) where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_mono BIUpdateFUpdate.fupd_of_bupd)).trans
      ((elim_fupd_refines (p := p) (io := io) e t P A).elim_modal h)

/-- Added (not in Rocq): a `pupd ⊤ ⊤` modality can be eliminated in front of a refinement. -/
theorem pupd_refines (e t : expr) (A : lrel GF) :
    pupd ⊤ ⊤ (refines e t A) ⊢ refines e t A := by
  unfold refines refines_def
  iintro H %K %j Hr
  imod H
  iapply H $$ Hr

/-- Added (not in Rocq): eliminating `pupd ⊤ ⊤` into `REL`, so that the `tp_*` tactics
(through `findUpd`) fire directly on `REL` goals. -/
instance elim_pupd_refines {p : Bool} {io : InOut} (e t : expr) (P : IProp GF) (A : lrel GF) :
    ElimModal True p io false (pupd ⊤ ⊤ P) P (refines e t A) (refines e t A) where
  elim_modal _ := calc
    _ ⊢ pupd ⊤ ⊤ P ∗ (P -∗ refines e t A) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ pupd ⊤ ⊤ (refines e t A) := by
      iintro ⟨H1, H2⟩
      imod H1
      imodintro
      iapply H2 $$ H1
    _ ⊢ refines e t A := pupd_refines e t A

end related_facts

/-! ## The monadic layer -/

section monadic

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `refines_bind`. -/
theorem refines_bind (K K' : List ectx_item) (A A' : lrel GF) (e e' : expr) :
    (REL e << e' : A) ⊢
      (∀ v v', A v v' -∗ REL fill K (Val v) << fill K' (Val v') : A') -∗
      REL fill K e << fill K' e' : A' := by
  iintro Hm Hf
  unfold refines refines_def
  iintro %K'' %j Hjis
  rw [← fill_app']
  ispecialize Hm $$ %(K' ++ K'') %j Hjis
  iapply wp_bind (fill K)
  iapply wp_wand $$ Hm
  iintro %v ⟨%v', Hj, HA⟩
  rw [fill_app']
  ispecialize Hf $$ %v %v' HA
  iapply Hf $$ %K'' %j Hj

/-- Rocq: `refines_ret`. -/
theorem refines_ret (e1 e2 : expr) (v1 v2 : val) (A : lrel GF)
    [H1 : IntoVal (Λ := con_prob_lang) e1 v1] [H2 : IntoVal (Λ := con_prob_lang) e2 v2] :
    (|={⊤}=> A v1 v2) ⊢ REL e1 << e2 : A := by
  obtain rfl : Val v1 = e1 := H1.into_val
  obtain rfl : Val v2 = e2 := H2.into_val
  unfold refines refines_def
  iintro HFA %K %j HK
  imod HFA
  iapply wp_value'
  iexists v2
  iframe

end monadic

/-! ## Test (added): `tp_*` tactics on `REL` goals, through `elim_pupd_refines` -/

section tests

variable {GF : BundledGFunctors} [foxtrotRGS GF]

example (j : ℕ) (e t : expr) (A : lrel GF) :
    j ⤇ BinOp PlusOp (Val (LitV (LitInt 1))) (Val (LitV (LitInt 2))) ∗
      (j ⤇ Val (LitV (LitInt 3)) -∗ REL e << t : A) ⊢ REL e << t : A := by
  iintro ⟨Hj, H⟩
  tp_pures j
  iapply H $$ Hj

end tests

end Foxtrot.BinaryRel
