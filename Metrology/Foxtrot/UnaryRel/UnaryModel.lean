module

public import Metrology.Foxtrot.ProofMode
public import Iris.Instances.Lib.Invariants

/-!
# The unary logical relation of Foxtrot: semantic model

Ported from clutch/theories/foxtrot/unary_rel/unary_model.v

A unary logical relation for System F_mu_ref_fork with tapes (files mostly copied from the
binary_rel directory). As in Rocq, the ghost state is `foxtrotGS` directly (no separate
`foxtrotRGS` class). The "refinement" judgement `REL e : A` is simply `WP e {{ A }}`.

Everything lives in the namespace `Foxtrot.UnaryRel`, so that the names (`lrel`, `refines`,
`lrel_arr`, ...) do not clash with those of the binary relation (`binary_rel`), which the Rocq
development keeps in separate files that are never imported together.

## Rocq → Lean map
* `logN`, `lrel` (constructor `LRel`, fields `lrel_car`, `lrel_persistent`),
  `lrel_equiv` / `lrel_dist` / `lrel_ofe_mixin` / `lrelC` (merged into the `OFE` instance on
  `lrel GF`: its `Equiv` and `Dist` fields), `lrel_cofe` (the `IsCOFE` instance),
  `lrel_inhabited`, `lrel_car_ne`, `refines_aux` / `refines_def` / `refines` / `refines_eq`
  (the Rocq seal `refines_aux` is replaced by the pair of `def`s, see Deviations), `refines_ne`, `lrel_unit`,
  `lrel_bool`, `lrel_nat`, `lrel_int`, `lrel_arr`, `lrel_ref`, `lrel_tape`, `lrel_prod`,
  `lrel_sum`, `lrel_rec1`, `lrel_rec1_contractive`, `lrel_rec`, `lrel_exists`, `lrel_forall`,
  `lrel_true`, `lrel_prod_ne`, `lrel_sum_ne`, `lrel_arr_ne`, `lrel_rec_ne`, `lrel_rec_unfold`,
  `fupd_refines`, `elim_fupd_refines`, `elim_bupd_logrel`, `refines_bind`, `refines_ret`: same
  names.
* `lrel_car` is a coercion to functions (`CoeFun`), so `A v` is `A.lrel_car v`.
* Rocq notation `REL e : A` is the scoped notation `REL e : A` (namespace `Foxtrot.UnaryRel`).
* Rocq `Ltac unfold_rel` is the tactic macro `unfold_rel` (`unfold refines refines_def`).

## Deviations
* Sealing: as for `Foxtrot.pupd`, `refines_def` and `refines := refines_def` are two `def`s
  (so `refines` is opaque to instance search) and `refines_eq` is an `rfl` equation.
* `refines e A` is `WP e {{ v, A v }}`, i.e. `Wp.wp .NotStuck ⊤ e (fun v => A v)` (the Foxtrot
  WP ignores the stuckness).
* The OFE of `lrel` has Leibniz equality (iris-lean's OFEs identify `≡` with `=`); Rocq's
  `A ≡ B` statements (`lrel_rec_unfold`) are equalities.
* `lrel_rec_ne` is stated pointwise: `(∀ A, C A ≡{n}≡ C' A) → lrel_rec C ≡{n}≡ lrel_rec C'`.
  `lrel_prod_ne`, `lrel_sum_ne`, `lrel_arr_ne` are `NonExpansive₂` instances, `refines_ne` is a
  `NonExpansive (refines e)` instance and `lrel_car_ne` a theorem.
* `lrel_tape` uses the raw tape points-to `α ↪ ⟨N, []⟩` (Rocq: `α ↪ (N; [])`).
* `elim_fupd_refines`/`elim_bupd_logrel` carry iris-lean's `InOut` parameter.
* Values: Rocq `#()` is `LitV LitUnit`, `#b` is `LitV (LitBool b)`, `#n` is
  `LitV (LitInt n)`, `#l` is `LitV (LitLoc l)`, `#lbl:α` is `LitV (LitLbl α)`, `(v1, v2)%V` is
  `PairV v1 v2`, `App w v` is `App (Val w) (Val v)`.

## Omitted
* `lrel_car_proper`, `refines_proper` (setoid plumbing: `≡` is `=`).
* `ectx_itemO` (canonical discrete OFE on evaluation contexts; unused).
* The `lrel_scope` notations `()`, `A → B`, `A * B`, `A + B`, `ref A`, `∃ A, C`, `∀ A, C`:
  Lean cannot overload `→`/`∀`/`∃`; use `lrel_unit`, `lrel_arr`, `lrel_prod`, `lrel_sum`,
  `lrel_ref`, `lrel_exists`, `lrel_forall`.
* The commented-out Rocq code (`foxtrotRGS`, `na_ownP`, `interp_ref_funct`, ...,
  `refines_ret_na`, `is_except_0_logrel`).

## Added (not in Rocq)
* `loc_pos_countable : Pos.Countable Loc` (via `Loc.loc_car : ℤ`), needed for the namespaces
  `logN.@ l` (Rocq: `Countable loc`).
* `lrel.ext`, `refines_unfold` (the unfolding equation `refines e A = WP e {{ v, A v }}`).
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.UnaryRel

/-- Added: `Loc` is countable into `Pos` (for namespaces `N.@ l`). -/
instance loc_pos_countable : Pos.Countable Loc where
  encode l := Pos.Countable.encode l.loc_car
  decode p := (Pos.Countable.decode p : Option ℤ).map Loc.mk
  decode_encode l := by simp [Pos.Countable.decode_encode]

/-- Rocq: `logN`. -/
def logN : Namespace := nroot.@ "logN"

/-! ## Semantic interpretation of types -/

/-- Rocq: `lrel`. -/
structure lrel (GF : BundledGFunctors) where
  LRel ::
  lrel_car : val → IProp GF
  [lrel_persistent : ∀ v1, Persistent (lrel_car v1)]

attribute [instance] lrel.lrel_persistent

export lrel (LRel)

instance {GF : BundledGFunctors} : CoeFun (lrel GF) (fun _ => val → IProp GF) := ⟨lrel.lrel_car⟩

/-! ## The COFE structure on semantic types (Rocq: section `lrel_ofe`) -/

section lrel_ofe

variable {GF : BundledGFunctors}

/-- Added: extensionality for `lrel`. -/
theorem lrel.ext {A B : lrel GF} (h : ∀ v, A.lrel_car v = B.lrel_car v) : A = B := by
  obtain ⟨carA⟩ := A
  obtain ⟨carB⟩ := B
  have hcar : carA = carB := funext h
  subst hcar; rfl

/-- Rocq: `lrel_ofe_mixin` / `lrelC`. -/
instance lrel_ofe : OFE (lrel GF) where
  Dist n A B := ∀ w1, A.lrel_car w1 ≡{n}≡ B.lrel_car w1
  dist_eqv := {
    refl _ _ := dist_eqv.refl _
    symm h w1 := dist_eqv.symm (h w1)
    trans h1 h2 w1 := dist_eqv.trans (h1 w1) (h2 w1)
  }
  eq_dist' {A B} := by
    refine ⟨fun h _ _ => h ▸ .rfl, fun h => ?_⟩
    exact lrel.ext fun w1 => OFE.eq_dist.mpr fun n => h n w1
  dist_lt hd hmn w1 := OFE.dist_lt (hd w1) hmn

/-- Project an `lrel`-valued chain into the underlying function-space chain. -/
def lrel.toFunChain (c : Chain (lrel GF)) : Chain (val → IProp GF) where
  chain k := (c.chain k).lrel_car
  cauchy h := (c.cauchy h : _)

/-- Evaluation at a value, as a non-expansive map. -/
abbrev lrel.appAt (w : val) : (val → IProp GF) → IProp GF := (· w)

instance lrel.appAt_ne (w : val) : OFE.NonExpansive (lrel.appAt (GF := GF) w) :=
  ⟨fun _ _ _ h => h w⟩

/-- Rocq: `lrel_cofe`. -/
instance lrel_cofe : IsCOFE (lrel GF) where
  compl c :=
    { lrel_car := IsCOFE.compl (lrel.toFunChain c)
      lrel_persistent w1 :=
        (limitPreserving_persistent (lrel.appAt w1)).compl
          (lrel.toFunChain c) fun k => (c.chain k).lrel_persistent w1 }
  conv_compl {_ c} w1 := IsCOFE.conv_compl (c := lrel.toFunChain c) w1

/-- Rocq: `lrel_inhabited`. -/
instance lrel_inhabited : Inhabited (lrel GF) where
  default := { lrel_car := fun _ => iprop(True) }

/-- Rocq: `lrel_car_ne`. -/
theorem lrel_car_ne {n : ℕ} {A A' : lrel GF} (h : A ≡{n}≡ A') (w : val) :
    A w ≡{n}≡ A' w := h w

end lrel_ofe

/-! ## Semantic types (Rocq: section `semtypes`) -/

section semtypes

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `refines_def`. Technically this is NOT a refinement, but the name is kept to share
the lemma names with the binary relation. -/
def refines_def (e : expr) (A : lrel GF) : IProp GF :=
  WP e {{ v, A v }}

/-- Rocq: `refines` (sealed in Rocq). -/
def refines (e : expr) (A : lrel GF) : IProp GF := refines_def e A

/-- Rocq: `refines_eq`. -/
theorem refines_eq : @refines GF _ = @refines_def GF _ := rfl

/-- Added: the unfolding equation of `refines`. -/
theorem refines_unfold (e : expr) (A : lrel GF) : refines e A = WP e {{ v, A v }} := rfl

/-- Rocq: `refines_ne`. -/
instance refines_ne (e : expr) : NonExpansive (refines (GF := GF) e) where
  ne _ _ _ h := (wp_ne (s := .NotStuck) (E := ⊤) (e := e)).ne h

/-- Rocq: `lrel_unit`. -/
def lrel_unit : lrel GF := LRel (fun w1 => iprop(⌜w1 = LitV LitUnit⌝))

/-- Rocq: `lrel_bool`. -/
def lrel_bool : lrel GF := LRel (fun w1 => iprop(∃ b : Bool, ⌜w1 = LitV (LitBool b)⌝))

/-- Rocq: `lrel_nat`. -/
def lrel_nat : lrel GF := LRel (fun w1 => iprop(∃ n : ℕ, ⌜w1 = LitV (LitInt (n : ℤ))⌝))

/-- Rocq: `lrel_int`. -/
def lrel_int : lrel GF := LRel (fun w1 => iprop(∃ n : ℤ, ⌜w1 = LitV (LitInt n)⌝))

/-- Rocq: `lrel_arr`. -/
def lrel_arr (A1 A2 : lrel GF) : lrel GF := LRel (fun w1 =>
  iprop(□ ∀ v1, A1 v1 -∗ refines (App (Val w1) (Val v1)) A2))

/-- Rocq: `lrel_ref`. -/
def lrel_ref (A : lrel GF) : lrel GF := LRel (fun w1 =>
  iprop(∃ l1 : Loc, ⌜w1 = LitV (LitLoc l1)⌝ ∧
    Iris.inv (logN.@ l1) iprop(∃ v1, l1 ↦ v1 ∗ A v1)))

/-- Rocq: `lrel_tape`. Both tapes are empty and are sampled from the same distribution. -/
def lrel_tape : lrel GF := LRel (fun w1 =>
  iprop(∃ (α1 : Loc) (N : ℕ), ⌜w1 = LitV (LitLbl α1)⌝ ∧
    Iris.inv (logN.@ α1) iprop(α1 ↪ (⟨N, []⟩ : tape))))

/-- Rocq: `lrel_prod`. -/
def lrel_prod (A B : lrel GF) : lrel GF := LRel (fun w1 =>
  iprop(∃ v1 v1', ⌜w1 = PairV v1 v1'⌝ ∧ A v1 ∗ B v1'))

/-- Rocq: `lrel_sum`. -/
def lrel_sum (A B : lrel GF) : lrel GF := LRel (fun w1 =>
  iprop(∃ v1, (⌜w1 = InjLV v1⌝ ∧ A v1) ∨ (⌜w1 = InjRV v1⌝ ∧ B v1)))

/-- Rocq: `lrel_rec1`. -/
def lrel_rec1 (C : lrel GF -n> lrel GF) (rec' : lrel GF) : lrel GF :=
  LRel (fun w1 => iprop(▷ C rec' w1))

/-- Rocq: `lrel_rec1_contractive`. -/
instance lrel_rec1_contractive (C : lrel GF -n> lrel GF) : Contractive (lrel_rec1 C) where
  distLater_dist {n P Q} hPQ w1 := by
    refine Contractive.distLater_dist (f := (Iris.BI.later : IProp GF → IProp GF)) ?_
    intro k hk
    exact C.ne.ne (show P ≡{k}≡ Q from hPQ k hk) w1

/-- Rocq: `lrel_rec`. -/
def lrel_rec (C : lrel GF -n> lrel GF) : lrel GF := fixpoint (lrel_rec1 C)

/-- Rocq: `lrel_exists`. -/
def lrel_exists (C : lrel GF → lrel GF) : lrel GF := LRel (fun w1 =>
  iprop(∃ A, C A w1))

/-- Rocq: `lrel_forall`. -/
def lrel_forall (C : lrel GF → lrel GF) : lrel GF := LRel (fun w1 =>
  iprop(∀ A : lrel GF, lrel_arr lrel_unit (C A) w1))

/-- Rocq: `lrel_true`. -/
def lrel_true : lrel GF := LRel (fun _ => iprop(True))

/-! ### The lrel constructors are non-expansive -/

/-- Rocq: `lrel_prod_ne`. -/
instance lrel_prod_ne : OFE.NonExpansive₂ (lrel_prod (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB w1 := by
    dsimp only [lrel_prod]
    exact exists_ne fun v1 => exists_ne fun v1' => and_ne.ne .rfl (sep_ne.ne (hA v1) (hB v1'))

/-- Rocq: `lrel_sum_ne`. -/
instance lrel_sum_ne : OFE.NonExpansive₂ (lrel_sum (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB w1 := by
    dsimp only [lrel_sum]
    exact exists_ne fun v1 => or_ne.ne (and_ne.ne .rfl (hA v1)) (and_ne.ne .rfl (hB v1))

/-- Rocq: `lrel_arr_ne`. -/
instance lrel_arr_ne : OFE.NonExpansive₂ (lrel_arr (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB w1 := by
    dsimp only [lrel_arr]
    exact intuitionistically_ne.ne <| forall_ne fun v1 =>
      wand_ne.ne (hA v1) ((refines_ne _).ne hB)

omit [foxtrotGS GF] in
/-- Rocq: `lrel_rec_ne`. -/
theorem lrel_rec_ne {n : ℕ} {C C' : lrel GF -n> lrel GF} (hC : ∀ A, C A ≡{n}≡ C' A) :
    lrel_rec C ≡{n}≡ lrel_rec C' := by
  unfold lrel_rec
  exact fixpoint_dist fun r w1 =>
    OFE.NonExpansive.ne (f := (Iris.BI.later : IProp GF → IProp GF)) (hC r w1)

omit [foxtrotGS GF] in
/-- Rocq: `lrel_rec_unfold`. -/
theorem lrel_rec_unfold (C : lrel GF -n> lrel GF) : lrel_rec C = lrel_rec1 C (lrel_rec C) :=
  fixpoint_unfold (lrel_rec1 C).toContractiveHom

end semtypes

/-- Rocq: notation `REL e : A`. -/
scoped notation:100 "REL " e " : " A => refines e A

/-! ## Properties of the relational interpretation (Rocq: section `related_facts`) -/

section related_facts

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `fupd_refines`. -/
theorem fupd_refines (e : expr) (A : lrel GF) : (|={⊤}=> refines e A) ⊢ refines e A :=
  fupd_wp

/-- Rocq: `elim_fupd_refines`. -/
instance elim_fupd_refines {p : Bool} {io : InOut} (e : expr) (P : IProp GF) (A : lrel GF) :
    ElimModal True p io false iprop(|={⊤}=> P) P (refines e A) (refines e A) where
  elim_modal := (elim_modal_fupd_wp (p := p) (io := io) (P := P) (s := .NotStuck) (E := ⊤)
    (e := e) (Φ := fun v => A v)).elim_modal

/-- Rocq: `elim_bupd_logrel`. -/
instance elim_bupd_logrel {p : Bool} {io : InOut} (e : expr) (P : IProp GF) (A : lrel GF) :
    ElimModal True p io false iprop(|==> P) P (refines e A) (refines e A) where
  elim_modal := (elim_modal_bupd_wp (p := p) (io := io) (P := P) (s := .NotStuck) (E := ⊤)
    (e := e) (Φ := fun v => A v)).elim_modal

end related_facts

/-! ## Monadic rules (Rocq: section `monadic`) -/

section monadic

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `refines_bind`. -/
theorem refines_bind (K : List ectx_item) (A A' : lrel GF) (e : expr) :
    (REL e : A) ⊢ (∀ v, A v -∗ REL fill K (Val v) : A') -∗ REL fill K e : A' := by
  unfold refines refines_def
  iintro Hm Hf
  iapply wp_bind (fill K)
  iapply wp_wand $$ Hm
  iexact Hf

/-- Rocq: `refines_ret`. -/
theorem refines_ret (e1 : expr) (v1 : val) (A : lrel GF)
    [IntoVal (Λ := con_prob_lang) e1 v1] :
    (|={⊤}=> A v1) ⊢ REL e1 : A :=
  wp_value_fupd

end monadic

/-- Rocq: `unfold_rel`. -/
macro "unfold_rel" : tactic => `(tactic| unfold refines refines_def)

end Foxtrot.UnaryRel
