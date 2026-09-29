module

public import Metrology.Foxtrot.BinaryRel.BinaryModel

/-!
# Core relational rules of Foxtrot's binary logical relation

Ported from clutch/theories/foxtrot/binary_rel/binary_app_rel_rules.v

## Rocq → Lean map
All Rocq names are kept (namespace `Foxtrot.BinaryRel`): `refines_pure_l`, `refines_masked_l`,
`refines_wp_l`, `refines_pure_r`, `refines_atomic_l`, `pupd_fupd'`, `refines_step_r`,
`refines_arrow_val`, `refines_arrow`, `refines_wand`, `refines_alloc_l`,
`refines_alloctape_l`, `refines_alloc_r`, `refines_alloctape_r`, `refines_fork`,
`refines_xchg_l`, `refines_cmpxchg_l`, `refines_faa_l`, `refines_xchg_r`,
`refines_cmpxchg_fail_r`, `refines_cmpxchg_suc_r`, `refines_faa_r`.

## Deviations
* `PureExec ϕ n e e'` and `IntoVal e v` are instance-implicit, `Atomic StronglyAtomic e1` too;
  `ϕ` is passed as an explicit proof `Hϕ`. `TCEq N (Z.to_nat z)` is `hN : N = z.toNat`.
* Rocq's `Local Existing Instance pure_exec_fill` is replaced by explicit uses of
  `pure_exec_ctx (fill K')`.
* `pupd_fupd'` is the same statement as `Foxtrot.pupd_fupd'` (Rocq re-proves it in this
  section); here it is `Foxtrot.BinaryRel.pupd_fupd'`, proved by `Foxtrot.pupd_fupd'`.
* Rocq's `#b`, `#l`, `#lbl:α`, `(v, #b)%V` are `LitV (LitBool b)`, `LitV (LitLoc l)`,
  `LitV (LitLbl α)`, `PairV v (LitV (LitBool b))`; `ref e` is `Alloc e`, `alloc #z` is
  `alloc (Val (LitV (LitInt z)))`, `Xchg #l e`/`CmpXchg #l e1 e2`/`FAA #l e2` take
  `Val (LitV (LitLoc l))`.
* Proofs on the RHS use the `tp_*` tactics of `Metrology.ConProbLang.Spec.SpecTactics`
  (instantiated for `pupd` in `Metrology.Foxtrot.SpecProofMode`), after merging the two
  evaluation contexts `fill k (fill K e)` into `fill (K ++ k) e` (Rocq: implicit, by
  `fill_app`). `refines_pure_r` uses `pupd_step_pure` directly (the redex is abstract).

## Omitted
* The commented-out Rocq proofs (atomic variants of the LHS heap rules).
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

section rules

variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-! ## Primitive rules -/

/-! ### Forward reductions on the LHS -/

/-- Rocq: `refines_pure_l`. -/
theorem refines_pure_l (n : ℕ) (K' : List ectx_item) (e e' t : expr) (A : lrel GF) (ϕ : Prop)
    [Hpure : PureExec (Λ := con_prob_lang) ϕ n e e'] (Hϕ : ϕ) :
    ▷^[n] (REL fill K' e' << t : A) ⊢ REL fill K' e << t : A := by
  have HpureK := pure_exec_ctx (Λ := con_prob_lang) (fill K') ϕ n e e' Hpure
  unfold refines refines_def
  iintro IH %K %j Hs
  iapply wp_pure_step_later (Hexec := HpureK) Hϕ
  inext
  iapply IH $$ %K %j Hs

/-- Rocq: `refines_masked_l`. -/
theorem refines_masked_l (n : ℕ) (K' : List ectx_item) (e e' t : expr) (A : lrel GF) (ϕ : Prop)
    [Hpure : PureExec (Λ := con_prob_lang) ϕ n e e'] (Hϕ : ϕ) :
    (REL fill K' e' << t : A) ⊢ REL fill K' e << t : A := by
  iintro IH
  iapply refines_pure_l n K' e e' t A ϕ Hϕ
  inext
  iexact IH

/-- Rocq: `refines_wp_l`. -/
theorem refines_wp_l (K : List ectx_item) (e1 t : expr) (A : lrel GF) :
    WP e1 {{ v, REL fill K (Val v) << t : A }} ⊢ REL fill K e1 << t : A := by
  unfold refines refines_def
  iintro He %K' %j Hs
  iapply wp_bind (fill K)
  iapply wp_wand $$ He
  iintro %v Hv
  iapply Hv $$ %K' %j Hs

/-- Rocq: `refines_pure_r`. -/
theorem refines_pure_r (K' : List ectx_item) (e e' t : expr) (A : lrel GF) (n : ℕ) (ϕ : Prop)
    [Hpure : PureExec (Λ := con_prob_lang) ϕ n e e'] (Hϕ : ϕ) :
    (REL t << fill K' e' : A) ⊢ REL t << fill K' e : A := by
  have HpureK := pure_exec_ctx (Λ := con_prob_lang) (fill K') ϕ n e e' Hpure
  unfold refines refines_def
  iintro Hlog %K %j Hj
  imod pupd_step_pure (H2 := HpureK) ϕ n (fill K' e) (fill K' e') j K ⊤ Hϕ $$ Hj with Hj
  iapply Hlog $$ %K %j Hj

/-- Rocq: `refines_atomic_l`. -/
theorem refines_atomic_l (E : CoPset) (K : List ectx_item) (e1 t : expr) (A : lrel GF)
    [Hatomic : Atomic (Λ := con_prob_lang) StronglyAtomic e1] :
    (∀ K' j, j ⤇ fill K' t ={⊤, E}=∗
      WP e1 @ E {{ v, |={E, ⊤}=> ∃ t', j ⤇ fill K' t' ∗ REL fill K (Val v) << t' : A }})
      ⊢ REL fill K e1 << t : A := by
  unfold refines refines_def
  iintro Hlog %K' %j Hs
  iapply wp_bind (fill K)
  iapply wp_atomic
  imod Hlog $$ %K' %j Hs with He
  imodintro
  iapply wp_wand $$ He
  iintro %v Hlog
  imod Hlog with ⟨%t', Hr, Hlog⟩
  imodintro
  iapply Hlog $$ %K' %j Hr

/-- Rocq: `pupd_fupd'` (re-proved in the Rocq section; see `Foxtrot.pupd_fupd'`). -/
theorem pupd_fupd' (E1 E2 : CoPset) (P : IProp GF) (h : E2 ⊆ E1) :
    pupd E1 E1 P ⊢ pupd E1 E2 iprop(|={E2, E1}=> P) :=
  Foxtrot.pupd_fupd' E1 E2 P h

/-- Rocq: `refines_step_r`. -/
theorem refines_step_r (K' : List ectx_item) (e1 e2 : expr) (A : lrel GF) :
    (∀ k j, j ⤇ fill k e2 -∗
      pupd ⊤ ⊤ iprop(∃ v, j ⤇ fill k (Val v) ∗ REL e1 << fill K' (Val v) : A))
      ⊢ REL e1 << fill K' e2 : A := by
  iintro He
  unfold refines refines_def
  iintro %K %j Hs
  isimp only [← fill_app'] at Hs
  imod He $$ %(K' ++ K) %j Hs with ⟨%v, Hs, He⟩
  isimp only [fill_app'] at Hs
  iapply He $$ %K %j Hs

/-- Rocq: `refines_arrow_val`. This rule is useful for proving that functions refine each
other. -/
theorem refines_arrow_val (v v' : val) (A A' : lrel GF) :
    □ (∀ v1 v2, A v1 v2 -∗ REL App (Val v) (Val v1) << App (Val v') (Val v2) : A')
      ⊢ REL Val v << Val v' : lrel_arr A A' := by
  iintro #H
  iapply refines_ret (Val v) (Val v') v v'
  imodintro
  dsimp only [lrel_arr]
  imodintro
  iintro %v1 %v2 HA
  iapply H $$ HA

/-- Rocq: `refines_arrow`. -/
theorem refines_arrow (v v' : val) (A A' : lrel GF) :
    □ (∀ v1 v2, □ (REL Val v1 << Val v2 : A) -∗
      REL App (Val v) (Val v1) << App (Val v') (Val v2) : A')
      ⊢ REL Val v << Val v' : lrel_arr A A' := by
  iintro #H
  iapply refines_arrow_val
  imodintro
  iintro %v1 %v2 #HA
  iapply H
  imodintro
  iapply refines_ret (Val v1) (Val v2) v1 v2
  imodintro
  iexact HA

/-- Rocq: `refines_wand`. -/
theorem refines_wand (e1 e2 : expr) (A A' : lrel GF) :
    (REL e1 << e2 : A) ⊢ (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗ REL e1 << e2 : A' := by
  iintro He HAA
  have h : (REL e1 << e2 : A) ⊢
      (∀ v v', A v v' -∗ REL Val v << Val v' : A') -∗ REL e1 << e2 : A' :=
    refines_bind [] [] A A' e1 e2
  iapply h $$ He
  iintro %v %v' HA
  iapply refines_ret (Val v) (Val v') v v'
  iapply HAA $$ HA

/-! ### Stateful reductions on the LHS -/

/-- Rocq: `refines_alloc_l`. -/
theorem refines_alloc_l (K : List ectx_item) (e : expr) (v : val) (t : expr) (A : lrel GF)
    [Hv : IntoVal (Λ := con_prob_lang) e v] :
    ▷ (∀ l : Loc, l ↦ v -∗ REL fill K (Val (LitV (LitLoc l))) << t : A)
      ⊢ REL fill K (Alloc e) << t : A := by
  obtain rfl : Val v = e := Hv.into_val
  iintro Hlog
  iapply refines_wp_l
  wp_alloc l as Hl
  iapply Hlog $$ Hl

/-- Rocq: `refines_alloctape_l`. -/
theorem refines_alloctape_l (K : List ectx_item) (N : ℕ) (z : ℤ) (t : expr) (A : lrel GF)
    (hN : N = z.toNat) :
    ▷ (∀ α : Loc, α ↪N (N; []) -∗ REL fill K (Val (LitV (LitLbl α))) << t : A)
      ⊢ REL fill K (alloc (Val (LitV (LitInt z)))) << t : A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloc_tape N z hN $$ %(fun w => iprop(REL fill K (Val w) << t : A)) [] Hlog
  ipureintro
  trivial

/-! ### Stateful reductions on the RHS -/

/-- Rocq: `refines_alloc_r`. -/
theorem refines_alloc_r (K : List ectx_item) (e : expr) (v : val) (t : expr) (A : lrel GF)
    [Hv : IntoVal (Λ := con_prob_lang) e v] :
    (∀ l : Loc, l ↦ₛ v -∗ REL t << fill K (Val (LitV (LitLoc l))) : A)
      ⊢ REL t << fill K (Alloc e) : A := by
  obtain rfl : Val v = e := Hv.into_val
  iintro Hlog
  iapply refines_step_r
  iintro %k %j HK'
  tp_alloc j as l Hl
  imodintro
  iexists LitV (LitLoc l)
  iframe HK'
  iapply Hlog $$ Hl

/-- Rocq: `refines_alloctape_r`. -/
theorem refines_alloctape_r (K : List ectx_item) (N : ℕ) (z : ℤ) (t : expr) (A : lrel GF)
    (hN : N = z.toNat) :
    (∀ α : Loc, α ↪ₛN (N; []) -∗ REL t << fill K (Val (LitV (LitLbl α))) : A)
      ⊢ REL t << fill K (alloc (Val (LitV (LitInt z)))) : A := by
  subst hN
  iintro Hlog
  iapply refines_step_r
  iintro %K' %j HK'
  tp_allocnattape j α as Hα
  imodintro
  iexists LitV (LitLbl α)
  iframe HK'
  iapply Hlog $$ Hα

/-- Rocq: `refines_fork`. -/
theorem refines_fork (e e' : expr) :
    (REL e << e' : lrel_unit (GF := GF)) ⊢ REL Fork e << Fork e' : lrel_unit := by
  unfold refines refines_def
  iintro H %K %j Hs
  tp_fork j as k' Hk'
  ispecialize H $$ %([] : List ectx_item) %k'
  ihave Hk' := (show k' ⤇ e' ⊢@{IProp GF} k' ⤇ fill [] e' from .rfl) $$ Hk'
  ispecialize H $$ Hk'
  iapply wp_fork $$ [H] [Hs]
  · inext
    iapply wp_wand $$ H
    iintro %v -
    ipureintro
    trivial
  · inext
    iexists LitV LitUnit
    iframe Hs
    dsimp only [lrel_unit]
    ipureintro
    exact ⟨rfl, rfl⟩

/-- Rocq: `refines_xchg_l`. -/
theorem refines_xchg_l (K : List ectx_item) (l : Loc) (e : expr) (v' : val) (t : expr)
    (A : lrel GF) [Hv : IntoVal (Λ := con_prob_lang) e v'] :
    (∃ v, ▷ l ↦ v ∗ ▷ (l ↦ v' -∗ REL fill K (Val v) << t : A))
      ⊢ REL fill K (Xchg (Val (LitV (LitLoc l))) e) << t : A := by
  obtain rfl : Val v' = e := Hv.into_val
  iintro Hlog
  iapply refines_wp_l
  icases Hlog with ⟨%v, Hl, Hlog⟩
  iapply wp_xchg v v' l $$ %(fun w => iprop(REL fill K (Val w) << t : A)) Hl Hlog

/-- Rocq: `refines_cmpxchg_l`. -/
theorem refines_cmpxchg_l (K : List ectx_item) (l : Loc) (e1 e2 : expr) (v1 v2 : val)
    (t : expr) (A : lrel GF) [H1 : IntoVal (Λ := con_prob_lang) e1 v1]
    [H2 : IntoVal (Λ := con_prob_lang) e2 v2] (Hub : val_is_unboxed v1) :
    (∃ v', ▷ l ↦ v' ∗
      ((⌜v' ≠ v1⌝ -∗ ▷ (l ↦ v' -∗ REL fill K (Val (PairV v' (LitV (LitBool false)))) << t : A)) ∧
       (⌜v' = v1⌝ -∗ ▷ (l ↦ v2 -∗ REL fill K (Val (PairV v' (LitV (LitBool true)))) << t : A))))
      ⊢ REL fill K (CmpXchg (Val (LitV (LitLoc l))) e1 e2) << t : A := by
  obtain rfl : Val v1 = e1 := H1.into_val
  obtain rfl : Val v2 = e2 := H2.into_val
  iintro Hlog
  iapply refines_wp_l
  icases Hlog with ⟨%v', Hl, Hlog⟩
  by_cases heq : v' = v1
  · -- CmpXchg successful
    subst heq
    icases Hlog with ⟨-, Hlog⟩
    ispecialize Hlog $$ %rfl
    iapply wp_cmpxchg_suc v' v' v2 l (Or.inr Hub) rfl $$ %(fun w => iprop(REL fill K (Val w) << t : A)) Hl Hlog
  · -- CmpXchg failed
    icases Hlog with ⟨Hlog, -⟩
    ispecialize Hlog $$ %heq
    iapply wp_cmpxchg_fail v' v1 v2 l (DFrac.own 1) (Or.inr Hub) heq $$ %(fun w => iprop(REL fill K (Val w) << t : A)) Hl Hlog

/-- Rocq: `refines_faa_l`. -/
theorem refines_faa_l (K : List ectx_item) (l : Loc) (e2 : expr) (i2 : ℤ) (t : expr)
    (A : lrel GF) [H2 : IntoVal (Λ := con_prob_lang) e2 (LitV (LitInt i2))] :
    (∃ i1 : ℤ, ▷ l ↦ LitV (LitInt i1) ∗
      ▷ (l ↦ LitV (LitInt (i1 + i2)) -∗ REL fill K (Val (LitV (LitInt i1))) << t : A))
      ⊢ REL fill K (FAA (Val (LitV (LitLoc l))) e2) << t : A := by
  obtain rfl : Val (LitV (LitInt i2)) = e2 := H2.into_val
  iintro Hlog
  iapply refines_wp_l
  icases Hlog with ⟨%i1, Hl, Hlog⟩
  iapply wp_faa i1 i2 l $$ %(fun w => iprop(REL fill K (Val w) << t : A)) Hl Hlog

/-- Rocq: `refines_xchg_r`. -/
theorem refines_xchg_r (K : List ectx_item) (l : Loc) (e1 : expr) (v1 v : val) (t : expr)
    (A : lrel GF) [H1 : IntoVal (Λ := con_prob_lang) e1 v1] :
    l ↦ₛ v ⊢ (l ↦ₛ v1 -∗ REL t << fill K (Val v) : A) -∗
      REL t << fill K (Xchg (Val (LitV (LitLoc l))) e1) : A := by
  obtain rfl : Val v1 = e1 := H1.into_val
  iintro Hl Hlog
  iapply refines_step_r
  iintro %k %j Hk
  tp_xchg j
  iexists v
  imodintro
  iframe Hk
  iapply Hlog $$ Hl

/-- Rocq: `refines_cmpxchg_fail_r`. -/
theorem refines_cmpxchg_fail_r (K : List ectx_item) (l : Loc) (e1 e2 : expr) (v1 v2 v : val)
    (t : expr) (A : lrel GF) [H1 : IntoVal (Λ := con_prob_lang) e1 v1]
    [H2 : IntoVal (Λ := con_prob_lang) e2 v2] (Hsafe : vals_compare_safe v v1) (Hne : v ≠ v1) :
    l ↦ₛ v ⊢ (l ↦ₛ v -∗ REL t << fill K (Val (PairV v (LitV (LitBool false)))) : A) -∗
      REL t << fill K (CmpXchg (Val (LitV (LitLoc l))) e1 e2) : A := by
  obtain rfl : Val v1 = e1 := H1.into_val
  obtain rfl : Val v2 = e2 := H2.into_val
  iintro Hl Hlog
  iapply refines_step_r
  iintro %k %j Hk
  tp_cmpxchg_fail j
  imodintro
  iexists _
  iframe Hk
  iapply Hlog $$ Hl

/-- Rocq: `refines_cmpxchg_suc_r`. -/
theorem refines_cmpxchg_suc_r (K : List ectx_item) (l : Loc) (e1 e2 : expr) (v1 v2 v : val)
    (t : expr) (A : lrel GF) [H1 : IntoVal (Λ := con_prob_lang) e1 v1]
    [H2 : IntoVal (Λ := con_prob_lang) e2 v2] (Hsafe : vals_compare_safe v v1) (Heq : v = v1) :
    l ↦ₛ v ⊢ (l ↦ₛ v2 -∗ REL t << fill K (Val (PairV v (LitV (LitBool true)))) : A) -∗
      REL t << fill K (CmpXchg (Val (LitV (LitLoc l))) e1 e2) : A := by
  obtain rfl : Val v1 = e1 := H1.into_val
  obtain rfl : Val v2 = e2 := H2.into_val
  subst Heq
  iintro Hl Hlog
  iapply refines_step_r
  iintro %k %j Hk
  tp_cmpxchg_suc j
  imodintro
  iexists _
  iframe Hk
  iapply Hlog $$ Hl

/-- Rocq: `refines_faa_r`. -/
theorem refines_faa_r (K : List ectx_item) (l : Loc) (e2 : expr) (i1 i2 : ℤ) (t : expr)
    (A : lrel GF) [H2 : IntoVal (Λ := con_prob_lang) e2 (LitV (LitInt i2))] :
    l ↦ₛ LitV (LitInt i1) ⊢
      (l ↦ₛ LitV (LitInt (i1 + i2)) -∗ REL t << fill K (Val (LitV (LitInt i1))) : A) -∗
      REL t << fill K (FAA (Val (LitV (LitLoc l))) e2) : A := by
  obtain rfl : Val (LitV (LitInt i2)) = e2 := H2.into_val
  iintro Hl Hlog
  iapply refines_step_r
  iintro %k %j Hk
  tp_faa j
  imodintro
  iexists _
  iframe Hk
  iapply Hlog $$ Hl

end rules

end Foxtrot.BinaryRel
