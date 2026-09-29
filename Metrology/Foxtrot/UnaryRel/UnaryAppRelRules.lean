module

public import Metrology.Foxtrot.SpecProofMode
public import Metrology.Foxtrot.UnaryRel.UnaryModel

/-!
# Core rules of the unary logical relation of Foxtrot

Ported from clutch/theories/foxtrot/unary_rel/unary_app_rel_rules.v

Primitive rules for the unary "refinement" judgement `REL e : A` (`= WP e {{ A }}`) of
`Foxtrot.UnaryRel.UnaryModel`: forward reductions on the (only) program.

## Rocq → Lean map
`refines_pure`, `refines_masked_l`, `refines_wp_l`, `refines_atomic_l`, `pupd_fupd'`,
`refines_arrow_val`, `refines_arrow`, `refines_wand`, `refines_alloc_l`, `refines_alloctape_l`,
`refines_fork`, `refines_xchg_l`, `refines_cmpxchg_l`, `refines_faa_l`: same names (namespace
`Foxtrot.UnaryRel`).

## Deviations
* `IntoVal e v →` hypotheses are instance-implicit `[IntoVal (Λ := con_prob_lang) e v]`;
  `PureExec` and `Atomic` are instance-implicit too. `TCEq N (Z.to_nat z)` is `N = z.toNat`.
* Rocq `ref e` is `Alloc e`, `alloc #z` is `alloc (Val (LitV (LitInt z)))`, `#l` is
  `Val (LitV (LitLoc l))`, `of_val v` is `Val v`.
* Rocq's `P -∗ Q` lemma statements are entailments `P ⊢ Q` (as in `Foxtrot.Weakestpre`).
* `pupd_fupd'` is the same statement as `Foxtrot.pupd_fupd'` (Rocq re-proves it in this
  section); here it is `Foxtrot.UnaryRel.pupd_fupd'`, proved by `Foxtrot.pupd_fupd'` (as in
  `BinaryAppRelRules`).

## Omitted
* `Local Existing Instance pure_exec_fill` (the proofs use `pure_exec_ctx` directly).
* The commented-out Rocq lemmas (`refines_pure_r`, `refines_step_r`, `refines_alloc_r`,
  `refines_alloctape_r`, `refines_xchg_r`, `refines_cmpxchg_fail_r`, `refines_cmpxchg_suc_r`,
  `refines_faa_r`).

## Added
* Three small tests (`imod` through `elim_fupd_refines`, `unfold_rel` + `wp_pures`,
  `refines_xchg_l`).
* Note: a lemma about `fill K ..` used at `K := []` is not unified with a bare expression by
  `iapply`; restate it with a `have` of the desired type (see `refines_wand` and the tests).
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.UnaryRel

section rules

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-! ### Forward reductions on the LHS -/

/-- Rocq: `refines_pure`. -/
theorem refines_pure (n : ℕ) (e e' : expr) (A : lrel GF) (ϕ : Prop) (K' : List ectx_item)
    [Hpure : PureExec (Λ := con_prob_lang) ϕ n e e'] (Hϕ : ϕ) :
    ▷^[n] (REL fill K' e' : A) ⊢ REL fill K' e : A :=
  have : PureExec (Λ := con_prob_lang) ϕ n (fill K' e) (fill K' e') :=
    pure_exec_ctx (Λ := con_prob_lang) (fill K') ϕ n e e' Hpure
  wp_pure_step_later Hϕ

/-- Rocq: `refines_masked_l`. -/
theorem refines_masked_l (n : ℕ) (K' : List ectx_item) (e e' : expr) (A : lrel GF) (ϕ : Prop)
    [PureExec (Λ := con_prob_lang) ϕ n e e'] (Hϕ : ϕ) :
    (REL fill K' e' : A) ⊢ REL fill K' e : A :=
  (laterN_intro n).trans (refines_pure n e e' A ϕ K' Hϕ)

/-- Rocq: `refines_wp_l`. -/
theorem refines_wp_l (K : List ectx_item) (e1 : expr) (A : lrel GF) :
    WP e1 {{ v, REL fill K (Val v) : A }} ⊢ REL fill K e1 : A :=
  wp_bind (fill K)

/-- Rocq: `refines_atomic_l`. -/
theorem refines_atomic_l (E : CoPset) (K : List ectx_item) (e1 : expr) (A : lrel GF)
    [Hatomic : Atomic (Λ := con_prob_lang) StronglyAtomic e1] :
    (|={⊤, E}=> WP e1 @ E {{ v, |={E, ⊤}=> REL fill K (Val v) : A }})
      ⊢ REL fill K e1 : A :=
  wp_atomic.trans (wp_bind (fill K))

/-- Rocq: `pupd_fupd'` (re-proved in the Rocq section; see `Foxtrot.pupd_fupd'`). -/
theorem pupd_fupd' (E1 E2 : CoPset) (P : IProp GF) (h : E2 ⊆ E1) :
    pupd E1 E1 P ⊢ pupd E1 E2 iprop(|={E2, E1}=> P) :=
  Foxtrot.pupd_fupd' E1 E2 P h

/-- Rocq: `refines_arrow_val`. This rule is useful for proving that functions refine each
other. -/
theorem refines_arrow_val (v : val) (A A' : lrel GF) :
    □ (∀ v1, A v1 -∗ REL App (Val v) (Val v1) : A') ⊢ REL Val v : lrel_arr A A' := by
  iintro #H
  iapply refines_ret (Val v) v
  imodintro
  unfold lrel_arr
  imodintro
  iintro %v1 HA
  iapply H $$ HA

/-- Rocq: `refines_arrow`. -/
theorem refines_arrow (v : val) (A A' : lrel GF) :
    □ (∀ v1 : val, □ (REL Val v1 : A) -∗ REL App (Val v) (Val v1) : A')
      ⊢ REL Val v : lrel_arr A A' := by
  iintro #H
  iapply refines_arrow_val
  imodintro
  iintro %v1 #HA
  iapply H
  imodintro
  iapply refines_ret (Val v1) v1
  imodintro
  iexact HA

/-- Rocq: `refines_wand`. -/
theorem refines_wand (e1 : expr) (A A' : lrel GF) :
    (REL e1 : A) ⊢ (∀ v1, A v1 ={⊤}=∗ A' v1) -∗ REL e1 : A' := by
  have hbind : (REL e1 : A) ⊢ (∀ v, A v -∗ REL Val v : A') -∗ REL e1 : A' :=
    refines_bind [] A A' e1
  iintro He HAA
  iapply hbind $$ He
  iintro %v HA
  iapply refines_ret (Val v) v
  iapply HAA $$ HA

/-- Rocq: `refines_alloc_l`. -/
theorem refines_alloc_l (K : List ectx_item) (e : expr) (v : val) (A : lrel GF)
    [IntoVal (Λ := con_prob_lang) e v] :
    ▷ (∀ l : Loc, l ↦ v -∗ REL fill K (Val (LitV (LitLoc l))) : A)
      ⊢ REL fill K (Alloc e) : A := by
  have he := into_val (Λ := con_prob_lang) (e := e)
  simp only [con_prob_lang_of_val] at he
  subst he
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloc v $$ %(fun w => REL fill K (Val w) : A) [] Hlog
  itrivial

/-- Rocq: `refines_alloctape_l`. -/
theorem refines_alloctape_l (K : List ectx_item) (N : ℕ) (z : ℤ) (A : lrel GF)
    (hN : N = z.toNat) :
    ▷ (∀ α : Loc, α ↪N (N; []) -∗ REL fill K (Val (LitV (LitLbl α))) : A)
      ⊢ REL fill K (alloc (Val (LitV (LitInt z)))) : A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloc_tape N z hN $$ %(fun w => REL fill K (Val w) : A) [] Hlog
  itrivial

/-- Rocq: `refines_fork`. -/
theorem refines_fork (e : expr) :
    (REL e : (lrel_unit : lrel GF)) ⊢ REL Fork e : lrel_unit := by
  unfold refines refines_def
  iintro H
  iapply wp_fork $$ [H]
  · inext
    iapply wp_wand $$ H
    iintro %_ _
    itrivial
  · inext
    unfold lrel_unit
    ipureintro
    rfl

/-- Rocq: `refines_xchg_l`. -/
theorem refines_xchg_l (K : List ectx_item) (l : Loc) (e : expr) (v' : val) (A : lrel GF)
    [IntoVal (Λ := con_prob_lang) e v'] :
    (∃ v, ▷ l ↦ v ∗ ▷ (l ↦ v' -∗ REL fill K (Val v) : A))
      ⊢ REL fill K (Xchg (Val (LitV (LitLoc l))) e) : A := by
  have he := into_val (Λ := con_prob_lang) (e := e)
  simp only [con_prob_lang_of_val] at he
  subst he
  iintro Hlog
  iapply refines_wp_l
  icases Hlog with ⟨%v, Hl, Hlog⟩
  iapply wp_xchg v v' l $$ %(fun w => REL fill K (Val w) : A) Hl Hlog

/-- Rocq: `refines_cmpxchg_l`. -/
theorem refines_cmpxchg_l (K : List ectx_item) (l : Loc) (e1 e2 : expr) (v1 v2 : val)
    (A : lrel GF) [IntoVal (Λ := con_prob_lang) e1 v1] [IntoVal (Λ := con_prob_lang) e2 v2]
    (Hunboxed : val_is_unboxed v1) :
    (∃ v', ▷ l ↦ v' ∗
      ((⌜v' ≠ v1⌝ -∗ ▷ (l ↦ v' -∗ REL fill K (Val (PairV v' (LitV (LitBool false)))) : A)) ∧
       (⌜v' = v1⌝ -∗ ▷ (l ↦ v2 -∗ REL fill K (Val (PairV v' (LitV (LitBool true)))) : A))))
      ⊢ REL fill K (CmpXchg (Val (LitV (LitLoc l))) e1 e2) : A := by
  have he1 := into_val (Λ := con_prob_lang) (e := e1)
  simp only [con_prob_lang_of_val] at he1
  subst he1
  have he2 := into_val (Λ := con_prob_lang) (e := e2)
  simp only [con_prob_lang_of_val] at he2
  subst he2
  iintro Hlog
  iapply refines_wp_l
  icases Hlog with ⟨%v', Hl, Hlog⟩
  by_cases h : v' = v1
  · -- CmpXchg successful
    subst h
    icases Hlog with ⟨-, Hlog⟩
    iapply wp_cmpxchg_suc v' v' v2 l (Or.inr Hunboxed) rfl $$ %(fun w => REL fill K (Val w) : A) Hl
    iapply Hlog
    ipureintro
    rfl
  · -- CmpXchg failed
    icases Hlog with ⟨Hlog, -⟩
    iapply wp_cmpxchg_fail v' v1 v2 l _ (Or.inr Hunboxed) h $$ %(fun w => REL fill K (Val w) : A) Hl
    iapply Hlog
    ipureintro
    exact h

/-- Rocq: `refines_faa_l`. -/
theorem refines_faa_l (K : List ectx_item) (l : Loc) (e2 : expr) (i2 : ℤ) (A : lrel GF)
    [IntoVal (Λ := con_prob_lang) e2 (LitV (LitInt i2))] :
    (∃ i1 : ℤ, ▷ l ↦ LitV (LitInt i1) ∗
      ▷ (l ↦ LitV (LitInt (i1 + i2)) -∗ REL fill K (Val (LitV (LitInt i1))) : A))
      ⊢ REL fill K (FAA (Val (LitV (LitLoc l))) e2) : A := by
  have he2 := into_val (Λ := con_prob_lang) (e := e2)
  simp only [con_prob_lang_of_val] at he2
  subst he2
  iintro Hlog
  iapply refines_wp_l
  icases Hlog with ⟨%i1, Hl, Hlog⟩
  iapply wp_faa i1 i2 l $$ %(fun w => REL fill K (Val w) : A) Hl Hlog

end rules

/-! ## Tests (not in Rocq) -/

section tests

variable {GF : BundledGFunctors} [foxtrotGS GF]

example (e : expr) (A : lrel GF) (P : IProp GF) :
    (|={⊤}=> P) ⊢ (P -∗ REL e : A) -∗ REL e : A := by
  iintro HP H
  imod HP
  iapply H $$ HP

example : ⊢@{IProp GF} REL cpl(#1 + #2) : lrel_int := by
  unfold_rel
  wp_pures
  imodintro
  unfold lrel_int
  iexists 3
  ipureintro
  rfl

example (l : Loc) (A : lrel GF) :
    (l ↦ LitV (LitInt 1) -∗ REL Val (LitV (LitInt 1)) : A) ⊢
      (▷ l ↦ LitV (LitInt 1)) -∗ REL Xchg (Val (LitV (LitLoc l))) (Val (LitV (LitInt 1))) : A := by
  have h : (∃ v, ▷ l ↦ v ∗ ▷ (l ↦ LitV (LitInt 1) -∗ REL Val v : A)) ⊢
      REL Xchg (Val (LitV (LitLoc l))) (Val (LitV (LitInt 1))) : A :=
    refines_xchg_l [] l (Val (LitV (LitInt 1))) (LitV (LitInt 1)) A
  iintro H Hl
  iapply h
  iexists _
  iframe Hl
  iexact H

end tests

end Foxtrot.UnaryRel
