module

public import Metrology.Coneris.WpTactics
public import Metrology.ConProbLang.Spec.SpecRA

/-!
# Generic `tp_*` tactics for the right-hand side (specification) of `con_prob_lang`

Ported from clutch/theories/con_prob_lang/spec/spec_tactics.v

As in Rocq, the tactics are generic in an update modality
`upd : CoPset → CoPset → IProp GF → IProp GF` (for Foxtrot: `pupd`, see
`Metrology.Foxtrot.SpecProofMode`). The requirements are bundled in the classes `UpdPure`,
`UpdHeap`, `UpdAtomicConcurrency` and `UpdTapes`. A tactic `tp_x j` works on any proof-mode
goal `Δ ⊢ Q`: it locates the hypothesis `j ⤇ e` in the spatial context, finds the redex in `e`,
takes the step with the corresponding class field (an update `upd E E ..`), and eliminates the
update in the goal `Q` with an `ElimModal` instance (Rocq: `∀ P, ElimModal ψ false false
(upd E1 E1 P) P Q Q`).

## Rocq → Lean mapping
* Classes: same names and fields (`tptac_upd_pure_step`, `tptac_upd_alloc`, `tptac_upd_load`,
  `tptac_upd_store`, `tptac_upd_cmpxchg_fail`, `tptac_upd_cmpxchg_suc`, `tptac_upd_xchg`,
  `tptac_upd_faa`, `tptac_upd_fork`, `tptac_upd_alloctape`). `Σ` is `GF`, the Rocq instance
  argument `specG_con_prob_lang Σ` is `[specG_con_prob_lang GF]`. Rocq's `P -∗ Q -∗ upd ..`
  statements are `P ⊢ Q -∗ upd ..`; `TCEq N (Z.to_nat z)` is `N = z.toNat`.
* Tactic lemmas: same names (`tac_tp_bind_gen`, `tac_tp_bind`, `tac_tp_pure`, `tac_tp_store`,
  `tac_tp_load`, `tac_tp_alloc`, `tac_tp_cmpxchg_fail`, `tac_tp_cmpxchg_suc`, `tac_tp_xchg`,
  `tac_tp_faa`, `tac_tp_fork`, `tac_tp_allocnattape`). As in `Metrology.Coneris.WpTactics`
  (and iris-lean's `HeapLang/ProofMode.lean`), Rocq's environment operations are replaced by
  premises: `Δ ⊣⊢ Δ' ∗ j ⤇ e` (Rocq: `envs_lookup`/`envs_lookup_delete`, the result of
  iris-lean's `Hyps.removeG`), and a continuation `Δ' ∗ j ⤇ e' ⊢ Q` (Rocq: `envs_simple_replace`
  followed by `envs_entails`).
  - The thread's expression is `fill Kout (fill K e1)`: `K` is the (concrete) evaluation
    context found by the redex search (Rocq: `reshape_expr`) and `Kout` an arbitrary outer
    context (Rocq: the `fill ?K' ?e` branch of `tp_pure_at`, generalized to all tactics).
  - Rocq's `∀ P, ElimModal ψ false false (upd E1 E1 P) P Q Q` is required only for the `P` that
    is actually eliminated: `ElimModal ψ false io false (upd E E P) P Q Q` (iris-lean's
    `ElimModal` has the extra `InOut` parameter `io`; the tactics use `.in`).
  - `IntoVal e v` premises: the tactics require the arguments to be syntactically `Val v`.
* Tactics (all take the thread `j : ℕ` as a term):
  `tp_normalise j`, `tp_bind j efoc`, `tp_pure_at j efoc`, `tp_pure j`, `tp_pures j`, `tp_rec j`,
  `tp_seq j`, `tp_let j`, `tp_lam j`, `tp_fst j`, `tp_snd j`, `tp_proj j`, `tp_case_inl j`,
  `tp_case_inr j`, `tp_case j`, `tp_binop j`, `tp_op j`, `tp_if_true j`, `tp_if_false j`,
  `tp_if j`, `tp_pair j`, `tp_closure j`, `tp_store j`, `tp_load j`, `tp_alloc j as l H`,
  `tp_alloc j as l`, `tp_cmpxchg_fail j`, `tp_cmpxchg_suc j`, `tp_xchg j`, `tp_faa j`,
  `tp_fork j`, `tp_fork j as j' H`, `tp_fork j as j'`, `tp_allocnattape j l as H`,
  `tp_allocnattape j l`. Intro patterns `H` are iris-lean intro patterns; the focus `efoc` is
  a term of type `expr` with holes (Rocq: `open_constr`).
  - `upd` is found as in Rocq, from the `ElimModal` instances for the goal `Q`: the instances
    whose conclusion matches `Q` are enumerated, and the first whose eliminated proposition
    has the shape `upd E E P` for an `upd` with an instance of the required class is used.
  - After each step the new expression is simplified (Rocq: `pm_reduce`, here the
    `wp_expr_simp` simp set of `Metrology.Coneris.WpTactics`, which substitutes and unfolds
    derived forms); the reducts of `UnOp`/`BinOp` are evaluated, as for `wp_pure`.
  - `tp_pures j` only takes steps whose side condition is solved automatically.
  - Side conditions (`φ` of a pure step, `ψ` of the `ElimModal` instance, `v ≠ v1`,
    `vals_compare_safe`, `N = z.toNat`) are solved by `wp_solve_side` when possible, and are
    otherwise left as goals.

## Omitted
* `tp_bind_helper` (the tactics decompose the expression at the meta level).
* `pm_reduce` (see above).
* Commented-out Rocq code (`tptac_upd_allocN`, `tptac_upd_rand`, `tptac_upd_rand_tape`,
  `tac_tp_randnat`, `tp_randnat`) is not ported. In particular there is no `tp_rand` tactic
  (as in Rocq, RHS `rand` steps go through coupling rules).

## Added
* `fill_app'` (`fill_app` for `con_prob_lang.fill`), `tac_tp_upd` (the common shape of the
  tactic lemmas), `tac_tp_readd`/`tac_tp_readd_l`/`tac_tp_split2`/`tac_tp_rewrite` (context
  manipulation), `tp_pure_strict j` (Rocq: `tp_pure j` failing on unsolved side conditions),
  the internal tactics `tp_alloc_core`, `tp_allocnattape_core`, and the meta-level machinery
  (`mkAppNamed`, `splitThreadExpr`, `TpGoal`, `runTacticTp`, `tpLookupHyp`, `findUpd`,
  `tpThreadCont`, `tpHeapOp`, `tpAllocCont`, ...). The generic helpers of
  `Metrology.Coneris.WpTactics` (the port of `con_prob_lang/wp_tactics.v`, which Rocq's
  `spec_tactics.v` imports) are reused: `gwpExprSimp`, `findAnyPureExec`, `findRecPureExec`,
  `gwpSolveSide`, `gwpFill`, ...
* Unlike Rocq, `tp_alloc`, `tp_fork .. as ..` and `tp_allocnattape` introduce the new
  location/thread with the user-given name directly (Rocq: `intros l`).
-/

open Iris Iris.BI Iris.ProofMode ConProbLang ConProbLang.con_prob_lang Qq

namespace ConProbLang

/-! ## The classes -/

section classes

variable (GF : BundledGFunctors) [specG_con_prob_lang GF]

/-- Rocq: `UpdPure`. A basic set of requirements for an update modality. -/
public class UpdPure (upd : CoPset → CoPset → IProp GF → IProp GF) : Prop where
  tptac_upd_pure_step (j : ℕ) (E : CoPset) (e1 e2 : expr) (φ : Prop) (n : ℕ) :
    PureExec (Λ := con_prob_lang) φ n e1 e2 → φ → j ⤇ e1 ⊢ upd E E (j ⤇ e2)

/-- Rocq: `UpdHeap`. -/
public class UpdHeap (upd : CoPset → CoPset → IProp GF → IProp GF) : Prop where
  tptac_upd_alloc (j : ℕ) (K : List ectx_item) (E : CoPset) (v : val) :
    j ⤇ fill K (Alloc (Val v)) ⊢
      upd E E iprop(∃ l, l ↦ₛ v ∗ j ⤇ fill K (Val (LitV (LitLoc l))))
  tptac_upd_load (j : ℕ) (K : List ectx_item) (E : CoPset) (v : val) (l : Loc) (dq : DFrac) :
    l ↦ₛ{dq} v ⊢ j ⤇ fill K (Load (Val (LitV (LitLoc l)))) -∗
      upd E E iprop(l ↦ₛ{dq} v ∗ j ⤇ fill K (Val v))
  tptac_upd_store (j : ℕ) (K : List ectx_item) (E : CoPset) (v v' : val) (l : Loc) :
    l ↦ₛ v' ⊢ j ⤇ fill K (Store (Val (LitV (LitLoc l))) (Val v)) -∗
      upd E E iprop(l ↦ₛ v ∗ j ⤇ fill K (Val (LitV LitUnit)))

/-- Rocq: `UpdAtomicConcurrency`. -/
public class UpdAtomicConcurrency (upd : CoPset → CoPset → IProp GF → IProp GF) : Prop where
  tptac_upd_cmpxchg_fail (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc) (dq : DFrac)
    (v v1 v2 : val) : v ≠ v1 → vals_compare_safe v v1 →
    l ↦ₛ{dq} v ⊢ j ⤇ fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) -∗
      upd E E iprop(l ↦ₛ{dq} v ∗ j ⤇ fill K (Val (PairV v (LitV (LitBool false)))))
  tptac_upd_cmpxchg_suc (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc) (v v1 v2 : val) :
    v = v1 → vals_compare_safe v v1 →
    l ↦ₛ v ⊢ j ⤇ fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) -∗
      upd E E iprop(l ↦ₛ v2 ∗ j ⤇ fill K (Val (PairV v (LitV (LitBool true)))))
  tptac_upd_xchg (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc) (v1 v2 : val) :
    l ↦ₛ v1 ⊢ j ⤇ fill K (Xchg (Val (LitV (LitLoc l))) (Val v2)) -∗
      upd E E iprop(l ↦ₛ v2 ∗ j ⤇ fill K (Val v1))
  tptac_upd_faa (j : ℕ) (K : List ectx_item) (E : CoPset) (l : Loc) (i1 i2 : ℤ) :
    l ↦ₛ LitV (LitInt i1) ⊢
      j ⤇ fill K (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) -∗
      upd E E iprop(l ↦ₛ LitV (LitInt (i1 + i2)) ∗ j ⤇ fill K (Val (LitV (LitInt i1))))
  tptac_upd_fork (j : ℕ) (K : List ectx_item) (E : CoPset) (e : expr) :
    j ⤇ fill K (Fork e) ⊢ upd E E iprop(∃ k, k ⤇ e ∗ j ⤇ fill K (Val (LitV LitUnit)))

/-- Rocq: `UpdTapes`. (Note: no presampling on the RHS.) -/
public class UpdTapes (upd : CoPset → CoPset → IProp GF → IProp GF) : Prop where
  tptac_upd_alloctape (j : ℕ) (K : List ectx_item) (E : CoPset) (N : ℕ) (z : ℤ) :
    N = z.toNat →
    True ⊢ j ⤇ fill K (AllocTape (Val (LitV (LitInt z)))) -∗
      upd E E iprop(∃ l, l ↪ₛN (N; []) ∗ j ⤇ fill K (Val (LitV (LitLbl l))))

end classes

/-! ## Tactic lemmas -/

/-- Helper: `fill_app` for `con_prob_lang.fill`. -/
public theorem fill_app' (K1 K2 : List ectx_item) (e : expr) :
    fill (K1 ++ K2) e = fill K2 (fill K1 e) :=
  conEctxiLanguage.fill_app _ _ _

section helpers

variable {GF : BundledGFunctors}

/-- Helper: the common shape of the tactic lemmas. The resource `R` (split off the context) is
updated to `R'` by `upd E E`, and the update is eliminated in the goal `Q`. -/
public theorem tac_tp_upd {upd : CoPset → CoPset → IProp GF → IProp GF}
    {Δ Δ' R R' Q : IProp GF} {ψ : Prop} {E : CoPset} {io : InOut}
    (hstep : R ⊢ upd E E R') (helim : ElimModal ψ false io false (upd E E R') R' Q Q)
    (hψ : ψ) (hsplit : Δ ⊢ Δ' ∗ R) (hcont : Δ' ∗ R' ⊢ Q) : Δ ⊢ Q := by
  refine hsplit.trans ?_
  refine .trans ?_ (helim.elim_modal hψ)
  refine sep_comm.1.trans (sep_mono hstep ?_)
  exact wand_intro hcont

/-- Helper: re-add one hypothesis (the result of iris-lean's `Hyps.add`). -/
public theorem tac_tp_readd {Δ J Δ1 Q : IProp GF} (h : Δ ∗ □?false J ⊣⊢ Δ1) (pf : Δ1 ⊢ Q) :
    Δ ∗ J ⊢ Q :=
  h.1.trans pf

/-- Helper: re-add a hypothesis `P` below another one `J`. -/
public theorem tac_tp_readd_l {Δ P J Δ1 Q : IProp GF} (h1 : Δ ∗ □?false P ⊣⊢ Δ1)
    (pf : Δ1 ∗ J ⊢ Q) : (Δ ∗ P) ∗ J ⊢ Q :=
  (sep_mono h1.1 .rfl).trans pf

/-- Helper: the two lookups of the heap tactic lemmas. -/
public theorem tac_tp_split2 {Δ1 Δ2 Δ3 P J : IProp GF} (h1 : Δ1 ⊣⊢ Δ2 ∗ J)
    (h2 : Δ2 ⊣⊢ Δ3 ∗ P) : Δ1 ⊢ Δ3 ∗ (P ∗ J) :=
  h1.1.trans ((sep_mono h2.1 .rfl).trans sep_assoc.1)

end helpers

section lemmas

variable {GF : BundledGFunctors} [specG_con_prob_lang GF]

/-- Helper: rewrite the expression of a thread hypothesis (Rocq: `pm_reduce`). -/
public theorem tac_tp_rewrite {Δ Q : IProp GF} (j : ℕ) (Kout : List ectx_item) {e e' : expr}
    (he : e = e') (h : Δ ∗ j ⤇ fill Kout e' ⊢ Q) : Δ ∗ j ⤇ fill Kout e ⊢ Q :=
  he ▸ h

/-- Rocq: `tac_tp_bind_gen`. -/
public theorem tac_tp_bind_gen {Δ Δ' Q : IProp GF} (j : ℕ) {e e' : expr}
    (hsplit : Δ ⊣⊢ Δ' ∗ j ⤇ e) (he : e = e') (hcont : Δ' ∗ j ⤇ e' ⊢ Q) : Δ ⊢ Q := by
  subst he
  exact hsplit.1.trans hcont

/-- Rocq: `tac_tp_bind`. -/
public theorem tac_tp_bind {Δ Δ' Q : IProp GF} (j : ℕ) (e' : expr) (K' : List ectx_item)
    {e : expr} (hsplit : Δ ⊣⊢ Δ' ∗ j ⤇ e) (he : e = fill K' e')
    (hcont : Δ' ∗ j ⤇ fill K' e' ⊢ Q) : Δ ⊢ Q :=
  tac_tp_bind_gen j hsplit he hcont

variable {upd : CoPset → CoPset → IProp GF → IProp GF}

/-- Rocq: `tac_tp_pure`. -/
public theorem tac_tp_pure [UpdPure GF upd] {Δ Δ' Q : IProp GF} (j : ℕ) (Kout K : List ectx_item)
    {e1 e2 : expr} {φ ψ : Prop} {n : ℕ} {E : CoPset} {io : InOut}
    (hexec : PureExec (Λ := con_prob_lang) φ n e1 e2)
    (helim : ElimModal ψ false io false (upd E E (j ⤇ fill Kout (fill K e2)))
      (j ⤇ fill Kout (fill K e2)) Q Q)
    (hsplit : Δ ⊣⊢ Δ' ∗ j ⤇ fill Kout (fill K e1)) (hψ : ψ) (hφ : φ)
    (hcont : Δ' ∗ j ⤇ fill Kout (fill K e2) ⊢ Q) : Δ ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ hsplit.1 hcont
  rw [← fill_app', ← fill_app']
  exact UpdPure.tptac_upd_pure_step j E _ _ φ n
    (pure_exec_ctx (Λ := con_prob_lang) (fill (K ++ Kout)) φ n e1 e2 hexec) hφ

section heap

variable [UpdHeap GF upd]

/-- Rocq: `tac_tp_store`. -/
public theorem tac_tp_store {Δ1 Δ2 Δ3 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item) {l : Loc}
    {v v' : val} {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(l ↦ₛ v ∗ j ⤇ fill Kout (fill K (Val (LitV LitUnit)))))
      iprop(l ↦ₛ v ∗ j ⤇ fill Kout (fill K (Val (LitV LitUnit)))) Q Q) (hψ : ψ)
    (hsplit1 : Δ1 ⊣⊢ Δ2 ∗ j ⤇ fill Kout (fill K (Store (Val (LitV (LitLoc l))) (Val v))))
    (hsplit2 : Δ2 ⊣⊢ Δ3 ∗ l ↦ₛ v')
    (hcont : (Δ3 ∗ l ↦ₛ v) ∗ j ⤇ fill Kout (fill K (Val (LitV LitUnit))) ⊢ Q) : Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ (tac_tp_split2 hsplit1 hsplit2) (sep_assoc.2.trans hcont)
  rw [← fill_app', ← fill_app']
  exact wand_elim (UpdHeap.tptac_upd_store (upd := upd) j (K ++ Kout) E v v' l)

/-- Rocq: `tac_tp_load`. -/
public theorem tac_tp_load {Δ1 Δ2 Δ3 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item) {l : Loc}
    {q : DFrac} {v : val} {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(l ↦ₛ{q} v ∗ j ⤇ fill Kout (fill K (Val v))))
      iprop(l ↦ₛ{q} v ∗ j ⤇ fill Kout (fill K (Val v))) Q Q) (hψ : ψ)
    (hsplit1 : Δ1 ⊣⊢ Δ2 ∗ j ⤇ fill Kout (fill K (Load (Val (LitV (LitLoc l))))))
    (hsplit2 : Δ2 ⊣⊢ Δ3 ∗ l ↦ₛ{q} v)
    (hcont : (Δ3 ∗ l ↦ₛ{q} v) ∗ j ⤇ fill Kout (fill K (Val v)) ⊢ Q) : Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ (tac_tp_split2 hsplit1 hsplit2) (sep_assoc.2.trans hcont)
  rw [← fill_app', ← fill_app']
  exact wand_elim (UpdHeap.tptac_upd_load (upd := upd) j (K ++ Kout) E v l q)

/-- Rocq: `tac_tp_alloc`. -/
public theorem tac_tp_alloc {Δ1 Δ2 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item) {v : val}
    {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(∃ l, l ↦ₛ v ∗ j ⤇ fill Kout (fill K (Val (LitV (LitLoc l))))))
      iprop(∃ l, l ↦ₛ v ∗ j ⤇ fill Kout (fill K (Val (LitV (LitLoc l))))) Q Q) (hψ : ψ)
    (hsplit : Δ1 ⊣⊢ Δ2 ∗ j ⤇ fill Kout (fill K (Alloc (Val v))))
    (hcont : ∀ l : Loc, Δ2 ∗ j ⤇ fill Kout (fill K (Val (LitV (LitLoc l)))) ⊢ l ↦ₛ v -∗ Q) :
    Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ hsplit.1 ?_
  · rw [← fill_app']
    refine (UpdHeap.tptac_upd_alloc (upd := upd) j (K ++ Kout) E v).trans ?_
    simp only [fill_app']
    exact .rfl
  · refine sep_exists_left.1.trans (exists_elim fun l => ?_)
    refine (sep_mono .rfl sep_comm.1).trans (sep_assoc.2.trans ?_)
    exact wand_elim (hcont l)

end heap

section concurrency

variable [UpdAtomicConcurrency GF upd]

/-- Rocq: `tac_tp_cmpxchg_fail`. -/
public theorem tac_tp_cmpxchg_fail {Δ1 Δ2 Δ3 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item)
    {l : Loc} {q : DFrac} {v' v1 v2 : val} {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(l ↦ₛ{q} v' ∗ j ⤇ fill Kout (fill K (Val (PairV v' (LitV (LitBool false)))))))
      iprop(l ↦ₛ{q} v' ∗ j ⤇ fill Kout (fill K (Val (PairV v' (LitV (LitBool false))))))
      Q Q) (hψ : ψ)
    (hsplit1 : Δ1 ⊣⊢ Δ2 ∗
      j ⤇ fill Kout (fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2))))
    (hsplit2 : Δ2 ⊣⊢ Δ3 ∗ l ↦ₛ{q} v') (hne : v' ≠ v1) (hsafe : vals_compare_safe v' v1)
    (hcont : (Δ3 ∗ l ↦ₛ{q} v') ∗
      j ⤇ fill Kout (fill K (Val (PairV v' (LitV (LitBool false))))) ⊢ Q) : Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ (tac_tp_split2 hsplit1 hsplit2) (sep_assoc.2.trans hcont)
  rw [← fill_app', ← fill_app']
  exact wand_elim (UpdAtomicConcurrency.tptac_upd_cmpxchg_fail (upd := upd) j (K ++ Kout) E l q v' v1 v2 hne hsafe)

/-- Rocq: `tac_tp_cmpxchg_suc`. -/
public theorem tac_tp_cmpxchg_suc {Δ1 Δ2 Δ3 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item)
    {l : Loc} {v' v1 v2 : val} {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(l ↦ₛ v2 ∗ j ⤇ fill Kout (fill K (Val (PairV v' (LitV (LitBool true)))))))
      iprop(l ↦ₛ v2 ∗ j ⤇ fill Kout (fill K (Val (PairV v' (LitV (LitBool true)))))) Q Q)
    (hψ : ψ)
    (hsplit1 : Δ1 ⊣⊢ Δ2 ∗
      j ⤇ fill Kout (fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2))))
    (hsplit2 : Δ2 ⊣⊢ Δ3 ∗ l ↦ₛ v') (heq : v' = v1) (hsafe : vals_compare_safe v' v1)
    (hcont : (Δ3 ∗ l ↦ₛ v2) ∗
      j ⤇ fill Kout (fill K (Val (PairV v' (LitV (LitBool true))))) ⊢ Q) : Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ (tac_tp_split2 hsplit1 hsplit2) (sep_assoc.2.trans hcont)
  rw [← fill_app', ← fill_app']
  exact wand_elim (UpdAtomicConcurrency.tptac_upd_cmpxchg_suc (upd := upd) j (K ++ Kout) E l v' v1 v2 heq hsafe)

/-- Rocq: `tac_tp_xchg`. -/
public theorem tac_tp_xchg {Δ1 Δ2 Δ3 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item) {l : Loc}
    {v v' : val} {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(l ↦ₛ v ∗ j ⤇ fill Kout (fill K (Val v'))))
      iprop(l ↦ₛ v ∗ j ⤇ fill Kout (fill K (Val v'))) Q Q) (hψ : ψ)
    (hsplit1 : Δ1 ⊣⊢ Δ2 ∗ j ⤇ fill Kout (fill K (Xchg (Val (LitV (LitLoc l))) (Val v))))
    (hsplit2 : Δ2 ⊣⊢ Δ3 ∗ l ↦ₛ v')
    (hcont : (Δ3 ∗ l ↦ₛ v) ∗ j ⤇ fill Kout (fill K (Val v')) ⊢ Q) : Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ (tac_tp_split2 hsplit1 hsplit2) (sep_assoc.2.trans hcont)
  rw [← fill_app', ← fill_app']
  exact wand_elim (UpdAtomicConcurrency.tptac_upd_xchg (upd := upd) j (K ++ Kout) E l v' v)

/-- Rocq: `tac_tp_faa`. -/
public theorem tac_tp_faa {Δ1 Δ2 Δ3 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item) {l : Loc}
    {z1 z2 : ℤ} {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(l ↦ₛ LitV (LitInt (z1 + z2)) ∗
        j ⤇ fill Kout (fill K (Val (LitV (LitInt z1))))))
      iprop(l ↦ₛ LitV (LitInt (z1 + z2)) ∗ j ⤇ fill Kout (fill K (Val (LitV (LitInt z1)))))
      Q Q) (hψ : ψ)
    (hsplit1 : Δ1 ⊣⊢ Δ2 ∗
      j ⤇ fill Kout (fill K (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt z2))))))
    (hsplit2 : Δ2 ⊣⊢ Δ3 ∗ l ↦ₛ LitV (LitInt z1))
    (hcont : (Δ3 ∗ l ↦ₛ LitV (LitInt (z1 + z2))) ∗
      j ⤇ fill Kout (fill K (Val (LitV (LitInt z1)))) ⊢ Q) : Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ (tac_tp_split2 hsplit1 hsplit2) (sep_assoc.2.trans hcont)
  rw [← fill_app', ← fill_app']
  exact wand_elim (UpdAtomicConcurrency.tptac_upd_faa (upd := upd) j (K ++ Kout) E l z1 z2)

/-- Rocq: `tac_tp_fork`. -/
public theorem tac_tp_fork {Δ1 Δ2 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item) {e' : expr}
    {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(∃ k, k ⤇ e' ∗ j ⤇ fill Kout (fill K (Val (LitV LitUnit)))))
      iprop(∃ k, k ⤇ e' ∗ j ⤇ fill Kout (fill K (Val (LitV LitUnit)))) Q Q) (hψ : ψ)
    (hsplit : Δ1 ⊣⊢ Δ2 ∗ j ⤇ fill Kout (fill K (Fork e')))
    (hcont : Δ2 ∗ j ⤇ fill Kout (fill K (Val (LitV LitUnit))) ⊢ ∀ k, k ⤇ e' -∗ Q) :
    Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ hsplit.1 ?_
  · rw [← fill_app']
    refine (UpdAtomicConcurrency.tptac_upd_fork (upd := upd) j (K ++ Kout) E e').trans ?_
    simp only [fill_app']
    exact .rfl
  · refine sep_exists_left.1.trans (exists_elim fun k => ?_)
    refine (sep_mono .rfl sep_comm.1).trans (sep_assoc.2.trans ?_)
    exact wand_elim (hcont.trans (forall_elim k))

end concurrency

section tapes

variable [UpdTapes GF upd]

/-- Rocq: `tac_tp_allocnattape`. -/
public theorem tac_tp_allocnattape {Δ1 Δ2 Q : IProp GF} (j : ℕ) (Kout K : List ectx_item)
    {N : ℕ} {z : ℤ} {ψ : Prop} {E : CoPset} {io : InOut}
    (helim : ElimModal ψ false io false
      (upd E E iprop(∃ l, l ↪ₛN (N; []) ∗ j ⤇ fill Kout (fill K (Val (LitV (LitLbl l))))))
      iprop(∃ l, l ↪ₛN (N; []) ∗ j ⤇ fill Kout (fill K (Val (LitV (LitLbl l))))) Q Q)
    (hψ : ψ) (hN : N = z.toNat)
    (hsplit : Δ1 ⊣⊢ Δ2 ∗ j ⤇ fill Kout (fill K (AllocTape (Val (LitV (LitInt z))))))
    (hcont : ∀ α : Loc, Δ2 ∗ j ⤇ fill Kout (fill K (Val (LitV (LitLbl α)))) ⊢
      α ↪ₛN (N; []) -∗ Q) :
    Δ1 ⊢ Q := by
  refine tac_tp_upd ?_ helim hψ hsplit.1 ?_
  · rw [← fill_app']
    refine emp_sep.2.trans ((sep_mono true_intro .rfl).trans
      ((wand_elim (UpdTapes.tptac_upd_alloctape (upd := upd) j (K ++ Kout) E N z hN)).trans ?_))
    simp only [fill_app']
    exact .rfl
  · refine sep_exists_left.1.trans (exists_elim fun l => ?_)
    refine (sep_mono .rfl sep_comm.1).trans (sep_assoc.2.trans ?_)
    exact wand_elim (hcont l)

end tapes

end lemmas

/-! ## The tactics -/

section meta_tactics

open Lean Meta Elab Tactic Coneris

/-- Apply the constant `c` to the arguments `args`, given by the names of the binders of `c`
(in binder order); the other arguments are inferred by unification, and the remaining
instance-implicit arguments are synthesized. -/
public meta def mkAppNamed (c : Name) (args : List (Name × Lean.Expr)) : MetaM Lean.Expr := do
  let cinfo ← getConstInfo c
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst c us
  let ty ← inferType f
  let names ← forallTelescope ty fun xs _ => xs.mapM fun x => x.fvarId!.getUserName
  let (mvs, bis, _) ← forallMetaTelescope ty
  for (n, _) in args do
    unless names.contains n do throwError "mkAppNamed: {c} has no argument {n}"
  for i in [0:mvs.size] do
    let some v := args.lookup names[i]! | continue
    let mv := mvs[i]!
    unless ← isDefEq (← inferType mv) (← inferType v) do
      throwError "mkAppNamed: argument {names[i]!} of {c} has type{indentExpr (← inferType v)}\n\
        but is expected to have type{indentExpr (← instantiateMVars (← inferType mv))}"
    unless ← isDefEq mv v do throwError "mkAppNamed: cannot assign argument {names[i]!} of {c}"
  for (mv, bi) in mvs.zip bis do
    if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
      let inst ← synthInstance (← instantiateMVars (← inferType mv))
      mv.mvarId!.assign inst
  instantiateMVars (mkAppN f mvs)

/-- The empty evaluation context `[] : List ectx_item`. -/
public meta def nilEctx : Lean.Expr := mkApp (mkConst ``List.nil [0]) (mkConst ``ectx_item)

/-- Parse an evaluation context `K : List ectx_item` into its literal items (innermost first)
and an opaque tail: `K = items ++ tail`. -/
public meta partial def parseEctxList (K : Lean.Expr) :
    MetaM (List Lean.Expr × Option Lean.Expr) := do
  let K ← instantiateMVars K
  match K.consumeMData.getAppFnArgs with
  | (``List.nil, _) => return ([], none)
  | (``List.cons, #[_, x, xs]) =>
    let (l, t) ← parseEctxList xs
    return (x :: l, t)
  | (``HAppend.hAppend, #[_, _, _, _, a, b]) | (``List.append, #[_, a, b]) =>
    let (la, ta) ← parseEctxList a
    if ta.isSome then return ([], some K)
    let (lb, tb) ← parseEctxList b
    return (la ++ lb, tb)
  | _ => return ([], some K)

/-- Expand the fills `fill K e` with a literal `K` at the head of `e`. -/
public meta partial def expandLitFills (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← instantiateMVars e
  match e.consumeMData.getAppFnArgs with
  | (``con_prob_lang.fill, #[K, x]) =>
    let (items, tail) ← parseEctxList K
    if tail.isSome then return e
    let some e' := fillMeta items (← expandLitFills x) | return e
    return e'
  | _ => return e

/-- Split the expression `e` of a thread `j ⤇ e` into an opaque outer evaluation context `Kout`
and an expression `e0` in constructor form (derived forms and literal fills are unfolded), with
`e ≡ fill Kout e0` definitionally (Rocq: the `fill ?K' ?e` branch of `tp_pure_at`). -/
public meta def splitThreadExpr (e : Lean.Expr) : MetaM (Option Lean.Expr × Lean.Expr) := do
  let e ← instantiateMVars e
  match e.consumeMData.getAppFnArgs with
  | (``con_prob_lang.fill, #[K, x]) =>
    let (items, tail) ← parseEctxList K
    let x ← expandLitFills (← expandDerived x)
    let some x' := fillMeta items x | return (none, ← expandDerived e)
    return (tail, x')
  | _ => return (none, ← expandLitFills (← expandDerived e))

/-- `fill Kout e` (or `e` if there is no outer context). -/
public meta def mkThreadExpr (Kout? : Option Lean.Expr) (e : Lean.Expr) : Lean.Expr :=
  match Kout? with
  | none => e
  | some K => mkApp2 (mkConst ``con_prob_lang.fill) K e

/-- A proof-mode goal `Δ ⊢ Q` for the `tp_*` tactics, with the thread hypothesis `j ⤇ e`
removed (`pfSplit : Δ ⊣⊢ Δ' ∗ j ⤇ e`) and `e ≡ fill Kout e0`. -/
public meta structure TpGoal where
  {u : Level}
  {prop : Q(Type u)}
  {bi : Q(BI $prop)}
  {ehyps : Q($prop)}
  hyps : Hyps bi ehyps
  {ehyps' : Q($prop)}
  hyps' : Hyps bi ehyps'
  pfSplit : Lean.Expr
  name : Name
  vid : IVarId
  GF : Lean.Expr
  S : Lean.Expr
  j : Lean.Expr
  e : Lean.Expr
  Kout? : Option Lean.Expr
  e0 : Lean.Expr
  Q : Lean.Expr

/-- The outer evaluation context (`[]` if there is none). -/
public meta def TpGoal.Kout (g : TpGoal) : Lean.Expr := g.Kout?.getD nilEctx

/-- `k ⤇ e`. -/
public meta def TpGoal.frag (g : TpGoal) (k e : Lean.Expr) : Lean.Expr :=
  mkApp4 (mkConst ``spec_prog_frag) g.GF g.S k e

/-- `j ⤇ fill Kout e0'` (the thread after a step to `e0'`). -/
public meta def TpGoal.thread (g : TpGoal) (e0' : Lean.Expr) : Lean.Expr :=
  g.frag g.j (mkThreadExpr g.Kout? e0')

/-- `l ↦ₛ{dq} v`. -/
public meta def TpGoal.heapFrag (g : TpGoal) (l v dq : Lean.Expr) : Lean.Expr :=
  mkApp5 (mkConst ``spec_heap_frag) g.GF g.S l v dq

/-- Elaborate the thread identifier `j : ℕ`. -/
public meta def elabThread (j : Syntax) : TacticM Lean.Expr := withMainContext do
  let j ← Tactic.elabTermEnsuringType j (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars j

/-- Locate (and remove) a spatial hypothesis `pat`, where `pat` is an application of the
constant `head` whose `i`-th argument `key` must match (up to reducible unfolding) before the
full pattern is unified (this avoids unfolding the resource definitions). -/
public meta def tpLookupHyp {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (head : Name) (i : Nat) (key pat : Lean.Expr) :
    ProofModeM (Name × IVarId × (e'' : Q($prop)) × Hyps bi e'' × Lean.Expr) := do
  let some ((name, vid), ⟨e'', hyps'', _, _, _, _, pf⟩) ← hyps.removeG false
      fun name vid p' ty => do
        let ty ← instantiateMVars ty
        let ty := ty.consumeMData
        unless ty.isAppOf head do return none
        let args := ty.getAppArgs
        unless i < args.size do return none
        unless ← withReducible (isDefEq args[i]! key) do return none
        let ok ← observing? (do
          guard (← isDefEq ty pat)
          guard (← isDefEq p' (mkConst ``false)))
        return ok.map fun _ => (name, vid)
    | throwError "cannot find a hypothesis {← instantiateMVars pat}"
  return ⟨name, vid, e'', hyps'', pf⟩

/-- Locate the hypothesis `j ⤇ e` (in the spatial context; Rocq: `iAssumptionCore`) and split
the proof-mode goal. -/
public meta def runTacticTp {α} (tacName : Name) (jStx : Syntax)
    (k : MVarId → TpGoal → ProofModeM α) : TacticM α := do
  let j ← elabThread jStx
  ProofModeM.runTactic tacName fun mvar {prop, hyps, goal, ..} => do
    let propE := (← instantiateMVars prop).consumeMData
    unless propE.isAppOfArity ``Iris.IProp 1 do
      throwError "{tacName}: the goal {goal} must be an `IProp`"
    let GF := propE.appArg!
    let S ← mkFreshExprMVar (← mkAppM ``specG_con_prob_lang #[GF])
    let ex ← mkFreshExprMVar (mkConst ``expr)
    let pat := mkApp4 (mkConst ``spec_prog_frag) GF S j ex
    let ⟨name, vid, _, hyps', pfSplit⟩ ← try tpLookupHyp hyps ``spec_prog_frag 2 j pat
      catch _ => throwError "{tacName}: cannot find the RHS '{j} ⤇ _'"
    let S ← instantiateMVars S
    let e ← instantiateMVars ex
    let (Kout?, e0) ← splitThreadExpr e
    k mvar { hyps, hyps', pfSplit, name, vid, GF, S, j, e, Kout?, e0, Q := goal }

/-- Find the update modality `upd` with an instance of `cls` and an `ElimModal` instance
`ElimModal ψ false .in false (upd E E P) P Q Q` for the goal `Q` (Rocq: the `tc_solve` of
`∀ P, ElimModal ψ false false (upd E1 E1 P) P Q Q`, which determines `upd` by unification).
The candidates for `upd` are read off the `ElimModal` instances whose conclusion matches `Q`.
Returns `upd`, `E`, `ψ` and the `ElimModal` instance. -/
public meta def findUpd (g : TpGoal) (cls : Name) (P : Lean.Expr) :
    ProofModeM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let prop : Lean.Expr := g.prop
  let bi : Lean.Expr := g.bi
  let elimTy (φ P0 Q' : Lean.Expr) : Lean.Expr :=
    mkAppN (mkConst ``ElimModal [g.u]) #[prop, bi, φ, mkConst ``false, mkConst ``InOut.in,
      mkConst ``false, P0, P, g.Q, Q']
  -- the candidates
  let cands ← IO.mkRef (#[] : Array Lean.Expr)
  let target := elimTy (← mkFreshExprMVar (mkSort .zero)) (← mkFreshExprMVar prop)
    (← mkFreshExprMVar prop)
  let insts ← try SynthInstance.getInstances target catch _ => pure #[]
  for inst in insts.reverse do
    let s ← saveState
    try
      let instTy ← inferType inst.val
      let (mvs, bis, body) ← forallMetaTelescope instTy
      if ← withTransparency .instances (isDefEq body target) then
        for (mv, bi) in mvs.zip bis do
          if bi.isInstImplicit && !(← mv.mvarId!.isAssigned) then
            if let some v ← synthInstance? (← instantiateMVars (← inferType mv)) then
              discard <| isDefEq mv v
        let P0 ← instantiateMVars (target.getAppArgs[6]!)
        let args := P0.getAppArgs
        if args.size ≥ 3 then
          let upd ← instantiateMVars (mkAppN P0.getAppFn (args.extract 0 (args.size - 3)))
          if !upd.hasExprMVar then cands.modify (·.push upd)
    catch _ => pure ()
    s.restore
  for upd in ← cands.get do
    let s ← saveState
    try
      let clsTy ← mkAppOptM cls #[g.GF, g.S, upd]
      let some _ ← synthInstance? clsTy | failure
      let E ← mkFreshExprMVar (mkConst ``CoPset)
      let ψ ← mkFreshExprMVar (mkSort .zero)
      let Q' ← mkFreshExprMVar prop
      let ty := elimTy ψ (mkApp3 upd E E P) Q'
      let some inst ← trySynthRaw ty | failure
      guard (← isDefEq Q' g.Q)
      return (upd, ← instantiateMVars E, ← instantiateMVars ψ, ← instantiateMVars inst)
    catch _ => s.restore
  throwError "cannot eliminate modality in the goal {g.Q} (no update modality with an \
    instance of {cls} found)"

/-- Add the goal `Δ ⊢ Q'`. -/
public meta def tpAddGoal {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (Q' : Lean.Expr) : ProofModeM Lean.Expr := do
  let pf ← addBIGoal hyps (Q' : Q($prop))
  return pf

/-- Add the hypothesis `P` (with name `name`) to the context `Δ` and add the goal `Q'`.
Returns the proof of `Δ ∗ P ⊢ Q'`. -/
public meta def tpAddHyp {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (name : Name) (vid : IVarId) (hypP Q' : Lean.Expr) :
    ProofModeM Lean.Expr := do
  let ⟨_, hyps2, pfAdd⟩ := hyps.add bi name vid q(false) (hypP : Q($prop))
  let pf ← tpAddGoal hyps2 Q'
  mkAppM ``tac_tp_readd #[pfAdd, pf]

/-- Re-add the thread hypothesis `j ⤇ fill Kout e0'` (with the name it had, after simplifying
`e0'`, Rocq: `pm_reduce`) to the context `Δ` and add the goal `Q'`. Returns the proof of
`Δ ∗ j ⤇ fill Kout e0' ⊢ Q'`. -/
public meta def tpThreadCont {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (g : TpGoal) (e0' Q' : Lean.Expr) : ProofModeM Lean.Expr := do
  let (e0s, pfeq?) ← gwpExprSimp e0'
  let pf ← tpAddHyp hyps g.name g.vid (g.thread e0s) Q'
  match pfeq? with
  | none => return pf
  | some pfeq => mkAppNamed ``tac_tp_rewrite [(`j, g.j), (`Kout, g.Kout), (`he, pfeq), (`h, pf)]

/-- Re-add a hypothesis `P` (with name `name`) and the thread hypothesis: a proof of
`(Δ ∗ P) ∗ j ⤇ fill Kout e0' ⊢ Q`. -/
public meta def tpReaddCont {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (hyps : Hyps bi e) (name : Name) (vid : IVarId) (P : Lean.Expr) (g : TpGoal)
    (e0' : Lean.Expr) : ProofModeM Lean.Expr := do
  let ⟨_, hyps2, pfAdd⟩ := hyps.add bi name vid q(false) (P : Q($prop))
  let pf ← tpThreadCont hyps2 g e0' g.Q
  mkAppM ``tac_tp_readd_l #[pfAdd, pf]

/-- Solve the side condition `ψ` of the `ElimModal` instance. -/
public meta def tpSolveElimSide (ψ : Lean.Expr) : ProofModeM Lean.Expr :=
  gwpSolveSide ψ false

/-- Rocq: `tp_normalise j`. Simplify the expression of the thread `j` (unfolding literal
evaluation contexts, derived forms and substitutions). -/
elab "tp_normalise " j:term:max : tactic =>
  runTacticTp `tp_normalise j fun mvar g => do
    let (e0s, pfeq?) ← gwpExprSimp g.e0
    let e' := mkThreadExpr g.Kout? e0s
    let heTy ← mkEq g.e e'
    let he ← match pfeq? with
      | none => mkExpectedTypeHint (← mkEqRefl g.e) heTy
      | some pfeq => do
        let pf ← match g.Kout? with
          | none => pure pfeq
          | some K => mkCongrArg (mkApp (mkConst ``con_prob_lang.fill) K) pfeq
        mkExpectedTypeHint pf heTy
    let hcont ← tpAddHyp g.hyps' g.name g.vid (g.frag g.j e') g.Q
    mvar.assign (← mkAppNamed ``tac_tp_bind_gen
      [(`j, g.j), (`hsplit, g.pfSplit), (`he, he), (`hcont, hcont)])

/-- Rocq: `tp_bind j efoc`. Bind the first subexpression (following the evaluation order) of the
thread `j` that unifies with `efoc`: the thread becomes `j ⤇ fill K efoc`. -/
elab "tp_bind " j:term:max ppSpace f:term:max : tactic => do
  let focus ← elabFocus f
  runTacticTp `tp_bind j fun mvar g => do
    let some ((), K, e1) ← reshapeExpr g.e0 fun _ e1 => do guard (← isDefEq e1 focus)
      | throwError "tp_bind: cannot find {focus} in {g.e0}"
    let Kfull ← match g.Kout? with
      | none => pure (quoteList K)
      | some Kout => mkAppM ``HAppend.hAppend #[quoteList K, Kout]
    let e' := mkApp2 (mkConst ``con_prob_lang.fill) Kfull (← instantiateMVars e1)
    let he ← mkExpectedTypeHint (← mkEqRefl g.e) (← mkEq g.e e')
    let hcont ← tpAddHyp g.hyps' g.name g.vid (g.frag g.j e') g.Q
    mvar.assign (← mkAppNamed ``tac_tp_bind
      [(`j, g.j), (`e', e1), (`K', Kfull), (`hsplit, g.pfSplit), (`he, he), (`hcont, hcont)])

/-- Rocq: `tp_pure_at j efoc` (with a pure-step search `find`). -/
public meta def tpPureCore (tacName : Name) (jStx : Syntax) (focus : Option Syntax)
    (failOnUnsolved : Bool) (find : Lean.Expr → ProofModeM PureStepRes) : TacticM Unit := do
  let focusE ← focus.mapM elabFocus
  runTacticTp tacName jStx fun mvar g => do
    let some (res, K, e1) ← reshapeExpr g.e0 fun _ e1 => do
        if let some f := focusE then guard (← isDefEq e1 f)
        find e1
      | throwError "{tacName}: cannot find a redex in {g.e0}"
    let hφ ← match res.hφ with
      | some hφ => pure hφ
      | none => gwpSolveSide res.φ failOnUnsolved
    let e0' ← gwpFill K res.e2
    let (upd, E, ψ, helim) ← findUpd g ``UpdPure (g.thread e0')
    let hψ ← tpSolveElimSide ψ
    let hcont ← tpThreadCont g.hyps' g e0' g.Q
    let pf ← mkAppNamed ``tac_tp_pure
      [(`upd, upd), (`j, g.j), (`Kout, g.Kout), (`K, quoteList K), (`e1, e1), (`e2, res.e2),
       (`E, E), (`hexec, res.inst), (`helim, helim), (`hsplit, g.pfSplit), (`hψ, hψ),
       (`hφ, hφ), (`hcont, hcont)]
    mvar.assign pf

/-- Rocq: `tp_pure_at j efoc`. Take a pure step in thread `j` at the first redex (following the
evaluation order) that unifies with the focus `efoc`. -/
elab "tp_pure_at " j:term:max ppSpace f:term:max : tactic =>
  tpPureCore `tp_pure j (some f) false findAnyPureExec

/-- Rocq: `tp_pure j`. -/
elab "tp_pure " j:term:max : tactic => tpPureCore `tp_pure j none false findAnyPureExec

/-- `tp_pure j` that fails if the side condition of the step cannot be solved. -/
elab "tp_pure_strict " j:term:max : tactic => tpPureCore `tp_pure j none true findAnyPureExec

/-- Rocq: `tp_pures j`. -/
macro "tp_pures " j:term:max : tactic => `(tactic| repeat tp_pure_strict $j)

/-- Rocq: `tp_rec j`. -/
elab "tp_rec " j:term:max : tactic => tpPureCore `tp_rec j none false findRecPureExec
/-- Rocq: `tp_seq j`. -/
macro "tp_seq " j:term:max : tactic => `(tactic| tp_rec $j)
/-- Rocq: `tp_let j`. -/
macro "tp_let " j:term:max : tactic => `(tactic| tp_rec $j)
/-- Rocq: `tp_lam j`. -/
macro "tp_lam " j:term:max : tactic => `(tactic| tp_rec $j)
/-- Rocq: `tp_fst j`. -/
macro "tp_fst " j:term:max : tactic =>
  `(tactic| tp_pure_at $j (expr.Fst (expr.Val (val.PairV _ _))))
/-- Rocq: `tp_snd j`. -/
macro "tp_snd " j:term:max : tactic =>
  `(tactic| tp_pure_at $j (expr.Snd (expr.Val (val.PairV _ _))))
/-- Rocq: `tp_proj j`. -/
macro "tp_proj " j:term:max : tactic => `(tactic| first | tp_fst $j | tp_snd $j)
/-- Rocq: `tp_case_inl j`. -/
macro "tp_case_inl " j:term:max : tactic =>
  `(tactic| tp_pure_at $j (expr.Case (expr.Val (val.InjLV _)) _ _))
/-- Rocq: `tp_case_inr j`. -/
macro "tp_case_inr " j:term:max : tactic =>
  `(tactic| tp_pure_at $j (expr.Case (expr.Val (val.InjRV _)) _ _))
/-- Rocq: `tp_case j`. -/
macro "tp_case " j:term:max : tactic => `(tactic| tp_pure_at $j (expr.Case _ _ _))
/-- Rocq: `tp_binop j`. -/
macro "tp_binop " j:term:max : tactic => `(tactic| tp_pure_at $j (expr.BinOp _ _ _))
/-- Rocq: `tp_op j`. -/
macro "tp_op " j:term:max : tactic => `(tactic| tp_binop $j)
/-- Rocq: `tp_if_true j`. -/
macro "tp_if_true " j:term:max : tactic =>
  `(tactic| tp_pure_at $j (expr.If (expr.Val (val.LitV (base_lit.LitBool true))) _ _))
/-- Rocq: `tp_if_false j`. -/
macro "tp_if_false " j:term:max : tactic =>
  `(tactic| tp_pure_at $j (expr.If (expr.Val (val.LitV (base_lit.LitBool false))) _ _))
/-- Rocq: `tp_if j`. -/
macro "tp_if " j:term:max : tactic => `(tactic| tp_pure_at $j (expr.If _ _ _))
/-- Rocq: `tp_pair j`. -/
macro "tp_pair " j:term:max : tactic => `(tactic| tp_pure_at $j (expr.Pair _ _))
/-- Rocq: `tp_closure j`. -/
macro "tp_closure " j:term:max : tactic => `(tactic| tp_pure_at $j (expr.Rec _ _ _))

/-! ### Heap, concurrency and tape tactics -/

/-- `P ∗ Q`. -/
public meta def mkSepE (P Q : Lean.Expr) : MetaM Lean.Expr := mkAppM ``BIBase.sep #[P, Q]

/-- Find a redex in the thread expression with `m`. -/
public meta def tpFindRedex {α} (tacName : Name) (what : String) (g : TpGoal)
    (m : Lean.Expr → Option α) : ProofModeM (α × List Lean.Expr) := do
  let some (r, K, _) ← reshapeExpr g.e0 fun _ e' => do
      let some r := m e'.consumeMData | failure
      return r
    | throwError "{tacName}: cannot find '{what}' in {g.e0}"
  return (r, K)

/-- Locate a points-to `l ↦ₛ{dq} v` in the remaining context. -/
public meta def tpLookupHeap {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {e : Q($prop)}
    (tacName : Name) (hyps : Hyps bi e) (g : TpGoal) (l v dq : Lean.Expr) :
    ProofModeM (Name × IVarId × (e'' : Q($prop)) × Hyps bi e'' × Lean.Expr) := do
  try tpLookupHyp hyps ``spec_heap_frag 2 l (g.heapFrag l v dq)
  catch _ => throwError "{tacName}: cannot find '{l} ↦ₛ ?'"

/-- The common part of the tactics updating one points-to: split off `P` (with pattern
`l ↦ₛ{dq} v`, whose metavariables `mvs` get instantiated), and build the lemma `lem` with the
new points-to `P' mvs` and the new thread expression `res mvs`. `extra` computes additional
arguments (side conditions). -/
public meta def tpHeapOp (tacName cls lem : Name) (g : TpGoal) (K : List Lean.Expr)
    (l : Lean.Expr) (mvs : Array Lean.Expr) (v dq : Lean.Expr)
    (newP : Array Lean.Expr → MetaM Lean.Expr) (res : Array Lean.Expr → MetaM Lean.Expr)
    (extra : Array Lean.Expr → ProofModeM (List (Name × Lean.Expr))) :
    ProofModeM Lean.Expr := do
  let ⟨name2, vid2, _, hyps3, pfSplit2⟩ ← tpLookupHeap tacName g.hyps' g l v dq
  let mvs ← mvs.mapM instantiateMVars
  let P' ← newP mvs
  let e0' ← gwpFill K (mkValE (← res mvs))
  let (upd, E, ψ, helim) ← findUpd g cls (← mkSepE P' (g.thread e0'))
  let hψ ← tpSolveElimSide ψ
  let extra ← extra mvs
  let hcont ← tpReaddCont hyps3 name2 vid2 P' g e0'
  mkAppNamed lem ([(`upd, upd), (`j, g.j), (`Kout, g.Kout), (`K, quoteList K), (`E, E),
    (`helim, helim), (`hψ, hψ), (`hsplit1, g.pfSplit), (`hsplit2, pfSplit2),
    (`hcont, hcont)] ++ extra)

/-- Match `Load (Val (LitV (LitLoc l)))`. -/
public meta def matchLoad? (e : Lean.Expr) : Option Lean.Expr := do
  let (``expr.Load, #[a]) := e.getAppFnArgs | none
  matchLocVal? a

/-- Match `Store (Val (LitV (LitLoc l))) (Val v)`. -/
public meta def matchStore? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let (``expr.Store, #[a1, a2]) := e.getAppFnArgs | none
  return (← matchLocVal? a1, ← isValExpr? a2)

/-- Match `Xchg (Val (LitV (LitLoc l))) (Val v)`. -/
public meta def matchXchg? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let (``expr.Xchg, #[a1, a2]) := e.getAppFnArgs | none
  return (← matchLocVal? a1, ← isValExpr? a2)

/-- Match `FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt z)))`. -/
public meta def matchFAA? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  let (``expr.FAA, #[a1, a2]) := e.getAppFnArgs | none
  return (← matchLocVal? a1, ← matchIntVal? a2)

/-- Match `CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)`. -/
public meta def matchCmpXchg? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let (``expr.CmpXchg, #[a0, a1, a2]) := e.getAppFnArgs | none
  return (← matchLocVal? a0, ← isValExpr? a1, ← isValExpr? a2)

/-- Match `AllocN (Val (LitV (LitInt 1))) (Val v)` (`Alloc (Val v)`). -/
public meta def matchAlloc? (e : Lean.Expr) : Option Lean.Expr := do
  let (``expr.AllocN, #[a1, a2]) := e.getAppFnArgs | none
  let n ← matchIntVal? a1
  guard (n == toExpr (1 : Int) || n.int? == some 1)
  isValExpr? a2

/-- Match `Fork e`. -/
public meta def matchFork? (e : Lean.Expr) : Option Lean.Expr := do
  let (``expr.Fork, #[a]) := e.getAppFnArgs | none
  return a

/-- Match `AllocTape (Val (LitV (LitInt z)))`. -/
public meta def matchAllocTape? (e : Lean.Expr) : Option Lean.Expr := do
  let (``expr.AllocTape, #[a]) := e.getAppFnArgs | none
  matchIntVal? a

/-- Rocq: `tp_load j`. -/
elab "tp_load " j:term:max : tactic =>
  runTacticTp `tp_load j fun mvar g => do
    let (l, K) ← tpFindRedex `tp_load "Load" g matchLoad?
    let v ← mkFreshExprMVar (mkConst ``val)
    let dq ← mkFreshExprMVar (mkConst ``DFrac)
    mvar.assign (← tpHeapOp `tp_load ``UpdHeap ``tac_tp_load g K l #[v, dq] v dq
      (fun m => pure (g.heapFrag l m[0]! m[1]!)) (fun m => pure m[0]!) (fun _ => pure []))

/-- Rocq: `tp_store j`. -/
elab "tp_store " j:term:max : tactic =>
  runTacticTp `tp_store j fun mvar g => do
    let ((l, v), K) ← tpFindRedex `tp_store "Store" g matchStore?
    let v' ← mkFreshExprMVar (mkConst ``val)
    let own1 ← dfracOwnOne
    mvar.assign (← tpHeapOp `tp_store ``UpdHeap ``tac_tp_store g K l #[v'] v' own1
      (fun _ => pure (g.heapFrag l v own1)) (fun _ => pure mkUnitV) (fun _ => pure []))

/-- Rocq: `tp_xchg j`. -/
elab "tp_xchg " j:term:max : tactic =>
  runTacticTp `tp_xchg j fun mvar g => do
    let ((l, v), K) ← tpFindRedex `tp_xchg "Xchg" g matchXchg?
    let v' ← mkFreshExprMVar (mkConst ``val)
    let own1 ← dfracOwnOne
    mvar.assign (← tpHeapOp `tp_xchg ``UpdAtomicConcurrency ``tac_tp_xchg g K l #[v'] v' own1
      (fun _ => pure (g.heapFrag l v own1)) (fun m => pure m[0]!) (fun _ => pure []))

/-- Rocq: `tp_faa j`. -/
elab "tp_faa " j:term:max : tactic =>
  runTacticTp `tp_faa j fun mvar g => do
    let ((l, z2), K) ← tpFindRedex `tp_faa "FAA" g matchFAA?
    let z1 ← mkFreshExprMVar (mkConst ``Int)
    let own1 ← dfracOwnOne
    mvar.assign (← tpHeapOp `tp_faa ``UpdAtomicConcurrency ``tac_tp_faa g K l #[z1]
      (mkIntV z1) own1
      (fun m => do
        let z12 ← gwpValSimpDefEq (← mkAppM ``HAdd.hAdd #[m[0]!, z2])
        pure (g.heapFrag l (mkIntV z12) own1))
      (fun m => pure (mkIntV m[0]!)) (fun m => pure [(`z1, m[0]!), (`z2, z2)]))

/-- Rocq: `tp_cmpxchg_fail j`. -/
elab "tp_cmpxchg_fail " j:term:max : tactic =>
  runTacticTp `tp_cmpxchg_fail j fun mvar g => do
    let ((l, v1, _), K) ← tpFindRedex `tp_cmpxchg_fail "CmpXchg" g matchCmpXchg?
    let v' ← mkFreshExprMVar (mkConst ``val)
    let dq ← mkFreshExprMVar (mkConst ``DFrac)
    mvar.assign (← tpHeapOp `tp_cmpxchg_fail ``UpdAtomicConcurrency ``tac_tp_cmpxchg_fail g K l
      #[v', dq] v' dq (fun m => pure (g.heapFrag l m[0]! m[1]!))
      (fun m => pure (mkPairBoolV m[0]! false))
      (fun m => do
        let hne ← gwpSolveSide (← mkAppM ``Ne #[m[0]!, v1]) false
        let hsafe ← gwpSolveSide (← mkAppM ``vals_compare_safe #[m[0]!, v1]) false
        pure [(`hne, hne), (`hsafe, hsafe)]))

/-- Rocq: `tp_cmpxchg_suc j`. -/
elab "tp_cmpxchg_suc " j:term:max : tactic =>
  runTacticTp `tp_cmpxchg_suc j fun mvar g => do
    let ((l, v1, v2), K) ← tpFindRedex `tp_cmpxchg_suc "CmpXchg" g matchCmpXchg?
    let v' ← mkFreshExprMVar (mkConst ``val)
    let own1 ← dfracOwnOne
    mvar.assign (← tpHeapOp `tp_cmpxchg_suc ``UpdAtomicConcurrency ``tac_tp_cmpxchg_suc g K l
      #[v'] v' own1 (fun _ => pure (g.heapFrag l v2 own1))
      (fun m => pure (mkPairBoolV m[0]! true))
      (fun m => do
        let heq ← gwpSolveSide (← mkEq m[0]! v1) false
        let hsafe ← gwpSolveSide (← mkAppM ``vals_compare_safe #[m[0]!, v1]) false
        pure [(`heq, heq), (`hsafe, hsafe)]))

/-- The common part of the allocation tactics: the new thread is `j ⤇ fill Kout (fill K #l)`
(with `mkV l` the value), the new resource `P l`. Builds the continuation
`∀ l, Δ' ∗ j ⤇ .. ⊢ P l -∗ Q`, introducing the location with the name `lName`. -/
public meta def tpAllocCont (g : TpGoal) (K : List Lean.Expr) (lName : Name)
    (P : Lean.Expr → Lean.Expr) (mkV : Lean.Expr → Lean.Expr) :
    ProofModeM (Lean.Expr × Lean.Expr) := do
  -- the eliminated proposition `∃ l, P l ∗ j ⤇ fill Kout (fill K #l)`
  let R' ← withLocalDeclD `l (mkConst ``Loc) fun l => do
    let body ← mkSepE (P l) (g.thread (← gwpFill K (mkValE (mkV l))))
    mkAppM ``BIBase.exists #[← mkLambdaFVars #[l] body]
  let hcont ← withLocalDeclD lName (mkConst ``Loc) fun l => do
    let Q' ← mkAppM ``BIBase.wand #[P l, g.Q]
    let pf ← tpThreadCont g.hyps' g (← gwpFill K (mkValE (mkV l))) Q'
    mkLambdaFVars #[l] pf
  return (R', hcont)

/-- The core of `tp_alloc j as l H` (Rocq: `tac_tp_alloc`): leaves the goal `l ↦ₛ v -∗ Q`
with the location `l` in the context. -/
elab "tp_alloc_core " j:term:max ppSpace l:ident : tactic =>
  runTacticTp `tp_alloc j fun mvar g => do
    let (v, K) ← tpFindRedex `tp_alloc "Alloc" g matchAlloc?
    let own1 ← dfracOwnOne
    let (R', hcont) ← tpAllocCont g K l.getId (fun l => g.heapFrag l v own1) mkLocV
    let (upd, E, ψ, helim) ← findUpd g ``UpdHeap R'
    let hψ ← tpSolveElimSide ψ
    mvar.assign (← mkAppNamed ``tac_tp_alloc
      [(`upd, upd), (`j, g.j), (`Kout, g.Kout), (`K, quoteList K), (`v, v), (`E, E),
       (`helim, helim), (`hψ, hψ), (`hsplit, g.pfSplit), (`hcont, hcont)])

/-- Rocq: `tp_alloc j as l "H"`. -/
syntax "tp_alloc " term:max " as " ident (ppSpace colGt introPat)? : tactic

macro_rules
  | `(tactic| tp_alloc $j as $l:ident $pat:introPat) =>
    `(tactic| focus (tp_alloc_core $j $l; iintro $pat:introPat))
  | `(tactic| tp_alloc $j as $l:ident) => `(tactic| focus (tp_alloc_core $j $l; iintro _))

/-- The core of `tp_allocnattape j α as H` (Rocq: `tac_tp_allocnattape`). -/
elab "tp_allocnattape_core " j:term:max ppSpace l:ident : tactic =>
  runTacticTp `tp_allocnattape j fun mvar g => do
    let (z, K) ← tpFindRedex `tp_allocnattape "AllocTape" g matchAllocTape?
    let N ← gwpValSimpDefEq (← mkAppM ``Int.toNat #[z])
    let nil ← mkAppOptM ``List.nil #[mkConst ``Nat]
    let (R', hcont) ← tpAllocCont g K l.getId
      (fun l => mkApp5 (mkConst ``nat_spec_tape) g.GF g.S l N nil) mkLblV
    let (upd, E, ψ, helim) ← findUpd g ``UpdTapes R'
    let hψ ← tpSolveElimSide ψ
    let hN ← gwpSolveSide (← mkEq N (← mkAppM ``Int.toNat #[z])) false
    mvar.assign (← mkAppNamed ``tac_tp_allocnattape
      [(`upd, upd), (`j, g.j), (`Kout, g.Kout), (`K, quoteList K), (`N, N), (`z, z), (`E, E),
       (`helim, helim), (`hψ, hψ), (`hN, hN), (`hsplit, g.pfSplit), (`hcont, hcont)])

/-- Rocq: `tp_allocnattape j α as "H"` and `tp_allocnattape j α`. -/
syntax "tp_allocnattape " term:max ppSpace ident (" as " introPat)? : tactic

macro_rules
  | `(tactic| tp_allocnattape $j $l:ident as $pat:introPat) =>
    `(tactic| focus (tp_allocnattape_core $j $l; iintro $pat:introPat))
  | `(tactic| tp_allocnattape $j $l:ident) =>
    `(tactic| focus (tp_allocnattape_core $j $l; iintro _))

/-- Rocq: `tp_fork j`. Leaves the goal `∀ j', j' ⤇ e' -∗ Q` for the forked thread `e'`. -/
elab "tp_fork " j:term:max : tactic =>
  runTacticTp `tp_fork j fun mvar g => do
    let (ef, K) ← tpFindRedex `tp_fork "Fork" g matchFork?
    let e0' ← gwpFill K (mkValE mkUnitV)
    let R' ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      let body ← mkSepE (g.frag k ef) (g.thread e0')
      mkAppM ``BIBase.exists #[← mkLambdaFVars #[k] body]
    let (upd, E, ψ, helim) ← findUpd g ``UpdAtomicConcurrency R'
    let hψ ← tpSolveElimSide ψ
    let Q' ← withLocalDeclD `j' (mkConst ``Nat) fun k => do
      let body ← mkAppM ``BIBase.wand #[g.frag k ef, g.Q]
      mkAppM ``BIBase.forall #[← mkLambdaFVars #[k] body]
    let hcont ← tpThreadCont g.hyps' g e0' Q'
    mvar.assign (← mkAppNamed ``tac_tp_fork
      [(`upd, upd), (`j, g.j), (`Kout, g.Kout), (`K, quoteList K), (`e', ef), (`E, E),
       (`helim, helim), (`hψ, hψ), (`hsplit, g.pfSplit), (`hcont, hcont)])

/-- Rocq: `tp_fork j as j' "H"` and `tp_fork j as j'`. -/
macro "tp_fork " j:term:max " as " k:ident pat:(ppSpace colGt introPat)? : tactic =>
  match pat with
  | some pat => `(tactic| focus (tp_fork $j; iintro %$k:ident $pat:introPat))
  | none => `(tactic| focus (tp_fork $j; iintro %$k:ident _))

end meta_tactics

end ConProbLang
