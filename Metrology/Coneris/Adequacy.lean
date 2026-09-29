module

public import Metrology.Coneris.PrimitiveLaws

/-!
# Adequacy of Coneris

Ported from clutch/theories/coneris/adequacy.v

The two adequacy theorems of Coneris: `wp_pgl_lim` (a WP with `↯ ε` bounds the probability of
the limit execution under a tape-oblivious scheduler returning a value violating `φ` by `ε`)
and `wp_safety` (for schedulers of mass one, the program runs `n` steps with probability at
least `1 - ε`).

## Design choices (Rocq → Lean)

* Errors are `ℝ≥0∞` (Rocq: `R`/`nonnegreal`): the hypotheses `0 <= ε` of `pgl_dbind'`,
  `safety_dbind'`, `wp_pgl_multi`, `wp_pgl`, `wp_pgl_lim`, `wp_safety_multi`, `wp_safety` are
  dropped. The bounds `⌜∃ r, ∀ a, ε2 a ≤ r⌝` are kept for fidelity (they are trivial in `ℝ≥0∞`).
* `SeriesC μ` is `∑' a, μ a`; the Rocq `SeriesC μ >= 1 - ε` is `1 - ε ≤ ∑' a, μ a`, with the
  truncated subtraction of `ℝ≥0∞`.
* Scheduler states live in `Type` with `[DecidableEq] [Countable]` (Rocq: `Countable`, which
  bundles `EqDecision`), since the erasability hypotheses of `state_step_coupl` are for
  schedulers in `Type` (`tape_oblivious_sch`).
* `λ '(e3, σ3, efs), ..` is written with projections `t.1`, `t.2.1`, `t.2.2`, and
  `<[num:=e3]> es` is `es.set num e3`, as in `Metrology.ConProbLang.Erasure`.
* `|={∅}▷=>^n P` is iris-lean's `|={∅}[∅]▷=>^[n] P`.
* The Rocq proofs move pure conclusions under `|={∅}=> |={∅}▷=>^n` through universal
  quantifiers using clutch's `iris_ext` `FromForall` instances; here this is done by the helpers
  `fupd_step_fupdN_pure_forall` / `fupd_step_fupdN_pure_forall_imp`.
* `wp_pgl_multi` and `wp_safety_multi` take `Hwp : ∀ [conerisGS GF], ⊢@{IProp GF} ↯ ε -∗ ..` (Rocq:
  `∀ `{conerisGS Σ}, ..`), and run the soundness of the step-indexed fancy update
  `step_fupdN_soundness` with `hlc := .hasNoLC` (Rocq: `step_fupdN_soundness_no_lc`).

## Omitted
* `conerisΣ` and `subG_conerisGPreS`: iris-lean has no `gFunctors` lists / `subG`; the
  `ElemG` instances of a `BundledGFunctors` are found by typeclass synthesis (as for iris-lean's
  `heapGpreS`).

## Added helpers (not in Rocq)
* Generic step-fupd facts (they belong in iris-lean): `fupd_laterN_to_step_fupdN`,
  `step_fupdN_except_0`, `fupd_step_fupdN_plain_forall`, `fupd_step_fupdN_pure_forall`,
  `fupd_step_fupdN_pure_forall_imp`, `fupd_pure_forall`, `fupd_pure_forall_imp`.
* Generic `ℝ≥0∞`/`Distr` facts (they belong in `Prob`): `one_sub_le_of_forall_lt`,
  `dmap_dbind_dret_dbind`.
* Facts about the MDP of `con_prob_lang` (they belong in `ConProbLang`):
  `con_prob_lang_to_final_cons`, `con_prob_lang_mdp_step_stutter`, `con_prob_lang_mdp_step_prim`
  (the Rocq proofs do this case analysis inline).
* `pgl_wp_unfold_none` (`pgl_wp_unfold` specialised to a non-value) is used here but lives in
  `Metrology.Coneris.Weakestpre`.
* The thread-pool bookkeeping of `wp_refRcoupl_step_fupdN`/`wp_safety_step_fupdN` uses
  `BigSepL.bigSepL_insert_acc` instead of Rocq's `list_elem_of_split_length` split.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris

/-- Rocq: `con_prob_lang_mdp`. -/
abbrev con_prob_lang_mdp := con_lang_mdp con_prob_lang

/-! ## Local helpers -/

section helpers

variable {GF : BundledGFunctors} [InvGS_gen .hasNoLC GF]

/-- Helper: a fancy update of `n + 1` laters is an `(n + 1)`-step fancy update. -/
theorem fupd_laterN_to_step_fupdN (E : CoPset) (n : ℕ) {Q : IProp GF} :
    (|={E}=> ▷^[n+1] Q) ⊢ |={E}[E]▷=>^[n+1] Q :=
  (BIFUpdate.mono (step_fupdN_intro LawfulSet.subset_refl)).trans BIFUpdate.trans

/-- Helper: an except-0 under `n + 1` step fancy updates can be dropped. -/
theorem step_fupdN_except_0 (E1 E2 : CoPset) {P : IProp GF} (n : ℕ) :
    (|={E1}[E2]▷=>^[n+1] ◇ P) ⊢ |={E1}[E2]▷=>^[n+1] P :=
  calc
    _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> ◇ P := (step_fupdN_add (n := n) (m := 1)).mp
    _ ⊢ |={E1}[E2]▷=>^[n] |={E1}[E2]▷=> P := step_fupdN_mono (BIFUpdate.mono (later_mono fupd_except0))
    _ ⊢ |={E1}[E2]▷=>^[n+1] P := (step_fupdN_add (n := n) (m := 1)).mpr

/-- Helper (clutch `iris_ext`): commuting a plain universal quantifier with
`|={∅}=> |={∅}▷=>^n`. -/
theorem fupd_step_fupdN_plain_forall {A : Type _} (Φ : A → IProp GF) [∀ x, Plain (Φ x)] (n : ℕ) :
    (∀ x, |={∅}=> |={∅}[∅]▷=>^[n] Φ x) ⊢ |={∅}=> |={∅}[∅]▷=>^[n] ∀ x, Φ x := by
  cases n with
  | zero =>
    simp only [Nat.repeat]
    exact (fupd_plain_forall LawfulSet.subset_refl).mpr
  | succ n =>
    calc
      _ ⊢ ∀ x, |={∅}=> ▷^[n+1] ◇ Φ x :=
          forall_mono fun _ => (BIFUpdate.mono step_fupdN_plain).trans BIFUpdate.trans
      _ ⊢ |={∅}=> ∀ x, ▷^[n+1] ◇ Φ x := (fupd_plain_forall LawfulSet.subset_refl).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ∀ x, ◇ Φ x := BIFUpdate.mono (laterN_forall (n+1)).mpr
      _ ⊢ |={∅}=> ▷^[n+1] ◇ ∀ x, Φ x := BIFUpdate.mono (laterN_mono (n+1) except0_forall.mpr)
      _ ⊢ |={∅}[∅]▷=>^[n+1] ◇ ∀ x, Φ x := fupd_laterN_to_step_fupdN ∅ n
      _ ⊢ |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := step_fupdN_except_0 ∅ ∅ n
      _ ⊢ |={∅}=> |={∅}[∅]▷=>^[n+1] ∀ x, Φ x := fupd_intro

/-- Helper: a pure consequence of pure conclusions under `|={∅}=> |={∅}▷=>^n`, for all `x`. -/
theorem fupd_step_fupdN_pure_forall {A : Type _} {q : A → Prop} {r : Prop} (n : ℕ)
    (h : (∀ x, q x) → r) :
    (∀ x, |={∅}=> |={∅}[∅]▷=>^[n] ⌜q x⌝) ⊢@{IProp GF} |={∅}=> |={∅}[∅]▷=>^[n] ⌜r⌝ :=
  (fupd_step_fupdN_plain_forall (fun x => iprop(⌜q x⌝)) n).trans
    (BIFUpdate.mono (step_fupdN_mono (pure_forall.2.trans (pure_mono h))))

/-- Helper: as `fupd_step_fupdN_pure_forall`, with a pure premise for each `x`. -/
theorem fupd_step_fupdN_pure_forall_imp {A : Type _} {p q : A → Prop} {r : Prop} (n : ℕ)
    (h : (∀ x, p x → q x) → r) :
    (∀ x, ⌜p x⌝ -∗ |={∅}=> |={∅}[∅]▷=>^[n] ⌜q x⌝) ⊢@{IProp GF} |={∅}=> |={∅}[∅]▷=>^[n] ⌜r⌝ := by
  iintro H
  iapply fupd_step_fupdN_pure_forall (q := fun x => p x → q x) n h
  iintro %x
  by_cases hx : p x
  · imod H $$ %x %hx with H
    imodintro
    iapply step_fupdN_mono (pure_mono fun hq _ => hq) $$ H
  · iclear H
    imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    exact fun hx' => absurd hx' hx

/-- Helper: `fupd_step_fupdN_pure_forall` without steps. -/
theorem fupd_pure_forall {A : Type _} {q : A → Prop} {r : Prop} (h : (∀ x, q x) → r) :
    (∀ x, |={∅}=> ⌜q x⌝) ⊢@{IProp GF} |={∅}=> ⌜r⌝ :=
  fupd_step_fupdN_pure_forall 0 h

/-- Helper: `fupd_step_fupdN_pure_forall_imp` without steps. -/
theorem fupd_pure_forall_imp {A : Type _} {p q : A → Prop} {r : Prop} (h : (∀ x, p x → q x) → r) :
    (∀ x, ⌜p x⌝ -∗ |={∅}=> ⌜q x⌝) ⊢@{IProp GF} |={∅}=> ⌜r⌝ :=
  fupd_step_fupdN_pure_forall_imp 0 h

end helpers

/-- Helper: `1 - ε ≤ S` follows from `1 - ε' ≤ S` for all `ε' > ε`. -/
theorem one_sub_le_of_forall_lt {ε S : ℝ≥0∞} (h : ∀ ε', ε < ε' → 1 - ε' ≤ S) : 1 - ε ≤ S := by
  rw [tsub_le_iff_right]
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hS : S ≠ ∞ := ne_top_of_lt (lt_of_le_of_lt le_self_add hc)
  have hlt : ε < c - S := (ENNReal.cancel_of_ne hS).lt_tsub_iff_left.2 hc
  have := h _ hlt
  rw [tsub_le_iff_right] at this
  refine this.trans (le_of_eq ?_)
  rw [add_tsub_cancel_of_le (le_self_add.trans hc.le)]

/-- Helper: the final value of a configuration is the value of its main thread. -/
theorem con_prob_lang_to_final_cons (e : expr) (es : List expr) (σ : state) :
    con_prob_lang_mdp.to_final (e :: es, σ) = to_val e := rfl

/-- Helper: a `dmap` of a deterministic continuation, followed by a bind. -/
theorem dmap_dbind_dret_dbind {α β γ δ : Type _} [Countable α] [Countable β] [Countable γ]
    [Countable δ] (F : β → γ) (G : α → β) (μ : Distr α) (g : γ → Distr δ) :
    (dmap F (μ ≫= fun a => dret (G a)) ≫= g) = μ ≫= fun a => g (F (G a)) := by
  rw [dmap, ← dbind_assoc, ← dbind_assoc]
  refine dbind_ext_right _ _ _ fun a => ?_
  rw [dret_id_left, dret_id_left]

section sch_step_helpers

variable {sch_int_state X : Type} [Countable sch_int_state] [Countable X]

/-- Helper: stepping a thread that is out of bounds, or a value, stutters. -/
theorem con_prob_lang_mdp_step_stutter (e : expr) (es : List expr) (σ : state)
    (sch_σ : sch_int_state) (k : ℕ) (g : sch_int_state × con_prob_lang_mdp.mdpstate → Distr X)
    (Hv : to_val e = none)
    (Hk : (e :: es)[k]? = none ∨ ∃ e' v, (e :: es)[k]? = some e' ∧ to_val e' = some v) :
    (dmap (fun c => (sch_σ, c)) (con_prob_lang_mdp.step k (e :: es, σ)) ≫= g) =
      g (sch_σ, (e :: es, σ)) := by
  have Hv : ConProbLang.to_val (Λ := con_prob_lang) e = none := Hv
  rcases Hk with Hk | ⟨e', v, Hk, Hv'⟩
  · simp only [con_lang_mdp_step_eq, con_lang_mdp_step, List.getElem?_cons_zero,
      Option.bind_eq_bind, Option.bind_some, Hv, Hk]
    exact (congrArg (· ≫= g) (dmap_dret _ _)).trans (dret_id_left _ _)
  · have Hv' : ConProbLang.to_val (Λ := con_prob_lang) e' = some v := Hv'
    simp only [con_lang_mdp_step_eq, con_lang_mdp_step, List.getElem?_cons_zero,
      Option.bind_eq_bind, Option.bind_some, Hv, Hk, Hv']
    exact (congrArg (· ≫= g) (dmap_dret _ _)).trans (dret_id_left _ _)

/-- Helper: stepping a thread that is not a value takes a `prim_step` of it. -/
theorem con_prob_lang_mdp_step_prim (e : expr) (es : List expr) (e' : expr) (σ : state)
    (sch_σ : sch_int_state) (k : ℕ) (g : sch_int_state × con_prob_lang_mdp.mdpstate → Distr X)
    (Hv : to_val e = none) (Hk : (e :: es)[k]? = some e') (Hv' : to_val e' = none) :
    (dmap (fun c => (sch_σ, c)) (con_prob_lang_mdp.step k (e :: es, σ)) ≫= g) =
      prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
        g (sch_σ, ((e :: es).set k t.1 ++ t.2.2, t.2.1)) := by
  have Hv : ConProbLang.to_val (Λ := con_prob_lang) e = none := Hv
  have Hv' : ConProbLang.to_val (Λ := con_prob_lang) e' = none := Hv'
  simp only [con_lang_mdp_step_eq, con_lang_mdp_step, List.getElem?_cons_zero,
    Option.bind_eq_bind, Option.bind_some, Hv, Hk, Hv']
  exact dmap_dbind_dret_dbind _ _ _ _


end sch_step_helpers

/-! ## Normal adequacy -/

section adequacy

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `step_fupd_fupdN_S`. -/
theorem step_fupd_fupdN_S (n : ℕ) (P : IProp GF) :
    (|={∅}[∅]▷=>^[n+1] P) ⊣⊢ |={∅}=> |={∅}[∅]▷=>^[n+1] P :=
  ⟨fupd_intro, BIFUpdate.trans⟩

/-- Rocq: `pgl_dbind'`. The hypothesis `0 <= ε'` is dropped. -/
theorem pgl_dbind' {A A' : Type _} [Countable A] [Countable A'] (f : A → Distr A') (μ : Distr A)
    (T : A' → Prop) (ε' : ℝ≥0∞) (n : ℕ) :
    ⊢@{IProp GF} (∀ a, |={∅}=> |={∅}[∅]▷=>^[n] ⌜pgl (f a) T ε'⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜pgl (dbind f μ) T ε'⌝ := by
  iintro H
  iapply fupd_step_fupdN_pure_forall n fun h => Prob.pgl_dbind' f μ T ε' fun a _ => h a
  iexact H

/-- Rocq: `pgl_dbind_adv'`. -/
theorem pgl_dbind_adv' {A A' : Type _} [Countable A] [Countable A'] (f : A → Distr A')
    (μ : Distr A) (T : A' → Prop) (ε' : A → ℝ≥0∞) (n : ℕ) :
    ⊢@{IProp GF} ⌜∃ r, ∀ a, ε' a ≤ r⌝ -∗
      (∀ a, |={∅}=> |={∅}[∅]▷=>^[n] ⌜pgl (f a) T (ε' a)⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜pgl (dbind f μ) T (Expval μ ε')⌝ := by
  iintro - H
  iapply fupd_step_fupdN_pure_forall (r := pgl (dbind f μ) T (Expval μ ε')) n
    (pgl_dbind_adv_aux f μ T ε')
  iexact H

variable {sch_int_state : Type} [DecidableEq sch_int_state] [Countable sch_int_state]

/-- Rocq: `wp_adequacy_val_fupd`. -/
theorem wp_adequacy_val_fupd (ζ : sch_int_state) (e : expr) (es : List expr)
    (sch : scheduler con_prob_lang_mdp sch_int_state) (n : ℕ) (v : val) (σ : state)
    (ε : ℝ≥0∞) (φ : val → Prop) [TapeOblivious sch_int_state sch] (Hval : to_val e = some v) :
    (state_interp σ : IProp GF) ∗ err_interp ε ∗ WP e {{ v, ⌜φ v⌝ }} ⊢
      |={⊤, ∅}=> ⌜pgl (sch_exec sch n (ζ, (Val v :: es, σ))) φ ε⌝ := by
  obtain rfl : e = Val v := (of_to_val (Λ := con_prob_lang) e v Hval).symm
  rw [pgl_wp_unfold]
  simp only [pgl_wp_pre, to_val_Val]
  iintro ⟨Hσ, Hε, Hwp⟩
  imod Hwp $$ %σ %ε [Hσ Hε] with H
  · iframe
  iapply state_step_coupl_ind
    (fun σ ε => iprop(|={∅}=> ⌜pgl (sch_exec sch n (ζ, (Val v :: es, σ))) φ ε⌝)) _
    $$ [] %σ %ε H
  iintro !> %σ' %ε' H
  icases H with (%H | H | H | ⟨%μ, %ε2, %Herasable, %Hr, %Hineq, H⟩)
  · imodintro
    ipureintro
    exact pgl_1 _ _ _ H
  · imod H with ⟨-, -, %Hφ⟩
    iapply fupd_mask_intro_discard LawfulSet.empty_subset
    ipureintro
    rw [sch_exec_is_final sch _ v n rfl]
    exact pgl_mon_grading _ _ _ _ zero_le (pgl_dret v φ Hφ)
  · iapply fupd_pure_forall_imp (pgl_epsilon_limit (sch_exec sch n (ζ, (Val v :: es, σ'))) φ ε')
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨H, -⟩
    iexact H
  · dsimp only at Herasable Hineq
    rw [← sch_erasable_sch_erasable_val tape_oblivious_sch μ σ' Herasable sch_int_state sch
      (Val v :: es) ζ n inferInstance]
    iapply fupd_pure_forall fun h => pgl_mon_grading _ _ _ _ Hineq
      (pgl_dbind_adv_aux (fun σ2 => sch_exec sch n (ζ, (Val v :: es, σ2))) μ φ ε2 h)
    iintro %σ2
    imod H $$ %σ2 with ⟨H, -⟩
    iexact H

/-- Rocq: `state_step_coupl_erasure`. -/
theorem state_step_coupl_erasure (ζ : sch_int_state) (es : List expr) (σ : state) (ε : ℝ≥0∞)
    (Z : state → ℝ≥0∞ → IProp GF) (n : ℕ) (sch : scheduler con_prob_lang_mdp sch_int_state)
    (φ : val → Prop) [TapeOblivious sch_int_state sch] :
    ⊢ state_step_coupl σ ε Z -∗
      (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n]
        ⌜pgl (sch_exec sch n (ζ, (es, σ2))) φ ε2⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜pgl (sch_exec sch n (ζ, (es, σ))) φ ε⌝ := by
  iintro H Hcont
  iapply state_step_coupl_ind
    (fun σ ε => iprop((∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n]
        ⌜pgl (sch_exec sch n (ζ, (es, σ2))) φ ε2⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜pgl (sch_exec sch n (ζ, (es, σ))) φ ε⌝)) Z
    $$ [] %σ %ε H Hcont
  iintro !> %σ' %ε' H Hcont
  icases H with (%H | H | H | ⟨%μ, %ε2, %Herasable, %Hr, %Hineq, H⟩)
  · imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    exact pgl_1 _ _ _ H
  · iapply Hcont $$ H
  · iapply fupd_step_fupdN_pure_forall_imp n
      (pgl_epsilon_limit (sch_exec sch n (ζ, (es, σ'))) φ ε')
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨H, -⟩
    iapply H $$ Hcont
  · dsimp only at Herasable Hineq
    rw [← sch_erasable_sch_erasable_val tape_oblivious_sch μ σ' Herasable sch_int_state sch
      es ζ n inferInstance]
    iapply fupd_step_fupdN_pure_forall n fun h => pgl_mon_grading _ _ _ _ Hineq
      (pgl_dbind_adv_aux (fun σ2 => sch_exec sch n (ζ, (es, σ2))) μ φ ε2 h)
    iintro %σ2
    imod H $$ %σ2 with ⟨H, -⟩
    iapply H $$ Hcont

/-- Rocq: `state_step_coupl_erasure'`. -/
theorem state_step_coupl_erasure' (ζ : sch_int_state) (e : expr) (es : List expr) (e' : expr)
    (σ : state) (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) (n num : ℕ)
    (sch : scheduler con_prob_lang_mdp sch_int_state) (φ : val → Prop)
    [TapeOblivious sch_int_state sch]
    (Hlookup : (e :: es)[num]? = some e') (Hv : to_val e = none) (Hv' : to_val e' = none) :
    ⊢ state_step_coupl σ ε Z -∗
      (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n+1]
        ⌜pgl (prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
          sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) φ ε2⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n+1]
        ⌜pgl (prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
          sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) φ ε⌝ := by
  iintro H Hcont
  iapply state_step_coupl_ind
    (fun σ ε => iprop((∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n+1]
        ⌜pgl (prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
          sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) φ ε2⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n+1]
        ⌜pgl (prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
          sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) φ ε⌝)) Z
    $$ [] %σ %ε H Hcont
  iintro !> %σ' %ε' H Hcont
  icases H with (%H | H | H | ⟨%μ, %ε2, %Herasable, %Hr, %Hineq, H⟩)
  · imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    exact pgl_1 _ _ _ H
  · iapply Hcont $$ H
  · iapply fupd_step_fupdN_pure_forall_imp (n+1)
      (pgl_epsilon_limit (prim_step (Λ := con_prob_lang) e' σ' ≫= fun t =>
          sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) φ ε')
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨H, -⟩
    iapply H $$ Hcont
  · dsimp only at Herasable Hineq
    rw [Rcoupl_eq_elim _ _ (prim_coupl_step_prim_sch_erasable e n es σ' ζ e' num μ Herasable
      Hlookup Hv Hv')]
    iapply fupd_step_fupdN_pure_forall (n+1) fun h => pgl_mon_grading _ _ _ _ Hineq
      (pgl_dbind_adv_aux (fun σ2 => prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
          sch_exec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) μ φ ε2 h)
    iintro %σ2
    imod H $$ %σ2 with ⟨H, -⟩
    iapply H $$ Hcont

/-- Rocq: `wp_refRcoupl_step_fupdN`. -/
theorem wp_refRcoupl_step_fupdN (ζ : sch_int_state) (ε : ℝ≥0∞) (e : expr) (es : List expr)
    (σ : state) (n : ℕ) (φ : val → Prop) (sch : scheduler con_prob_lang_mdp sch_int_state)
    [TapeOblivious sch_int_state sch] :
    (state_interp σ : IProp GF) ∗ err_interp ε ∗ WP e {{ v, ⌜φ v⌝ }} ∗
        ([∗list] e' ∈ es, WP e' {{ _v, True }}) ⊢
      |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜pgl (sch_exec sch n (ζ, (e :: es, σ))) φ ε⌝ := by
  induction n generalizing ζ ε e es σ with
  | zero =>
    simp only [Nat.repeat]
    cases Heq : to_val e with
    | some v =>
      obtain rfl : e = Val v := (of_to_val (Λ := con_prob_lang) e v Heq).symm
      iintro ⟨Hσ, Hε, Hwp, -⟩
      iapply wp_adequacy_val_fupd ζ (Val v) es sch 0 v σ ε φ rfl
      iframe
    | none =>
      iintro -
      iapply fupd_mask_intro_discard LawfulSet.empty_subset
      ipureintro
      rw [sch_exec_O_not_final _ _ (to_final_None_2 _ Heq)]
      exact pgl_dzero _ _
  | succ n IH =>
    cases Heq : to_val e with
    | some v =>
      obtain rfl : e = Val v := (of_to_val (Λ := con_prob_lang) e v Heq).symm
      iintro ⟨Hσ, Hε, Hwp, -⟩
      imod wp_adequacy_val_fupd ζ (Val v) es sch (n+1) v σ ε φ rfl $$ [Hσ Hε Hwp] with %H
      · iframe
      imodintro
      iapply step_fupdN_intro LawfulSet.subset_refl
      iapply laterN_intro
      ipureintro
      exact H
    | none =>
      rw [sch_exec_Sn_not_final _ _ _ (to_final_None_2 _ Heq), sch_step, ← dbind_assoc]
      dsimp only
      iintro ⟨Hσ, Hε, Hwp, Hwps⟩
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hclose
      iapply (step_fupd_fupdN_S n _).2
      iapply pgl_dbind' (fun a => dmap (fun mdp_σ' => (a.1, mdp_σ'))
        (con_prob_lang_mdp.step a.2 (e :: es, σ)) ≫= sch_exec sch n) (sch (ζ, (e :: es, σ))) φ ε
        (n+1)
      iintro %⟨sch_σ, k⟩
      imod Hclose
      change ℕ at k
      cases Hk : (e :: es)[k]? with
      | none =>
        -- step a thread that is out of bounds
        rw [con_prob_lang_mdp_step_stutter e es σ sch_σ k _ Heq (.inl Hk)]
        iapply fupd_mask_intro LawfulSet.empty_subset
        iintro Hclose
        simp only [Nat.repeat]
        iintro !> !>
        imod Hclose
        iapply IH sch_σ ε e es σ
        iframe
      | some e' =>
        cases Hv' : to_val e' with
        | some v =>
          -- step a thread that is a value
          rw [con_prob_lang_mdp_step_stutter e es σ sch_σ k _ Heq (.inr ⟨e', v, Hk, Hv'⟩)]
          iapply fupd_mask_intro LawfulSet.empty_subset
          iintro Hclose
          simp only [Nat.repeat]
          iintro !> !>
          imod Hclose
          iapply IH sch_σ ε e es σ
          iframe
        | none =>
          rw [con_prob_lang_mdp_step_prim e es e' σ sch_σ k _ Heq Hk Hv']
          cases k with
          | zero =>
            -- step the main thread
            obtain rfl : e = e' := Option.some.inj Hk
            imod pgl_wp_unfold_none Heq $$ Hwp %σ %ε [Hσ Hε] with Hlift
            · iframe
            iapply state_step_coupl_erasure' sch_σ e es e σ ε _ n 0 sch φ rfl Heq Heq $$ Hlift
            iintro %σ2 %ε2 ⟨%ε3, %Hred, %Hr, %Hineq, H⟩
            iapply fupd_step_fupdN_pure_forall (n+1) fun h => pgl_mon_grading _ _ _ _ Hineq
              (pgl_dbind_adv_aux (fun t => sch_exec sch n (sch_σ, ((e :: es).set 0 t.1 ++ t.2.2,
                t.2.1))) (prim_step (Λ := con_prob_lang) e σ2) φ ε3 h)
            iintro %⟨e3, σ3, efs⟩
            imod H $$ %e3 %σ3 %efs with H
            simp only [Nat.repeat]
            iintro !> !> !>
            iapply state_step_coupl_erasure $$ H
            iintro %σ4 %ε4 H
            imod H with ⟨Hσ, Hε, Hwp, Hefs⟩
            simp only [List.set_cons_zero, List.cons_append]
            iapply IH sch_σ ε4 e3 (es ++ efs) σ4
            iframe Hσ Hε Hwp
            iapply BigSepL.bigSepL_append.2
            iframe
          | succ k =>
            -- step another thread
            have Hk' : es[k]? = some e' := by simpa using Hk
            icases BigSepL.bigSepL_insert_acc (Φ := fun _ e' => iprop(WP e' {{ _v, True }})) Hk'
              $$ Hwps with ⟨Hwp', Hwps⟩
            imod pgl_wp_unfold_none Hv' $$ Hwp' %σ %ε [Hσ Hε] with Hlift
            · iframe
            iapply state_step_coupl_erasure' sch_σ e es e' σ ε _ n (k+1) sch φ Hk Heq Hv' $$ Hlift
            iintro %σ2 %ε2 ⟨%ε3, %Hred, %Hr, %Hineq, H⟩
            iapply fupd_step_fupdN_pure_forall (n+1) fun h => pgl_mon_grading _ _ _ _ Hineq
              (pgl_dbind_adv_aux (fun t => sch_exec sch n (sch_σ, ((e :: es).set (k+1) t.1 ++ t.2.2,
                t.2.1))) (prim_step (Λ := con_prob_lang) e' σ2) φ ε3 h)
            iintro %⟨e3, σ3, efs⟩
            imod H $$ %e3 %σ3 %efs with H
            simp only [Nat.repeat]
            iintro !> !> !>
            iapply state_step_coupl_erasure $$ H
            iintro %σ4 %ε4 H
            imod H with ⟨Hσ, Hε, Hwp', Hefs⟩
            simp only [List.set_cons_succ, List.cons_append]
            iapply IH sch_σ ε4 e (es.set k e3 ++ efs) σ4
            iframe Hσ Hε Hwp
            iapply BigSepL.bigSepL_append.2
            iframe Hefs
            iapply Hwps $$ Hwp'

end adequacy

/-- Rocq: `conerisGpreS`. -/
class conerisGpreS (GF : BundledGFunctors) where
  conerisGpreS_iris : InvGpreS GF
  conerisGpreS_heap : GhostMapG GF Loc val loc_map
  conerisGpreS_tapes : GhostMapG GF Loc tape loc_map
  conerisGpreS_err : ECPreGS GF

attribute [reducible, instance] conerisGpreS.conerisGpreS_iris conerisGpreS.conerisGpreS_heap
  conerisGpreS.conerisGpreS_tapes conerisGpreS.conerisGpreS_err

section pgl_adequacy

variable {GF : BundledGFunctors} {sch_int_state : Type} [DecidableEq sch_int_state]
  [Countable sch_int_state]

/-- Rocq: `wp_pgl_multi`. The hypothesis `0 <= ε` is dropped. -/
theorem wp_pgl_multi [conerisGpreS GF] (ζ : sch_int_state) (n : ℕ) (e : expr) (es : List expr)
    (σ : state) (ε : ℝ≥0∞) (sch : scheduler con_prob_lang_mdp sch_int_state) (φ : val → Prop)
    [TapeOblivious sch_int_state sch]
    (Hwp : ∀ [conerisGS GF],
      ⊢@{IProp GF} ↯ ε -∗ (WP e {{ v, ⌜φ v⌝ }} ∗ [∗list] e' ∈ es, WP e' {{ _v, True }})) :
    pgl (sch_exec sch n (ζ, (e :: es, σ))) φ ε := by
  -- Handle the trivial `1 ≤ ε` case
  by_cases hε : 1 ≤ ε
  · exact pgl_1 _ _ _ hε
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 fun Hinv => ?_
  iintro -
  imod ghost_map_alloc (GF := GF) (H := loc_map) σ.heap with ⟨%γH, Hh, -⟩
  imod ghost_map_alloc (GF := GF) (H := loc_map) σ.tapes with ⟨%γT, Ht, -⟩
  imod ec_alloc ε (lt_of_not_ge hε) with ⟨%γec, HecAuth, Hec⟩
  let HconerisGS : conerisGS GF :=
    { conerisGS_invG := Hinv
      conerisGS_heap := inferInstance
      conerisGS_tapes := inferInstance
      conerisGS_heap_name := γH
      conerisGS_tapes_name := γT
      conerisGS_error := { γec := γec } }
  ihave H := @Hwp HconerisGS $$ Hec
  icases H with ⟨Hwp, Hwps⟩
  iapply wp_refRcoupl_step_fupdN (GF := GF) ζ ε e es σ n φ sch
  iframe Hwp Hwps HecAuth
  simp only [conerisGS_state_interp_eq, heap_auth, tapes_auth]
  iframe

/-- Rocq: `wp_pgl`. The hypothesis `0 <= ε` is dropped. -/
theorem wp_pgl [conerisGpreS GF] (ζ : sch_int_state) (n : ℕ) (e : expr) (σ : state) (ε : ℝ≥0∞)
    (sch : scheduler con_prob_lang_mdp sch_int_state) (φ : val → Prop)
    [TapeOblivious sch_int_state sch]
    (Hwp : ∀ [conerisGS GF], ⊢@{IProp GF} ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) :
    pgl (sch_exec sch n (ζ, ([e], σ))) φ ε := by
  refine wp_pgl_multi (GF := GF) ζ n e [] σ ε sch φ ?_
  intro _
  iintro Hε
  isplitl
  · iapply Hwp $$ Hε
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

omit [DecidableEq sch_int_state] in
/-- Rocq: `pgl_closed_lim`. -/
theorem pgl_closed_lim (ζ : sch_int_state) (e : expr) (σ : state) (ε : ℝ≥0∞)
    (sch : scheduler con_prob_lang_mdp sch_int_state) (φ : val → Prop)
    [TapeOblivious sch_int_state sch] (Hn : ∀ n, pgl (sch_exec sch n (ζ, ([e], σ))) φ ε) :
    pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε :=
  sch_lim_exec_continuous_prob sch _ _ ε Hn

/-- Rocq: `wp_pgl_lim`. The hypothesis `0 <= ε` is dropped. -/
theorem wp_pgl_lim [conerisGpreS GF] (ζ : sch_int_state) (e : expr) (σ : state) (ε : ℝ≥0∞)
    (sch : scheduler con_prob_lang_mdp sch_int_state) (φ : val → Prop)
    [TapeOblivious sch_int_state sch]
    (Hwp : ∀ [conerisGS GF], ⊢@{IProp GF} ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) :
    pgl (sch_lim_exec sch (ζ, ([e], σ))) φ ε :=
  pgl_closed_lim ζ e σ ε sch φ fun n => wp_pgl (GF := GF) ζ n e σ ε sch φ Hwp

end pgl_adequacy

/-! ## Safety -/

/-- Rocq: `sch_mass_1`. -/
def sch_mass_1 {sch_int_state : Type} [Countable sch_int_state]
    (sch : scheduler con_prob_lang_mdp sch_int_state) : Prop :=
  ∀ sch_cfg, ∑' a, sch sch_cfg a = 1

/-- Rocq: `safety_dbind_adv`. -/
theorem safety_dbind_adv {A A' : Type _} [Countable A] [Countable A'] (h : A → Distr A')
    (μ : Distr A) (ε : ℝ≥0∞) (ε2 : A → ℝ≥0∞) (R : A → Prop) (H' : ∑' a, μ a = 1)
    (_H1 : ∃ r, ∀ a, ε2 a ≤ r) (Hpgl : pgl μ R ε) (H2 : ∀ a, R a → 1 - ε2 a ≤ ∑' b, h a b) :
    1 - (ε + Expval μ ε2) ≤ ∑' b, (μ ≫= h) b := by
  classical
  rw [pgl_unfold] at Hpgl
  rw [dbind_mass, tsub_le_iff_right, ← H']
  calc ∑' a, μ a
      ≤ ∑' a, (μ a * ∑' b, h a b +
          ((if (!decide (R a)) = true then μ a else 0) + μ a * ε2 a)) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases hR : R a
        · simp only [hR, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, zero_add,
            ← mul_add]
          calc μ a = μ a * 1 := (mul_one _).symm
            _ ≤ μ a * (∑' b, h a b + ε2 a) := by gcongr; exact tsub_le_iff_right.1 (H2 a hR)
        · simp only [hR, decide_false, Bool.not_false, ite_true]
          exact le_add_left le_self_add
    _ = ∑' a, μ a * ∑' b, h a b + (prob μ (fun a => !decide (R a)) + Expval μ ε2) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
        rfl
    _ ≤ ∑' a, μ a * ∑' b, h a b + (ε + Expval μ ε2) := by gcongr

section safety

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `safety_dbind_adv'`. -/
theorem safety_dbind_adv' {A A' : Type _} [Countable A] [Countable A'] (h : A → Distr A')
    (μ : Distr A) (ε : ℝ≥0∞) (ε2 : A → ℝ≥0∞) (n : ℕ) (R : A → Prop) :
    ⊢@{IProp GF} ⌜∑' a, μ a = 1⌝ -∗ ⌜∃ r, ∀ a, ε2 a ≤ r⌝ -∗ ⌜pgl μ R ε⌝ -∗
      (∀ a, ⌜R a⌝ ={∅}=∗ |={∅}[∅]▷=>^[n] ⌜1 - ε2 a ≤ ∑' b, h a b⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜1 - (ε + Expval μ ε2) ≤ ∑' b, (μ ≫= h) b⌝ := by
  iintro %H' %H1 %Hpgl H
  iapply fupd_step_fupdN_pure_forall_imp (r := 1 - (ε + Expval μ ε2) ≤ ∑' b, (μ ≫= h) b) n
    (safety_dbind_adv h μ ε ε2 R H' H1 Hpgl)
  iexact H

/-- Rocq: `safety_dbind'`. The hypothesis `0 <= ε` is dropped. -/
theorem safety_dbind' {A A' : Type _} [Countable A] [Countable A'] (h : A → Distr A')
    (μ : Distr A) (ε : ℝ≥0∞) (n : ℕ) :
    ⊢@{IProp GF} ⌜∑' a, μ a = 1⌝ -∗
      (∀ a, |={∅}[∅]▷=>^[n] ⌜1 - ε ≤ ∑' b, h a b⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜1 - ε ≤ ∑' b, (μ ≫= h) b⌝ := by
  iintro %Hmass H
  iapply fupd_step_fupdN_pure_forall (r := 1 - ε ≤ ∑' b, (μ ≫= h) b) n fun H' => by
    have := safety_dbind_adv h μ 0 (fun _ => ε) (fun _ => True) Hmass ⟨ε, fun _ => le_rfl⟩
      (pgl_trivial μ 0) fun a _ => H' a
    rwa [zero_add, Expval_const, Hmass, mul_one] at this
  iintro %a
  imodintro
  iapply H

variable {sch_int_state : Type} [DecidableEq sch_int_state] [Countable sch_int_state]

omit [conerisGS GF] in
/-- Rocq: `sch_erasable_mass`. -/
theorem sch_erasable_mass (ζ : sch_int_state) (sch : scheduler con_prob_lang_mdp sch_int_state)
    [TapeOblivious sch_int_state sch] (μ : Distr state) (σ : state)
    (H : sch_erasable tape_oblivious_sch μ σ) : ∑' a, μ a = 1 := by
  have H0 := sch_erasable_sch_erasable_val tape_oblivious_sch μ σ H sch_int_state sch
    [Val (LitV LitUnit)] ζ 0 inferInstance
  have Hf : ∀ σ', sch_exec sch 0 (ζ, ([Val (LitV LitUnit)], σ')) = dret (LitV LitUnit) :=
    fun σ' => sch_exec_is_final sch _ _ 0 rfl
  simp only [Hf] at H0
  have := congrArg (fun ν => ∑' a, ν a) H0
  erw [dbind_mass, dret_mass] at this
  simpa using this

/-- Rocq: `state_step_coupl_erasure_safety`. -/
theorem state_step_coupl_erasure_safety (ζ : sch_int_state) (es : List expr) (σ : state)
    (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) (n : ℕ)
    (sch : scheduler con_prob_lang_mdp sch_int_state) [TapeOblivious sch_int_state sch] :
    ⊢ state_step_coupl σ ε Z -∗
      (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n]
        ⌜1 - ε2 ≤ ∑' a, sch_pexec sch n (ζ, (es, σ2)) a⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜1 - ε ≤ ∑' a, sch_pexec sch n (ζ, (es, σ)) a⌝ := by
  iintro H Hcont
  iapply state_step_coupl_ind
    (fun σ ε => iprop((∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n]
        ⌜1 - ε2 ≤ ∑' a, sch_pexec sch n (ζ, (es, σ2)) a⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n] ⌜1 - ε ≤ ∑' a, sch_pexec sch n (ζ, (es, σ)) a⌝)) Z
    $$ [] %σ %ε H Hcont
  iintro !> %σ' %ε' H Hcont
  icases H with (%H | H | H | ⟨%μ, %ε2, %Herasable, %Hr, %Hineq, H⟩)
  · imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    rw [tsub_eq_zero_of_le H]
    exact zero_le
  · iapply Hcont $$ H
  · iapply fupd_step_fupdN_pure_forall_imp
      (r := 1 - ε' ≤ ∑' a, sch_pexec sch n (ζ, (es, σ')) a) n one_sub_le_of_forall_lt
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨H, -⟩
    iapply H $$ Hcont
  · dsimp only at Herasable Hineq
    have Hm : ∑' a, sch_pexec sch n (ζ, (es, σ')) a =
        ∑' a, (μ ≫= fun σ2 => sch_pexec sch n (ζ, (es, σ2))) a := by
      have := congrArg (fun ν => ∑' a, ν a) (Herasable sch_int_state sch es ζ n inferInstance)
      dsimp only at this
      erw [dmap_mass, dmap_mass] at this
      exact this.symm
    rw [Hm]
    iapply fupd_step_fupdN_pure_forall_imp
      (r := 1 - ε' ≤ ∑' a, (μ ≫= fun σ2 => sch_pexec sch n (ζ, (es, σ2))) a) n fun h =>
        (tsub_le_tsub_left (by simpa using Hineq) 1).trans
          (safety_dbind_adv _ μ 0 ε2 (fun _ => True) (sch_erasable_mass ζ sch μ σ' Herasable) Hr
            (pgl_trivial μ 0) h)
    iintro %σ2 -
    imod H $$ %σ2 with ⟨H, -⟩
    iapply H $$ Hcont

/-- Rocq: `state_step_coupl_erasure_safety'`. -/
theorem state_step_coupl_erasure_safety' (ζ : sch_int_state) (e : expr) (es : List expr)
    (e' : expr) (σ : state) (ε : ℝ≥0∞) (Z : state → ℝ≥0∞ → IProp GF) (n num : ℕ)
    (sch : scheduler con_prob_lang_mdp sch_int_state) [TapeOblivious sch_int_state sch]
    (Hlookup : (e :: es)[num]? = some e') (Hv : to_val e = none) (Hv' : to_val e' = none) :
    ⊢ state_step_coupl σ ε Z -∗
      (∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n+1]
        ⌜1 - ε2 ≤ ∑' a, (prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n+1]
        ⌜1 - ε ≤ ∑' a, (prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a⌝ := by
  iintro H Hcont
  iapply state_step_coupl_ind
    (fun σ ε => iprop((∀ σ2 ε2, Z σ2 ε2 ={∅}=∗ |={∅}[∅]▷=>^[n+1]
        ⌜1 - ε2 ≤ ∑' a, (prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[n+1]
        ⌜1 - ε ≤ ∑' a, (prim_step (Λ := con_prob_lang) e' σ ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a⌝)) Z
    $$ [] %σ %ε H Hcont
  iintro !> %σ' %ε' H Hcont
  icases H with (%H | H | H | ⟨%μ, %ε2, %Herasable, %Hr, %Hineq, H⟩)
  · imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply laterN_intro
    ipureintro
    rw [tsub_eq_zero_of_le H]
    exact zero_le
  · iapply Hcont $$ H
  · iapply fupd_step_fupdN_pure_forall_imp
      (r := 1 - ε' ≤ ∑' a, (prim_step (Λ := con_prob_lang) e' σ' ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a) (n+1)
      one_sub_le_of_forall_lt
    iintro %ε'' %Hlt
    icases H $$ %ε'' %Hlt with ⟨H, -⟩
    iapply H $$ Hcont
  · dsimp only at Herasable Hineq
    have Hm : ∑' a, (prim_step (Λ := con_prob_lang) e' σ' ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a =
        ∑' a, (μ ≫= fun σ2 => prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a := by
      have := congrArg (fun ν => ∑' a, ν a) (Rcoupl_eq_elim _ _
        (prim_coupl_step_prim_pexec_sch_erasable (sch := sch) e n es σ' ζ e' num μ Herasable
          Hlookup Hv Hv'))
      dsimp only at this
      erw [dmap_mass, dmap_mass] at this
      exact this
    rw [Hm]
    iapply fupd_step_fupdN_pure_forall_imp
      (r := 1 - ε' ≤ ∑' a, (μ ≫= fun σ2 => prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
          sch_pexec sch n (ζ, ((e :: es).set num t.1 ++ t.2.2, t.2.1))) a) (n+1) fun h =>
        (tsub_le_tsub_left (by simpa using Hineq) 1).trans
          (safety_dbind_adv _ μ 0 ε2 (fun _ => True) (sch_erasable_mass ζ sch μ σ' Herasable) Hr
            (pgl_trivial μ 0) h)
    iintro %σ2 -
    imod H $$ %σ2 with ⟨H, -⟩
    iapply H $$ Hcont

/-- Rocq: `wp_safety_step_fupdN`. -/
theorem wp_safety_step_fupdN (ζ : sch_int_state) (ε : ℝ≥0∞) (e : expr) (es : List expr)
    (σ : state) (n : ℕ) (φ : val → Prop) (sch : scheduler con_prob_lang_mdp sch_int_state)
    [TapeOblivious sch_int_state sch] (Hmass : sch_mass_1 sch) :
    (state_interp σ : IProp GF) ∗ err_interp ε ∗ WP e {{ v, ⌜φ v⌝ }} ∗
        ([∗list] e' ∈ es, WP e' {{ _v, True }}) ⊢
      |={⊤, ∅}=> |={∅}[∅]▷=>^[n] ⌜1 - ε ≤ ∑' a, sch_pexec sch n (ζ, (e :: es, σ)) a⌝ := by
  induction n generalizing ζ ε e es σ with
  | zero =>
    iintro -
    iapply fupd_mask_intro_discard LawfulSet.empty_subset
    simp only [Nat.repeat]
    ipureintro
    rw [sch_pexec_O]
    erw [dret_mass]
    exact tsub_le_self
  | succ n IH =>
    rw [sch_pexec_Sn]
    cases Heq : to_val e with
    | some v =>
      rw [sch_step_or_final_is_final _ _ ⟨v, Heq⟩, dret_id_left]
      iintro ⟨Hσ, Hε, Hwp, Hwps⟩
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hclose
      simp only [Nat.repeat]
      iintro !> !>
      imod Hclose
      iapply IH ζ ε e es σ
      iframe
    | none =>
      rw [sch_step_or_final_not_final _ _ (to_final_None_2 _ Heq), sch_step, ← dbind_assoc]
      dsimp only
      iintro ⟨Hσ, Hε, Hwp, Hwps⟩
      iapply fupd_mask_intro LawfulSet.empty_subset
      iintro Hclose
      iapply (step_fupd_fupdN_S n _).2
      iapply safety_dbind' (fun a => dmap (fun mdp_σ' => (a.1, mdp_σ'))
        (con_prob_lang_mdp.step a.2 (e :: es, σ)) ≫= sch_pexec sch n) (sch (ζ, (e :: es, σ))) ε
        (n+1) $$ %(Hmass _)
      iintro %⟨ζ', k⟩
      change ℕ at k
      cases Hk : (e :: es)[k]? with
      | none =>
        -- step a thread that is out of bounds
        rw [con_prob_lang_mdp_step_stutter e es σ ζ' k _ Heq (.inl Hk)]
        simp only [Nat.repeat]
        iintro !> !>
        imod Hclose
        iapply IH ζ' ε e es σ
        iframe
      | some e' =>
        cases Hv' : to_val e' with
        | some v =>
          -- step a thread that is a value
          rw [con_prob_lang_mdp_step_stutter e es σ ζ' k _ Heq (.inr ⟨e', v, Hk, Hv'⟩)]
          simp only [Nat.repeat]
          iintro !> !>
          imod Hclose
          iapply IH ζ' ε e es σ
          iframe
        | none =>
          rw [con_prob_lang_mdp_step_prim e es e' σ ζ' k _ Heq Hk Hv']
          iapply (step_fupd_fupdN_S n _).2
          imod Hclose
          cases k with
          | zero =>
            -- step the main thread
            obtain rfl : e = e' := Option.some.inj Hk
            imod pgl_wp_unfold_none Heq $$ Hwp %σ %ε [Hσ Hε] with Hlift
            · iframe
            iapply state_step_coupl_erasure_safety' ζ' e es e σ ε _ n 0 sch rfl Heq Heq $$ Hlift
            iintro %σ2 %ε2 ⟨%ε3, %Hred, %Hr, %Hineq, H⟩
            iapply fupd_step_fupdN_pure_forall_imp
              (r := 1 - ε2 ≤ ∑' a, (prim_step (Λ := con_prob_lang) e σ2 ≫= fun t =>
                sch_pexec sch n (ζ', ((e :: es).set 0 t.1 ++ t.2.2, t.2.1))) a) (n+1) fun h =>
                (tsub_le_tsub_left (by simpa using Hineq) 1).trans
                  (safety_dbind_adv _ _ 0 ε3 (fun _ => True)
                    (prim_step_mass (Λ := con_prob_lang) _ _ Hred) Hr (pgl_trivial _ 0) h)
            iintro %⟨e3, σ3, efs⟩ -
            imod H $$ %e3 %σ3 %efs with H
            simp only [Nat.repeat]
            iintro !> !> !>
            iapply state_step_coupl_erasure_safety $$ H
            iintro %σ4 %ε4 H
            imod H with ⟨Hσ, Hε, Hwp, Hefs⟩
            simp only [List.set_cons_zero, List.cons_append]
            iapply IH ζ' ε4 e3 (es ++ efs) σ4
            iframe Hσ Hε Hwp
            iapply BigSepL.bigSepL_append.2
            iframe
          | succ k =>
            -- step another thread
            have Hk' : es[k]? = some e' := by simpa using Hk
            icases BigSepL.bigSepL_insert_acc (Φ := fun _ e' => iprop(WP e' {{ _v, True }})) Hk'
              $$ Hwps with ⟨Hwp', Hwps⟩
            imod pgl_wp_unfold_none Hv' $$ Hwp' %σ %ε [Hσ Hε] with Hlift
            · iframe
            iapply state_step_coupl_erasure_safety' ζ' e es e' σ ε _ n (k+1) sch Hk Heq Hv'
              $$ Hlift
            iintro %σ2 %ε2 ⟨%ε3, %Hred, %Hr, %Hineq, H⟩
            iapply fupd_step_fupdN_pure_forall_imp
              (r := 1 - ε2 ≤ ∑' a, (prim_step (Λ := con_prob_lang) e' σ2 ≫= fun t =>
                sch_pexec sch n (ζ', ((e :: es).set (k+1) t.1 ++ t.2.2, t.2.1))) a) (n+1) fun h =>
                (tsub_le_tsub_left (by simpa using Hineq) 1).trans
                  (safety_dbind_adv _ _ 0 ε3 (fun _ => True)
                    (prim_step_mass (Λ := con_prob_lang) _ _ Hred) Hr (pgl_trivial _ 0) h)
            iintro %⟨e3, σ3, efs⟩ -
            imod H $$ %e3 %σ3 %efs with H
            simp only [Nat.repeat]
            iintro !> !> !>
            iapply state_step_coupl_erasure_safety $$ H
            iintro %σ4 %ε4 H
            imod H with ⟨Hσ, Hε, Hwp', Hefs⟩
            simp only [List.set_cons_succ, List.cons_append]
            iapply IH ζ' ε4 e (es.set k e3 ++ efs) σ4
            iframe Hσ Hε Hwp
            iapply BigSepL.bigSepL_append.2
            iframe Hefs
            iapply Hwps $$ Hwp'

end safety

section safety_adequacy

variable {GF : BundledGFunctors} {sch_int_state : Type} [DecidableEq sch_int_state]
  [Countable sch_int_state]

/-- Rocq: `wp_safety_multi`. The hypothesis `0 <= ε` is dropped. -/
theorem wp_safety_multi [conerisGpreS GF] (ζ : sch_int_state) (n : ℕ) (e : expr)
    (es : List expr) (σ : state) (ε : ℝ≥0∞) (sch : scheduler con_prob_lang_mdp sch_int_state)
    (φ : val → Prop) [TapeOblivious sch_int_state sch] (Hmass : sch_mass_1 sch)
    (Hwp : ∀ [conerisGS GF],
      ⊢@{IProp GF} ↯ ε -∗ (WP e {{ v, ⌜φ v⌝ }} ∗ [∗list] e' ∈ es, WP e' {{ _v, True }})) :
    1 - ε ≤ ∑' a, sch_pexec sch n (ζ, (e :: es, σ)) a := by
  -- Handle the trivial `1 ≤ ε` case
  by_cases hε : 1 ≤ ε
  · rw [tsub_eq_zero_of_le hε]
    exact zero_le
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) n 0 fun Hinv => ?_
  iintro -
  imod ghost_map_alloc (GF := GF) (H := loc_map) σ.heap with ⟨%γH, Hh, -⟩
  imod ghost_map_alloc (GF := GF) (H := loc_map) σ.tapes with ⟨%γT, Ht, -⟩
  imod ec_alloc ε (lt_of_not_ge hε) with ⟨%γec, HecAuth, Hec⟩
  let HconerisGS : conerisGS GF :=
    { conerisGS_invG := Hinv
      conerisGS_heap := inferInstance
      conerisGS_tapes := inferInstance
      conerisGS_heap_name := γH
      conerisGS_tapes_name := γT
      conerisGS_error := { γec := γec } }
  ihave H := @Hwp HconerisGS $$ Hec
  icases H with ⟨Hwp, Hwps⟩
  iapply wp_safety_step_fupdN (GF := GF) ζ ε e es σ n φ sch Hmass
  iframe Hwp Hwps HecAuth
  simp only [conerisGS_state_interp_eq, heap_auth, tapes_auth]
  iframe

/-- Rocq: `wp_safety`. The hypothesis `0 <= ε` is dropped. -/
theorem wp_safety [conerisGpreS GF] (ζ : sch_int_state) (e : expr) (σ : state) (ε : ℝ≥0∞)
    (n : ℕ) (sch : scheduler con_prob_lang_mdp sch_int_state) (φ : val → Prop)
    [TapeOblivious sch_int_state sch] (Hmass : sch_mass_1 sch)
    (Hwp : ∀ [conerisGS GF], ⊢@{IProp GF} ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) :
    1 - ε ≤ ∑' a, sch_pexec sch n (ζ, ([e], σ)) a := by
  refine wp_safety_multi (GF := GF) ζ n e [] σ ε sch φ Hmass ?_
  intro _
  iintro Hε
  isplitl
  · iapply Hwp $$ Hε
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

end safety_adequacy

end Coneris
