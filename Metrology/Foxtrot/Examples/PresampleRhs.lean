module

public import Metrology.Foxtrot.Lib.Diverge
public import Metrology.Foxtrot.Lib.Nodet
public import Metrology.ConProbLang.LubTermination

/-!
# Counterexample to presampling on the right-hand side (programs and termination)

Ported from clutch/theories/foxtrot/examples/presample_rhs.v (the programs `prog0`–`prog3` and
the termination lemmas `prog0_termination`, `prog3_termination`). The counterexample itself
(`unsound_presample_RHS`, `presample_RHS_is_unsound'`, `presample_RHS_is_unsound`) is in
`Metrology.Foxtrot.Examples.PresampleRhsUnsound`.

## Rocq → Lean map
* `prog0`, `prog1`, `prog2`, `prog3`, `prog0_termination`, `prog3_termination`: same names
  (namespace `Foxtrot.Examples.PresampleRhs`).

## Deviations
* `Rbar_le 1 (lub_termination_prob prog0 σ)` is `1 ≤ lub_termination_prob prog0 σ` and
  `Rbar_le (lub_termination_prob prog3 σ) (1/2)` is `lub_termination_prob prog3 σ ≤ 1/2`
  in `ℝ≥0∞` (`lub_termination_prob` is an `sSup` in `ℝ≥0∞`).
* The scheduler of `prog0_termination` is the same (`λ _, dzero` on the unit type).
* `prog3_termination`: the Rocq proof bounds the pointwise `sch_exec sch n (ζ, ([prog3], σ)) v`
  (first showing that only `v = #()` has positive mass), with the local lemma `K` (one step of
  a single-thread configuration, stutter or thread `0`). Here the same argument is done on the
  total mass `∑' v, sch_exec sch n (ζ, ([e], σ)) v` directly: `K` is the helper
  `sch_exec_single_le`, and the inlined inductions of the Rocq proof are the helpers
  `sch_exec_det_step_le` (a deterministic pure step), `sch_exec_diverge_le`,
  `sch_exec_if_zero_le` and `sch_exec_prog3_le`. The prim-step computations of the Rocq proof
  (`fill_dmap`, `head_prim_step_eq`, `dmap_elem_ne`, `SeriesC_list`, ...) are the helpers
  `prim_step_of_pure`, `prim_step_prog3` and `tsum_dmap_mul`.

## Added
* `sch_exec_single_le`, `sch_exec_zero_single`, `sch_exec_det_step_le`, `sch_exec_diverge_le`,
  `sch_exec_if_zero_le`,
  `sch_exec_prog3_le`, `prim_step_of_pure`, `prim_step_prog3`, `tsum_dmap_mul`,
  `tsum_dret_mul`, `unit_termination_prob_type`.

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Prob ConProbLang ConProbLang.con_prob_lang Foxtrot.Lib.Diverge Foxtrot.Lib.Nodet

namespace Foxtrot.Examples.PresampleRhs

set_option quotPrecheck false in
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-- Rocq: `prog0`. -/
def prog0 : expr := cpl(#())

/-- Rocq: `prog1`. -/
def prog1 : expr := cpl(if &nodet #() = rand(#1) then #() else &diverge #())

/-- Rocq: `prog2`. -/
def prog2 : expr := cpl(
  let α := alloc(#1) in
  if (rand(α) #1) = &nodet #() then #() else &diverge #())

/-- Rocq: `prog3`. -/
def prog3 : expr := cpl(if rand(#1) = #1 then #() else &diverge #())

/-! ## Termination of `prog0` -/

/-- Helper: the trivial scheduler `λ _, dzero` on the unit type (Rocq: inline in
`prog0_termination`), as an element of `termination_prob_type`. -/
def unit_termination_prob_type : termination_prob_type where
  sch_int_σ := Unit
  ζ := ()
  eqdec := inferInstance
  countable := inferInstance
  sch := ⟨fun _ => dzero⟩
  tape_oblivious := ⟨fun _ _ _ _ _ => rfl⟩

/-- Rocq: `prog0_termination`. -/
theorem prog0_termination (σ : state) : 1 ≤ lub_termination_prob prog0 σ := by
  unfold lub_termination_prob
  refine le_sSup ⟨unit_termination_prob_type, ?_⟩
  unfold termination_prob
  rw [sch_lim_exec_final _ _ (LitV LitUnit) rfl]
  exact dret_mass _

/-! ## Termination of `prog3` -/

/-- Helper: `∑' x, dret a x * F x = F a`. -/
theorem tsum_dret_mul {A : Type*} [Countable A] (a : A) (F : A → ℝ≥0∞) :
    ∑' x, dret a x * F x = F a := by
  rw [tsum_eq_single a (fun x hx => by rw [dret_0 _ _ hx, zero_mul]), dret_1_1 _ _ rfl, one_mul]

/-- Helper: `∑' x, dmap f μ x * F x = ∑' a, μ a * F (f a)`. -/
theorem tsum_dmap_mul {A B : Type*} [Countable A] [Countable B] (f : A → B) (μ : Distr A)
    (F : B → ℝ≥0∞) : ∑' x, dmap f μ x * F x = ∑' a, μ a * F (f a) := by
  unfold dmap
  simp only [dbind_unfold_pmf, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  simp only [mul_assoc]
  rw [ENNReal.tsum_mul_left, tsum_dret_mul]

/-- Helper: a pure step is a deterministic `prim_step`. -/
theorem prim_step_of_pure {φ : Prop} (e1 e2 : expr) (h : PureExec (Λ := con_prob_lang) φ 1 e1 e2)
    (hφ : φ) (σ : state) :
    prim_step (Λ := con_prob_lang) e1 σ = dret (e2, σ, []) := by
  have h1 := h.pure_exec hφ
  cases h1 with
  | nsteps_l _ _ y _ hxy hyz =>
    cases hyz
    exact pmf_1_eq_dret _ _ (hxy.pure_step_det σ)

variable {sch_int_σ : Type} [Countable sch_int_σ]
variable (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ)

/-- Rocq: the local lemma `K` of `prog3_termination`, for the total mass. One step of a
single-thread configuration `([e], σ)` (`e` not a value): either the scheduler stutters, or it
steps thread `0`. -/
theorem sch_exec_single_le (n : ℕ) (e : expr) (σ : state)
    (Hval : ConProbLang.to_val (Λ := con_prob_lang) e = none) (r : ℝ≥0∞)
    (H1 : ∀ ζ', ∑' v, sch_exec sch n (ζ', (([e], σ) : CPState)) v ≤ r)
    (H2 : ∀ ζ', ∑' x : expr × state × List expr, prim_step (Λ := con_prob_lang) e σ x *
      ∑' v, sch_exec sch n (ζ', (((x.1 :: x.2.2), x.2.1) : CPState)) v ≤ r)
    (ζ : sch_int_σ) :
    ∑' v, sch_exec sch (n + 1) (ζ, (([e], σ) : CPState)) v ≤ r := by
  have hnf : ¬ is_final (δ := con_lang_mdp con_prob_lang) (([e], σ) : CPState) := by
    apply to_final_None_2
    show con_lang_mdp_to_final con_prob_lang ([e], σ) = none
    simp [con_lang_mdp_to_final, Hval]
  rw [sch_exec_Sn_not_final _ _ _ hnf]
  unfold sch_step
  rw [← dbind_assoc, dbind_mass]
  calc ∑' p, sch (ζ, (([e], σ) : CPState)) p * ∑' v, (dmap (fun mdp_σ' => (p.1, mdp_σ'))
          ((con_lang_mdp con_prob_lang).step p.2 (([e], σ) : CPState)) ≫= sch_exec sch n) v
      ≤ ∑' p, sch (ζ, (([e], σ) : CPState)) p * r := by
        refine ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl ?_
        obtain ⟨ζ', a⟩ := p
        rw [dbind_mass, tsum_dmap_mul]
        show ∑' x, con_lang_mdp_step con_prob_lang a ([e], σ) x * _ ≤ r
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp only [con_lang_mdp_step, List.getElem?_cons_zero, Option.bind_eq_bind,
            Option.bind_some, Hval]
          rw [tsum_dmap_mul]
          simpa using H2 ζ'
        · have hnone : ∀ b : ℕ, 0 < b → ([e] : List expr)[b]? = none := by
            intro b hb; simp; omega
          simp only [con_lang_mdp_step, List.getElem?_cons_zero, Option.bind_eq_bind,
            Option.bind_some, Hval, hnone a ha]
          rw [tsum_dret_mul]
          exact H1 ζ'
    _ = (∑' p, sch (ζ, (([e], σ) : CPState)) p) * r := ENNReal.tsum_mul_right
    _ ≤ 1 * r := mul_le_mul' (pmf_SeriesC _) le_rfl
    _ = r := one_mul r

/-- Helper: a single-thread configuration that is not final has no mass after `0` steps. -/
theorem sch_exec_zero_single (e : expr) (σ : state) (ζ : sch_int_σ)
    (Hval : ConProbLang.to_val (Λ := con_prob_lang) e = none) :
    ∑' v, sch_exec sch 0 (ζ, (([e], σ) : CPState)) v = 0 := by
  have hnf : ¬ is_final (δ := con_lang_mdp con_prob_lang) (([e], σ) : CPState) := by
    apply to_final_None_2
    show con_lang_mdp_to_final con_prob_lang ([e], σ) = none
    simp [con_lang_mdp_to_final, Hval]
  rw [sch_exec_O_not_final _ _ hnf]
  exact dzero_mass

/-- Helper (Rocq: the inlined inductions over deterministic steps in `prog3_termination`): if
`e` deterministically steps to `e'` without forking, and every `n`-step execution of `[e']` has
mass at most `r` (possibly assuming the same of `[e]`), then so has every execution of `[e]`. -/
theorem sch_exec_det_step_le (e e' : expr)
    (Hval : ConProbLang.to_val (Λ := con_prob_lang) e = none)
    (Hstep : ∀ σ, prim_step (Λ := con_prob_lang) e σ = dret (e', σ, [])) (r : ℝ≥0∞)
    (H : ∀ n, (∀ ζ σ, ∑' v, sch_exec sch n (ζ, (([e], σ) : CPState)) v ≤ r) →
      ∀ ζ σ, ∑' v, sch_exec sch n (ζ, (([e'], σ) : CPState)) v ≤ r) :
    ∀ n ζ σ, ∑' v, sch_exec sch n (ζ, (([e], σ) : CPState)) v ≤ r := by
  intro n
  induction n with
  | zero => intro ζ σ; rw [sch_exec_zero_single sch e σ ζ Hval]; exact zero_le
  | succ n IH =>
    intro ζ σ
    refine sch_exec_single_le sch n e σ Hval r (fun ζ' => IH ζ' σ) (fun ζ' => ?_) ζ
    rw [Hstep, tsum_dret_mul]
    exact H n IH ζ' σ

/-- Helper: `diverge #()` never terminates (Rocq: `Hdiverge`). -/
theorem sch_exec_diverge_le (n : ℕ) (ζ : sch_int_σ) (σ : state) :
    ∑' v, sch_exec sch n (ζ, (([cpl(&diverge #())], σ) : CPState)) v ≤ 0 :=
  sch_exec_det_step_le sch _ _ rfl
    (fun σ => by
      unfold diverge
      rw [prim_step_of_pure _ _ inferInstance trivial σ]
      rfl) 0 (fun _ h => h) n ζ σ

/-- Helper: `if: #0 = #1 then #() else diverge #()` never terminates. -/
theorem sch_exec_if_zero_le (n : ℕ) (ζ : sch_int_σ) (σ : state) :
    ∑' v, sch_exec sch n (ζ, (([cpl(if #(0 : ℤ) = #1 then #() else &diverge #())], σ) : CPState))
      v ≤ 0 := by
  have Hstep : ∀ σ, prim_step (Λ := con_prob_lang)
      cpl(if #(0 : ℤ) = #1 then #() else &diverge #()) σ =
      dret (cpl(if #false then #() else &diverge #()), σ, []) := by
    intro σ
    have h := prim_step_of_pure _ _
      (pure_exec_ctx (Λ := con_prob_lang) (fill [IfCtx cpl(#()) cpl(&diverge #())]) _ _ _ _
        (pure_binop_eval EqOp (LitV (LitInt 0)) (LitV (LitInt 1))))
      (by simp [bin_op_eval, vals_compare_safe, val_is_unboxed, lit_is_unboxed]) σ
    simp only [bin_op_eval, vals_compare_safe, val_is_unboxed, lit_is_unboxed] at h
    rw [show cpl(if #(0 : ℤ) = #1 then #() else &diverge #()) =
      fill [IfCtx cpl(#()) cpl(&diverge #())] cpl(#(0 : ℤ) = #1) from rfl, h]
    simp; rfl
  refine sch_exec_det_step_le sch _ cpl(if #false then #() else &diverge #()) rfl Hstep 0
    (fun m _ => ?_) n ζ σ
  exact sch_exec_det_step_le sch _ cpl(&diverge #()) rfl
    (fun σ => prim_step_of_pure _ _ (pure_if_false _ _) trivial σ) 0
    (fun k _ => sch_exec_diverge_le sch k) m

/-- Helper: the `prim_step` of `prog3`. -/
theorem prim_step_prog3 (σ : state) :
    prim_step (Λ := con_prob_lang) prog3 σ =
      dmap (fun n : Fin (1 + 1) =>
        ((cpl(if #((n : ℕ) : ℤ) = #1 then #() else &diverge #()), σ, []) :
          expr × state × List expr))
        (dunifP 1) :=
  prim_step_fill_head [BinOpLCtx EqOp (LitV (LitInt 1)), IfCtx _ _] _ σ (dunifP 1)
    (fun n : Fin (1 + 1) =>
      ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) : expr × state × List expr)) rfl
    (dunifP_mass _)

/-- Helper: every `n`-step execution of `prog3` has mass at most `1/2`. -/
theorem sch_exec_prog3_le (n : ℕ) (ζ : sch_int_σ) (σ : state) :
    ∑' v, sch_exec sch n (ζ, (([prog3], σ) : CPState)) v ≤ 1 / 2 := by
  induction n generalizing ζ with
  | zero => rw [sch_exec_zero_single sch prog3 σ ζ rfl]; exact zero_le
  | succ n IH =>
    refine sch_exec_single_le sch n prog3 σ rfl _ IH (fun ζ' => ?_) ζ
    rw [prim_step_prog3, tsum_dmap_mul, tsum_fintype, Fin.sum_univ_two]
    simp only [dunifP_pmf]
    have h0 := sch_exec_if_zero_le sch n ζ' σ
    have h1 := pmf_SeriesC (sch_exec sch n (ζ', (([cpl(if #(1 : ℤ) = #1
      then #() else &diverge #())], σ) : CPState)))
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_one, Nat.cast_one] at h0 h1 ⊢
    rw [nonpos_iff_eq_zero.1 h0, mul_zero, zero_add]
    calc ((1 + 1 : ℕ) : ℝ≥0∞)⁻¹ * _ ≤ ((1 + 1 : ℕ) : ℝ≥0∞)⁻¹ * 1 := mul_le_mul' le_rfl h1
      _ = 1 / 2 := by norm_num

/-- Rocq: `prog3_termination`. -/
theorem prog3_termination (σ : state) : lub_termination_prob prog3 σ ≤ 1 / 2 := by
  unfold lub_termination_prob
  refine sSup_le ?_
  rintro r ⟨p, rfl⟩
  unfold termination_prob
  rw [sch_lim_exec_Sup_seq]
  exact iSup_le fun n => sch_exec_prog3_le p.sch n p.ζ σ

end Foxtrot.Examples.PresampleRhs
