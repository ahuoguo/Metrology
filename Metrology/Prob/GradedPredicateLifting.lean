module

public import Metrology.Prob.Distribution

/-!
# Graded predicate liftings

Ported from clutch/theories/prob/graded_predicate_lifting.v

* `pgl μ f ε` (partial graded lifting): the probability that `f` fails under `μ` is at most `ε`.
* `tgl μ f ε` (total graded lifting): the probability that `f` holds under `μ` is at least
  `1 - ε`.

Compared with the Rocq development:
* gradings are `ℝ≥0∞` instead of `R`, so all hypotheses `0 <= ε` disappear and `1 - ε` is
  truncated subtraction (which agrees with the Rocq meaning since probabilities are
  non-negative);
* the predicates `f : α → Prop` are decided classically inside the definitions (as in Rocq,
  which uses `make_decision`); `pgl_unfold` / `tgl_unfold` restate them for any
  `DecidablePred` instance;
* summability and boundedness hypotheses (`ex_seriesC`, `∃ r, ∀ a, 0 <= ε' a <= r`) are dropped;
* `Forall P l` is written `∀ m ∈ l, P m`, and `1/(n+1)` is `1 / ((n : ℝ≥0∞) + 1)`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Prob

variable {α α' β : Type*} [Countable α] [Countable α'] [Countable β]

/-- Monotonicity of `prob` in the event (helper). -/
theorem prob_mono_event (μ : Distr α) {P Q : α → Bool} (h : ∀ a, P a = true → Q a = true) :
    prob μ P ≤ prob μ Q :=
  ENNReal.tsum_le_tsum fun a => by
    by_cases hP : P a
    · simp [hP, h a hP]
    · simp [hP]

/-- Complementary events split the mass (helper). -/
theorem prob_add_prob_not (μ : Distr α) (P : α → Bool) :
    prob μ P + prob μ (fun a => !P a) = ∑' a, μ a :=
  (SeriesC_split_pred (fun a => μ a) P).symm

/-! ## Partial graded lifting -/

section partial_graded_lifting

open Classical in
/-- Rocq: `pgl`. -/
def pgl (μ₁ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) : Prop :=
  prob μ₁ (fun a => !decide (f a)) ≤ ε

theorem pgl_unfold (μ : Distr α) (f : α → Prop) [DecidablePred f] (ε : ℝ≥0∞) :
    pgl μ f ε ↔ prob μ (fun a => !decide (f a)) ≤ ε := by
  unfold pgl; congr!

end partial_graded_lifting

section pgl_theory

open Classical

/-- Rocq: `pgl_mon_grading`. -/
theorem pgl_mon_grading (μ : Distr α) (f : α → Prop) (ε ε' : ℝ≥0∞) (Hleq : ε ≤ ε')
    (Hf : pgl μ f ε) : pgl μ f ε' :=
  le_trans Hf Hleq

/-- Rocq: `pgl_mon_pred`. -/
theorem pgl_mon_pred (μ : Distr α) (f g : α → Prop) (ε : ℝ≥0∞) (Himp : ∀ a, f a → g a)
    (Hf : pgl μ f ε) : pgl μ g ε := by
  unfold pgl at *
  refine le_trans (prob_mono_event μ fun a ha => ?_) Hf
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at ha ⊢
  exact fun hf => ha (Himp a hf)

/-- Rocq: `pgl_nonneg_grad` (trivial in `ℝ≥0∞`). -/
theorem pgl_nonneg_grad (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (_ : pgl μ f ε) : 0 ≤ ε :=
  zero_le

/-- Rocq: `pgl_dret`. -/
theorem pgl_dret (a : α) (f : α → Prop) (Hfa : f a) : pgl (dret a) f 0 := by
  unfold pgl
  rw [prob_dret_false]
  simp [Hfa]

/-- Rocq: `pgl_dbind`. The hypotheses `0 <= ε`, `0 <= ε'` are dropped. -/
theorem pgl_dbind (h : α → Distr α') (μ₁ : Distr α) (f : α → Prop) (g : α' → Prop)
    (ε ε' : ℝ≥0∞) (Hf : ∀ a, f a → pgl (h a) g ε') (Hμ₁ : pgl μ₁ f ε) :
    pgl (dbind h μ₁) g (ε + ε') := by
  unfold pgl at *
  rw [prob_dbind]
  calc ∑' a, μ₁ a * prob (h a) (fun b => !decide (g b))
      ≤ ∑' a, ((if !decide (f a) then μ₁ a else 0) + μ₁ a * ε') := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases hfa : f a
        · simp only [hfa, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, zero_add]
          exact mul_le_mul_right (Hf a hfa) _
        · simp only [hfa, decide_false, Bool.not_false, ite_true]
          calc μ₁ a * _ ≤ μ₁ a * 1 := mul_le_mul_right (prob_le_1 _ _) _
            _ = μ₁ a := mul_one _
            _ ≤ μ₁ a + μ₁ a * ε' := le_self_add
    _ = prob μ₁ (fun a => !decide (f a)) + (∑' a, μ₁ a) * ε' := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]; rfl
    _ ≤ ε + 1 * ε' := add_le_add Hμ₁ (mul_le_mul_left (pmf_SeriesC μ₁) _)
    _ = ε + ε' := by rw [one_mul]

/-- Rocq: `pgl_dbind'`. The hypothesis `0 <= ε` is dropped. -/
theorem pgl_dbind' (h : α → Distr α') (μ₁ : Distr α) (g : α' → Prop) (ε : ℝ≥0∞)
    (H' : ∀ a, 0 < μ₁ a → pgl (h a) g ε) : pgl (dbind h μ₁) g ε := by
  unfold pgl at *
  rw [prob_dbind]
  calc ∑' a, μ₁ a * prob (h a) (fun b => !decide (g b)) ≤ ∑' a, μ₁ a * ε := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        rcases eq_zero_or_pos (μ₁ a) with h0 | hpos
        · simp [h0]
        · exact mul_le_mul_right (H' a hpos) _
    _ = (∑' a, μ₁ a) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul_left (pmf_SeriesC μ₁) _
    _ = ε := one_mul _

/-- Rocq: `pgl_dbind_adv_aux`. The non-negativity and summability hypotheses are dropped. -/
theorem pgl_dbind_adv_aux (h : α → Distr α') (μ : Distr α) (g : α' → Prop) (ε : α → ℝ≥0∞)
    (Hg : ∀ a, pgl (h a) g (ε a)) : pgl (dbind h μ) g (∑' a, μ a * ε a) := by
  unfold pgl at *
  rw [prob_dbind]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (Hg a) _

/-- Rocq: `pgl_dbind_adv`. The hypotheses `0 <= ε` and `∃ r, ∀ a, 0 <= ε' a <= r` are
dropped (they are not needed in `ℝ≥0∞`). -/
theorem pgl_dbind_adv (h : α → Distr α') (μ : Distr α) (f : α → Prop) (g : α' → Prop)
    (ε : ℝ≥0∞) (ε' : α → ℝ≥0∞) (Hg : ∀ a, f a → pgl (h a) g (ε' a)) (Hf : pgl μ f ε) :
    pgl (dbind h μ) g (ε + ∑' a, μ a * ε' a) := by
  unfold pgl at *
  rw [prob_dbind]
  calc ∑' a, μ a * prob (h a) (fun b => !decide (g b))
      ≤ ∑' a, ((if !decide (f a) then μ a else 0) + μ a * ε' a) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases hfa : f a
        · simp only [hfa, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, zero_add]
          exact mul_le_mul_right (Hg a hfa) _
        · simp only [hfa, decide_false, Bool.not_false, ite_true]
          calc μ a * _ ≤ μ a * 1 := mul_le_mul_right (prob_le_1 _ _) _
            _ = μ a := mul_one _
            _ ≤ μ a + μ a * ε' a := le_self_add
    _ = prob μ (fun a => !decide (f a)) + ∑' a, μ a * ε' a := by
        rw [ENNReal.tsum_add]; rfl
    _ ≤ ε + ∑' a, μ a * ε' a := add_le_add_left Hf _

/-- Rocq: `pgl_dzero`. The hypothesis `ε >= 0` is dropped. -/
theorem pgl_dzero (f : α → Prop) (ε : ℝ≥0∞) : pgl (dzero : Distr α) f ε := by
  unfold pgl prob
  simp

/-- Rocq: `pgl_pos_R`. -/
theorem pgl_pos_R (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (Hμ : pgl μ f ε) :
    pgl μ (fun a => f a ∧ 0 < μ a) ε := by
  unfold pgl prob at *
  refine le_trans (ENNReal.tsum_le_tsum fun a => ?_) Hμ
  rcases eq_zero_or_pos (μ a) with h0 | hpos
  · simp [h0]
  · split_ifs <;> simp_all

/-- Rocq: `pgl_trivial`. The hypothesis `0 <= ε` is dropped. -/
theorem pgl_trivial (μ : Distr α) (ε : ℝ≥0∞) : pgl μ (fun _ => True) ε := by
  unfold pgl prob
  simp

/-- Rocq: `pgl_1`. -/
theorem pgl_1 (μ : Distr α) (ε : ℝ≥0∞) (P : α → Prop) (h : 1 ≤ ε) : pgl μ P ε :=
  (prob_le_1 _ _).trans h

/-- Rocq: `pgl_and`. -/
theorem pgl_and (μ : Distr α) (f g : α → Prop) (ε1 ε2 : ℝ≥0∞) (Hf : pgl μ f ε1)
    (Hg : pgl μ g ε2) : pgl μ (fun a => f a ∧ g a) (ε1 + ε2) := by
  unfold pgl at *
  refine le_trans ?_ (add_le_add Hf Hg)
  unfold prob
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hf : f a <;> by_cases hg : g a <;> simp [hf, hg]

/-- Rocq: `pgl_ext`. -/
theorem pgl_ext (μ : Distr α) (f g : α → Prop) (ε : ℝ≥0∞) (Hequiv : ∀ a, f a ↔ g a)
    (Hf : pgl μ f ε) : pgl μ g ε :=
  pgl_mon_pred μ f g ε (fun a => (Hequiv a).1) Hf

/-- Rocq: `pgl_epsilon_limit`. The hypotheses `ε' >= 0` and `EqDecision A` are dropped. -/
theorem pgl_epsilon_limit (μ : Distr α) (f : α → Prop) (ε' : ℝ≥0∞)
    (H' : ∀ ε, ε' < ε → pgl μ f ε) : pgl μ f ε' :=
  le_of_forall_gt_imp_ge_of_dense H'

end pgl_theory

/-! ## Instances for uniform distributions -/

section ub_instances

/-- Rocq: `ub_unif_err`. -/
theorem ub_unif_err (n : ℕ) (m : Fin (n + 1)) :
    pgl (dunifP n) (fun x => x ≠ m) (1 / ((n : ℝ≥0∞) + 1)) := by
  unfold pgl prob
  rw [tsum_eq_single m (fun b hb => by simp [hb])]
  simp

/-- Rocq: `ub_unif_err_nat`. -/
theorem ub_unif_err_nat (n m : ℕ) :
    pgl (dunifP n) (fun x => (x : ℕ) ≠ m) (1 / ((n : ℝ≥0∞) + 1)) := by
  by_cases hlt : m < n + 1
  · refine pgl_ext _ (fun x => x ≠ ⟨m, hlt⟩) _ _ (fun a => ?_) (ub_unif_err n ⟨m, hlt⟩)
    simp [Fin.ext_iff]
  · refine pgl_ext _ (fun _ => True) _ _ (fun a => ?_) (pgl_trivial _ _)
    simp only [true_iff]
    omega

/-- Rocq: `ub_unif_err_int`. -/
theorem ub_unif_err_int (n : ℕ) (m : ℤ) :
    pgl (dunifP n) (fun x => ((x : ℕ) : ℤ) ≠ m) (1 / ((n : ℝ≥0∞) + 1)) := by
  by_cases hpos : 0 ≤ m
  · refine pgl_ext _ (fun x : Fin (n + 1) => (x : ℕ) ≠ m.toNat) _ _ (fun a => ?_) (ub_unif_err_nat n _)
    omega
  · refine pgl_ext _ (fun _ => True) _ _ (fun a => ?_) (pgl_trivial _ _)
    simp only [true_iff]
    omega

/-- Rocq: `ub_unif_err_list_nat`. -/
theorem ub_unif_err_list_nat (n : ℕ) (l : List ℕ) :
    pgl (dunifP n) (fun x => ∀ m ∈ l, (x : ℕ) ≠ m) ((l.length : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) := by
  induction l with
  | nil =>
    refine pgl_ext _ (fun _ => True) _ _ (fun a => ?_) (pgl_trivial _ _)
    simp
  | cons a l IHl =>
    have : ((a :: l).length : ℝ≥0∞) / ((n : ℝ≥0∞) + 1) =
        1 / ((n : ℝ≥0∞) + 1) + (l.length : ℝ≥0∞) / ((n : ℝ≥0∞) + 1) := by
      rw [← ENNReal.add_div, List.length_cons]; push_cast; rw [add_comm]
    rw [this]
    refine pgl_ext _ _ _ _ (fun x => ?_) (pgl_and _ _ _ _ _ (ub_unif_err_nat n a) IHl)
    simp

/-- Rocq: `ub_unif_err_list_int`. -/
theorem ub_unif_err_list_int (n : ℕ) (l : List ℤ) :
    pgl (dunifP n) (fun x => ∀ m ∈ l, ((x : ℕ) : ℤ) ≠ m)
      ((l.length : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) := by
  induction l with
  | nil =>
    refine pgl_ext _ (fun _ => True) _ _ (fun a => ?_) (pgl_trivial _ _)
    simp
  | cons a l IHl =>
    have : ((a :: l).length : ℝ≥0∞) / ((n : ℝ≥0∞) + 1) =
        1 / ((n : ℝ≥0∞) + 1) + (l.length : ℝ≥0∞) / ((n : ℝ≥0∞) + 1) := by
      rw [← ENNReal.add_div, List.length_cons]; push_cast; rw [add_comm]
    rw [this]
    refine pgl_ext _ _ _ _ (fun x => ?_) (pgl_and _ _ _ _ _ (ub_unif_err_int n a) IHl)
    simp

end ub_instances

/-! ## Total graded lifting -/

section total_graded_lifting

open Classical in
/-- Rocq: `tgl`. -/
def tgl (μ₁ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) : Prop :=
  1 - ε ≤ prob μ₁ (fun a => decide (f a))

theorem tgl_unfold (μ : Distr α) (f : α → Prop) [DecidablePred f] (ε : ℝ≥0∞) :
    tgl μ f ε ↔ 1 - ε ≤ prob μ (fun a => decide (f a)) := by
  unfold tgl; congr!

end total_graded_lifting

section tgl_theory

open Classical

/-- Rocq: `tgl_implies_pgl_strong`. -/
theorem tgl_implies_pgl_strong (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (Htotal : tgl μ f ε) :
    pgl μ f (ε - (1 - ∑' a, μ a)) := by
  unfold tgl pgl at *
  set pf := prob μ (fun a => decide (f a))
  set pnf := prob μ (fun a => !decide (f a))
  have hsplit : pf + pnf = ∑' a, μ a := prob_add_prob_not μ _
  have hpf : pf ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_1 _ _)
  have h1 : 1 ≤ pf + ε := tsub_le_iff_right.1 Htotal
  refine ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) ?_
  rw [← hsplit, ← tsub_tsub]
  have hle : pnf ≤ 1 - pf := by
    refine ENNReal.le_sub_of_add_le_left hpf ?_
    rw [hsplit]; exact pmf_SeriesC μ
  rw [tsub_add_cancel_of_le hle, tsub_le_iff_right, add_comm]
  exact h1

/-- Rocq: `tgl_implies_pgl`. -/
theorem tgl_implies_pgl (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (Htotal : tgl μ f ε) :
    pgl μ f ε :=
  pgl_mon_grading μ f _ _ tsub_le_self (tgl_implies_pgl_strong μ f ε Htotal)

/-- Rocq: `tgl_mon_grading`. -/
theorem tgl_mon_grading (μ : Distr α) (f : α → Prop) (ε ε' : ℝ≥0∞) (Hleq : ε ≤ ε')
    (Hf : tgl μ f ε) : tgl μ f ε' :=
  le_trans (tsub_le_tsub_left Hleq _) Hf

/-- Rocq: `tgl_mon_pred`. -/
theorem tgl_mon_pred (μ : Distr α) (f g : α → Prop) (ε : ℝ≥0∞) (Himp : ∀ a, f a → g a)
    (Hf : tgl μ f ε) : tgl μ g ε := by
  unfold tgl at *
  refine le_trans Hf (prob_mono_event μ fun a ha => ?_)
  simp only [decide_eq_true_eq] at ha ⊢
  exact Himp a ha

/-- Rocq: `tgl_nonneg_grad` (trivial in `ℝ≥0∞`). -/
theorem tgl_nonneg_grad (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (_ : tgl μ f ε) : 0 ≤ ε :=
  zero_le

/-- Rocq: `tgl_dret`. -/
theorem tgl_dret (a : α) (f : α → Prop) (Hfa : f a) : tgl (dret a) f 0 := by
  unfold tgl
  rw [prob_dret_true _ _ (by simp [Hfa])]
  exact tsub_le_self

/-- `(1 - ε) * (1 - ε') ≥ 1 - (ε + ε')` in `ℝ≥0∞` (helper). -/
theorem one_sub_add_le_mul_one_sub (ε ε' : ℝ≥0∞) : 1 - (ε + ε') ≤ (1 - ε) * (1 - ε') := by
  rw [ENNReal.mul_sub (fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self),
    mul_one, tsub_add_eq_tsub_tsub]
  exact tsub_le_tsub_left (mul_le_of_le_one_left zero_le tsub_le_self) _

/-- Rocq: `tgl_dbind`. The hypotheses `0 <= ε`, `0 <= ε'` are dropped. -/
theorem tgl_dbind (h : α → Distr α') (μ₁ : Distr α) (f : α → Prop) (g : α' → Prop)
    (ε ε' : ℝ≥0∞) (Hf : ∀ a, f a → tgl (h a) g ε') (Hμ₁ : tgl μ₁ f ε) :
    tgl (dbind h μ₁) g (ε + ε') := by
  unfold tgl at *
  rw [prob_dbind]
  calc 1 - (ε + ε') ≤ (1 - ε) * (1 - ε') := one_sub_add_le_mul_one_sub ε ε'
    _ ≤ prob μ₁ (fun a => decide (f a)) * (1 - ε') := mul_le_mul_left Hμ₁ _
    _ = ∑' a, (if decide (f a) then μ₁ a else 0) * (1 - ε') := ENNReal.tsum_mul_right.symm
    _ ≤ ∑' a, μ₁ a * prob (h a) (fun b => decide (g b)) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases hfa : f a
        · simp only [hfa, decide_true, ite_true]
          exact mul_le_mul_right (Hf a hfa) _
        · simp [hfa]

/-- Rocq: `tgl_pos_R`. -/
theorem tgl_pos_R (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (Hμ : tgl μ f ε) :
    tgl μ (fun a => f a ∧ 0 < μ a) ε := by
  unfold tgl prob at *
  refine le_trans Hμ (ENNReal.tsum_le_tsum fun a => ?_)
  rcases eq_zero_or_pos (μ a) with h0 | hpos
  · simp [h0]
  · split_ifs <;> simp_all

/-- Rocq: `tgl_ge_1`. -/
theorem tgl_ge_1 (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (h : 1 ≤ ε) : tgl μ f ε := by
  unfold tgl
  rw [tsub_eq_zero_of_le h]
  exact zero_le

/-- Rocq: `tgl_and`. The hypotheses `0 <= ε1 <= 1`, `0 <= ε2 <= 1` are dropped. -/
theorem tgl_and (μ : Distr α) (f g : α → Prop) (ε1 ε2 : ℝ≥0∞) (Hf : tgl μ f ε1)
    (Hg : tgl μ g ε2) : tgl μ (fun a => f a ∧ g a) (ε1 + ε2) := by
  unfold tgl at *
  set pf := prob μ (fun a => decide (f a))
  set pg := prob μ (fun a => decide (g a))
  set pfg := prob μ (fun a => @decide (f a ∧ g a) (Classical.propDecidable _))
  have h1 : 1 ≤ pf + ε1 := tsub_le_iff_right.1 Hf
  have h2 : 1 ≤ pg + ε2 := tsub_le_iff_right.1 Hg
  have hinc : pf + pg ≤ 1 + pfg := by
    calc pf + pg ≤ (∑' a, μ a) + pfg := by
          simp only [pf, pg, pfg, prob]
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum fun a => ?_
          by_cases hf : f a <;> by_cases hg : g a <;> simp [hf, hg]
      _ ≤ 1 + pfg := add_le_add_left (pmf_SeriesC μ) _
  refine tsub_le_iff_right.2 ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 ?_)
  show 1 + 1 ≤ 1 + (pfg + (ε1 + ε2))
  calc 1 + 1 ≤ (pf + ε1) + (pg + ε2) := add_le_add h1 h2
    _ = (pf + pg) + (ε1 + ε2) := by ring
    _ ≤ (1 + pfg) + (ε1 + ε2) := add_le_add_left hinc _
    _ = 1 + (pfg + (ε1 + ε2)) := by ring

/-- Rocq: `tgl_ext`. -/
theorem tgl_ext (μ : Distr α) (f g : α → Prop) (ε : ℝ≥0∞) (Hequiv : ∀ a, f a ↔ g a)
    (Hf : tgl μ f ε) : tgl μ g ε :=
  tgl_mon_pred μ f g ε (fun a => (Hequiv a).1) Hf

/-- Rocq: `tgl_epsilon_limit`. The hypotheses `ε' >= 0` and `EqDecision A` are dropped. -/
theorem tgl_epsilon_limit (μ : Distr α) (f : α → Prop) (ε' : ℝ≥0∞)
    (H' : ∀ ε, ε' < ε → tgl μ f ε) : tgl μ f ε' := by
  unfold tgl at *
  refine tsub_le_iff_right.2 (ENNReal.le_of_forall_pos_le_add fun δ hδ hlt => ?_)
  have hε' : ε' ≠ ∞ := ne_top_of_le_ne_top hlt.ne le_add_self
  have hlt' : ε' < ε' + δ := ENNReal.lt_add_right hε' (by exact_mod_cast hδ.ne')
  have := tsub_le_iff_right.1 (H' _ hlt')
  rwa [← add_assoc] at this

/-- Rocq: `tgl_termination_ineq`. -/
theorem tgl_termination_ineq (μ : Distr α) (f : α → Prop) (ε : ℝ≥0∞) (H2 : tgl μ f ε) :
    1 - ε ≤ ∑' a, μ a :=
  le_trans H2 (ENNReal.tsum_le_tsum fun a => by split_ifs <;> simp)

end tgl_theory

end Prob
