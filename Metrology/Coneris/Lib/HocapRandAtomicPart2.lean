module

public import Metrology.Coneris.Lib.HocapRandAtomic

/-!
# Hocap atomic rand specs, part 2: the rejection sampler

Ported from clutch/theories/coneris/lib/hocap_rand_atomic.v (section `impl3`).

## Rocq → Lean mapping
* `rand_tapes3`, `rand_atomic_spec3` (Rocq: `#[local] Program Definition`, a definition here);
  the `Next Obligation`s are the helper theorems `rand_atomic_spec3_*`.
* `filter (λ x, x <= tb) ns'` is `ns'.filter (fun x => decide (x ≤ tb))`.
* The presampling obligation uses `ec_ind_amp` (iris-lean: `ErrorCredit.Induction.amplifying`)
  with `k = S (S tb)` as in Rocq. The Rocq error function
  `λ x, match decide (fin_to_nat x < S tb) with left p => ε2 (nat_to_fin p) | _ => ε + S (S tb) * eps end`
  is the helper `rej_err tb ε2 (ε + (tb + 2) * eps)`, and the Rocq series manipulation
  (`SeriesC_split_elem`, `SeriesC_nat_bounded`, ...) is the helper `rej_err_sum` (a finite sum
  over `Fin (tb + 2)` split with `Fin.sum_univ_castSucc`).

## Added helpers
`rej_err`, `rej_err_castSucc`, `rej_err_last`, `rej_err_sum`, `rand_tapes3_timeless`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.HocapRandAtomic

/-! ## Error redistribution of the rejection sampler (pure helpers) -/

/-- Helper: the error function of the rejection-sampling presampling step (Rocq: the
`match decide (fin_to_nat x < S tb) ...` function). -/
def rej_err (tb : ℕ) (ε2 : Fin (tb + 1) → ℝ≥0∞) (e : ℝ≥0∞) (x : Fin (tb + 1 + 1)) : ℝ≥0∞ :=
  if h : (x : ℕ) < tb + 1 then ε2 ⟨x, h⟩ else e

theorem rej_err_castSucc (tb : ℕ) (ε2 : Fin (tb + 1) → ℝ≥0∞) (e : ℝ≥0∞) (i : Fin (tb + 1)) :
    rej_err tb ε2 e i.castSucc = ε2 i := by
  have h : ((i.castSucc : Fin (tb + 1 + 1)) : ℕ) < tb + 1 := by simpa using i.isLt
  unfold rej_err
  simp only [h, ↓reduceDIte]
  rfl

theorem rej_err_last (tb : ℕ) (ε2 : Fin (tb + 1) → ℝ≥0∞) (e : ℝ≥0∞) :
    rej_err tb ε2 e (Fin.last (tb + 1)) = e := by
  simp [rej_err]

/-- Helper: the Rocq series inequality of the presampling obligation of `rand_atomic_spec3`. -/
theorem rej_err_sum (tb : ℕ) (ε : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞)
    (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) (eps : ℝ≥0∞) :
    ∑' n : Fin (tb + 1 + 1), 1 / (((tb + 1 : ℕ) : ℝ≥0∞) + 1) *
      rej_err tb ε2 (ε + ((tb : ℝ≥0∞) + 2) * eps) n ≤ ε + eps := by
  rw [tsum_fintype] at Hsum ⊢
  rw [Fin.sum_univ_castSucc]
  simp only [rej_err_castSucc, rej_err_last]
  rw [← Finset.mul_sum] at Hsum ⊢
  rw [← mul_add]
  set S := ∑ i, ε2 i
  have h1 : ((tb : ℝ≥0∞) + 1) ≠ 0 := by simp
  have h1' : ((tb : ℝ≥0∞) + 1) ≠ ∞ := by simp
  have h2 : ((tb : ℝ≥0∞) + 2) ≠ 0 := by simp
  have h2' : ((tb : ℝ≥0∞) + 2) ≠ ∞ := by simp
  have hS : S ≤ ((tb : ℝ≥0∞) + 1) * ε := by
    calc S = ((tb : ℝ≥0∞) + 1) * (1 / ((tb : ℝ≥0∞) + 1) * S) := by
          rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel h1 h1', one_mul]
      _ ≤ _ := mul_le_mul_right Hsum _
  have hc : (((tb + 1 : ℕ) : ℝ≥0∞) + 1) = (tb : ℝ≥0∞) + 2 := by push_cast; ring
  rw [hc]
  calc 1 / ((tb : ℝ≥0∞) + 2) * (S + (ε + ((tb : ℝ≥0∞) + 2) * eps))
      ≤ 1 / ((tb : ℝ≥0∞) + 2) * (((tb : ℝ≥0∞) + 2) * (ε + eps)) := by
        gcongr
        calc S + (ε + ((tb : ℝ≥0∞) + 2) * eps)
            ≤ ((tb : ℝ≥0∞) + 1) * ε + (ε + ((tb : ℝ≥0∞) + 2) * eps) := by gcongr
          _ = ((tb : ℝ≥0∞) + 2) * (ε + eps) := by ring
    _ = ε + eps := by rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel h2 h2', one_mul]

/-! ## Implementation 3 (the rejection sampler) -/

section impl3

variable {GF : BundledGFunctors} [conerisGS GF] (tb : ℕ)

/-- Rocq: `rand_tapes3`. -/
def rand_tapes3 (α : val) (ns : List ℕ) : IProp GF :=
  iprop(∃ (α' : Loc) (ns' : List ℕ), ⌜LitV (LitLbl α') = α⌝ ∗
    ⌜ns'.filter (fun x => decide (x ≤ tb)) = ns⌝ ∗ α' ↪N (tb + 1; ns'))

instance rand_tapes3_timeless (α : val) (ns : List ℕ) :
    Timeless (rand_tapes3 (GF := GF) tb α ns) := by
  unfold rand_tapes3; infer_instance

/-- Rocq: `rand_allocate_tape` of `rand_atomic_spec3`. -/
def rand_allocate_tape3 : val := cpl_val(λ <>, alloc(#((tb + 1 : ℕ))))

/-- Rocq: `rand_tape` of `rand_atomic_spec3`. -/
def rand_tape3 : val :=
  cpl_val(rec f α := let res := rand(α) #((tb + 1 : ℕ)); if res ≤ #tb then res else f α)

/-- Rocq: first `Next Obligation` of `rand_atomic_spec3`. -/
theorem rand_atomic_spec3_rand_tapes_exclusive (α : val) (ns ns' : List ℕ) :
    ⊢@{IProp GF} rand_tapes3 tb α ns -∗ rand_tapes3 tb α ns' -∗ False := by
  unfold rand_tapes3
  iintro ⟨%a1, %l1, %h1, -, H1⟩ ⟨%a2, %l2, %h2, -, H2⟩
  rw [← h2] at h1
  cases h1
  iapply tapeN_tapeN_contradict $$ H1 H2

/-- Rocq: second `Next Obligation` of `rand_atomic_spec3`. -/
theorem rand_atomic_spec3_rand_tapes_valid (α : val) (ns : List ℕ) :
    ⊢@{IProp GF} rand_tapes3 tb α ns -∗ ⌜∀ n ∈ ns, n ≤ tb⌝ := by
  unfold rand_tapes3
  iintro ⟨%a, %l, -, %Hfilter, -⟩
  ipureintro
  subst Hfilter
  intro n hn
  simpa using (List.mem_filter.1 hn).2

/-- Rocq: third `Next Obligation` of `rand_atomic_spec3`. -/
theorem rand_atomic_spec3_rand_tapes_presample (E : CoPset) (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞) (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢@{IProp GF} rand_tapes3 tb α ns -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes3 tb α (ns ++ [(n : ℕ)])) := by
  iintro Hfrag Herr
  imod state_update_epsilon_err E with ⟨%ep, %Hep, Heps⟩
  have hk : (1 : NNReal) < (tb : NNReal) + 2 := by
    have : (0 : NNReal) ≤ tb := by positivity
    exact lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left this)
  iapply ErrorCredit.Induction.amplifying (P := iprop(rand_tapes3 tb α ns -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes3 tb α (ns ++ [(n : ℕ)]))))
    Hep hk $$ [] Heps Hfrag Herr
  iintro !> %eps %_ #IH Heps Hfrag Herr
  iunfold rand_tapes3 at Hfrag
  icases Hfrag with ⟨%a, %ns', %ha, %Hfilter, Ht⟩
  icombine Herr Heps as Herr'
  imod state_update_presample_exp E a (tb + 1) ns' (ε + eps)
      (rej_err tb ε2 (ε + ((tb : ℝ≥0∞) + 2) * eps)) (rej_err_sum tb ε ε2 Hsum eps) $$ Ht Herr'
    with ⟨%x, Ht, Herr⟩
  by_cases hx : (x : ℕ) < tb + 1
  · -- accept
    ihave Herr := ErrorCredit.ext (show rej_err tb ε2 (ε + ((tb : ℝ≥0∞) + 2) * eps) x =
      ε2 ⟨x, hx⟩ by simp [rej_err, hx]) $$ Herr
    imodintro
    iexists ⟨x, hx⟩
    iframe Herr
    iunfold rand_tapes3
    iexists a, ns' ++ [(x : ℕ)]
    iframe Ht
    ipureintro
    refine ⟨ha, ?_⟩
    rw [List.filter_append, Hfilter]
    simp [Nat.lt_succ_iff.1 hx]
  · -- reject
    ihave Herr := ErrorCredit.ext (show rej_err tb ε2 (ε + ((tb : ℝ≥0∞) + 2) * eps) x =
      ε + (((tb : NNReal) + 2 : NNReal) : ℝ≥0∞) * eps by simp [rej_err, hx]) $$ Herr
    ihave ⟨Hε, Hk⟩ := ErrorCredit.split $$ Herr
    iapply IH $$ Hk [Ht] Hε
    iunfold rand_tapes3
    iexists a, ns' ++ [(x : ℕ)]
    iframe Ht
    ipureintro
    refine ⟨ha, ?_⟩
    rw [List.filter_append, Hfilter]
    simp [Nat.lt_succ_iff.not.1 hx]

/-- Rocq: fourth `Next Obligation` of `rand_atomic_spec3`. -/
theorem rand_atomic_spec3_rand_allocate_tape_spec (E : CoPset) :
    {{ True }} cpl(v(&(rand_allocate_tape3 tb)) #()) @ E
    {{ v, RET v; rand_tapes3 (GF := GF) tb v [] }} := by
  iintro %Φ - HΦ
  wp_lam
  wp_alloctape α as Hα
  iapply HΦ
  unfold rand_tapes3
  iexists α, []
  iframe Hα
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Rocq: fifth `Next Obligation` of `rand_atomic_spec3`. -/
theorem rand_atomic_spec3_rand_tape_spec_some (E : CoPset) (α : val) :
    ⊢@{IProp GF} iprop(<<{ ∀∀ (n : ℕ) (ns : List ℕ), rand_tapes3 tb α (n :: ns) }>>
      cpl(v(&(rand_tape3 tb)) v(&α)) @ E
      <<{ rand_tapes3 tb α ns | RET LitV (LitInt (n : ℤ)) }>>) := by
  iunfold atomic_wp
  iintro %Φ AU
  iapply fupd_pgl_wp
  imod AU with ⟨%⟨n, ns, ⟨⟩⟩, Ht, Habort, -⟩
  tele_simp
  iunfold rand_tapes3 at Ht
  icases Ht with ⟨%a, %ns', %h, %Hfilter, Ht⟩
  subst h
  imod Habort $$ [Ht] with AU
  · iunfold rand_tapes3
    iexists a, ns'
    iframe Ht
    ipureintro
    exact ⟨rfl, Hfilter⟩
  imodintro
  clear Hfilter ns' n ns
  iloeb as IH generalizing AU
  wp_rec
  wp_bind (Rand _ _)
  imod AU with ⟨%⟨n, ns, ⟨⟩⟩, Ht, Hac⟩
  tele_simp
  iunfold rand_tapes3 at Ht
  icases Ht with ⟨%a', %ns', %h, %Hfilter, Ht⟩
  cases h
  cases ns' with
  | nil => simp at Hfilter
  | cons m ns' =>
    by_cases hm : m = tb + 1
    · -- reject case
      icases Hac with ⟨Habort, -⟩
      wp_randtape as %_
      imod Habort $$ [Ht] with AU
      · iunfold rand_tapes3
        iexists a, ns'
        iframe Ht
        ipureintro
        refine ⟨rfl, ?_⟩
        simpa [hm] using Hfilter
      imodintro
      wp_pures
      rw [decide_eq_false (by omega)]
      wp_if
      iapply IH $$ AU
    · -- accept case
      icases Hac with ⟨-, Hcommit⟩
      wp_randtape as %Hle
      have hm' : m ≤ tb := by omega
      rw [List.filter_cons_of_pos (by simpa using hm')] at Hfilter
      cases Hfilter
      imod Hcommit $$ [Ht] with HΦ
      · iunfold rand_tapes3
        iexists a, ns'
        iframe Ht
        ipureintro
        exact ⟨rfl, rfl⟩
      imodintro
      wp_pures
      rw [decide_eq_true hm']
      wp_pures
      iexact HΦ

/-- Rocq: `rand_atomic_spec3` (a `#[local] Program Definition`). -/
@[instance_reducible]
def rand_atomic_spec3 : rand_atomic_spec tb GF where
  rand_allocate_tape := rand_allocate_tape3 tb
  rand_tape := rand_tape3 tb
  rand_tapes := rand_tapes3 tb
  rand_tapes_timeless := rand_tapes3_timeless tb
  rand_tapes_exclusive := rand_atomic_spec3_rand_tapes_exclusive tb
  rand_tapes_valid := rand_atomic_spec3_rand_tapes_valid tb
  rand_tapes_presample := rand_atomic_spec3_rand_tapes_presample tb
  rand_allocate_tape_spec := rand_atomic_spec3_rand_allocate_tape_spec tb
  rand_tape_spec_some := rand_atomic_spec3_rand_tape_spec_some tb

end impl3

end Coneris.Lib.HocapRandAtomic
