module

public import Metrology.Coneris.Examples.RandomCounter.RandomCounter
public import Metrology.Coneris.Lib.HocapRand

/-!
# Random counter: third implementation (rejection sampling on a `rand_spec` tape with bound 4)

Ported from clutch/theories/coneris/examples/random_counter/impl3.v

## Rocq → Lean mapping
* Section `filter`: `filter_f`, `filtered_list`, `Forall_filter_f` (same names). Rocq's
  `filter_f (n:nat) := (n<4)%nat` (a decidable `Prop`, used through `filter`) is the boolean
  predicate `filter_f n = decide (n < 4)`, and `filter filter_f l` is `l.filter filter_f`.
  `Forall (λ x, x ≤ 3) ns` is `∀ x ∈ ns, x ≤ 3`.
* Section `impl3`: the context `H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ,
  !inG Σ (frac_authR natR)` is `[conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
  [ElemG GF frac_authF_nat]` (as in `Coneris.Lib.HocapRand`, `L` is explicit).
* `new_counter3`, `allocate_tape3`, `incr_counter_tape3`, `read_counter3`: same names,
  transcribed with the `cpl` notation (`#4%nat` is `#4`).
* `counterG3` is the Lean `class counterG3 GF'` (over `[r1 : rand_spec GF]`); in
  `random_counter3` its field `counterG3_frac_authR` is a local instance and `counterG3_randG`
  is passed as `L`.
* `own γ (●F z)` / `own γ (◯F{f} z)` are `own_auth_nat γ z` / `own_frag_nat γ f z` of
  `RandomCounter`.
* `counter_inv_pred3`, `is_counter3`, `new_counter_spec3`, `allocate_tape_spec3`,
  `incr_counter_tape_spec_some3`, `counter_tapes_presample3`, `read_counter_spec3`: same names.
  - `iLöb as "IH" forall (ls Hfilter Φ) "Hfrag"` is `iloeb as IH generalizing %ls %Hfilter`
    (spatial hypotheses, among them `Hfrag` and `HΦ`, are always generalised).
  - In `counter_tapes_presample3` the hypothesis `∀ x, 0 <= ε2 x` is dropped (`ℝ≥0∞`);
    `ec_ind_amp _ 5` is `ErrorCredit.Induction.amplifying` with `k := 5 : ℝ≥0`; the error
    function `λ x, match decide (fin_to_nat x < 4) with left p => ε2 (nat_to_fin p) | _ =>
    ε + 5*eps end` is `λ x, if h : (x : ℕ) < 4 then ε2 ⟨x, h⟩ else ε + 5 * eps`.
* `random_counter3` (Rocq: `Program Definition`) is a definition (not an instance) over
  `[r1 : rand_spec GF]`. Its `Next Obligation`s are the helper theorems
  `random_counter3_counter_tapes_exclusive`, `random_counter3_counter_tapes_valid`, and the
  shared `frac_auth_nat_*` lemmas of `RandomCounter`.

## Omitted
* The commented-out Rocq code (`rand_inv_create_spec`, `fupd_mask_subseteq`, `tape_name`,
  `counter_tapes_auth`).

## Added
* `presample3_sum` (the `SeriesC_finite_foldr ... lra` step), `counter_inv_pred3_timeless`,
  `is_counter3_persistent`.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.iris.dupNamespace false

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.HocapRand Coneris.Examples.RandomCounter.RandomCounter

namespace Coneris.Examples.RandomCounter.Impl3

section filter

/-- Rocq: `filter_f`. -/
def filter_f (n : ℕ) : Bool := decide (n < 4)

/-- Rocq: `filtered_list`. -/
def filtered_list (l : List ℕ) : List ℕ := l.filter filter_f

/-- Rocq: `Forall_filter_f`. -/
theorem Forall_filter_f (ns : List ℕ) (H : ∀ x ∈ ns, x ≤ 3) : ns.filter filter_f = ns := by
  rw [List.filter_eq_self]
  intro a ha
  have := H a ha
  simp only [filter_f, decide_eq_true_eq]
  omega

end filter

/-- Helper (Rocq: the `SeriesC_finite_foldr ... lra` side condition of
`counter_tapes_presample3`). -/
theorem presample3_sum (ε eps : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞)
    (Hineq : ∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε) :
    ∑' x : Fin (4 + 1), 1 / (((4 : ℕ) : ℝ≥0∞) + 1) *
      (if h : (x : ℕ) < 4 then ε2 ⟨x, h⟩ else ε + 5 * eps) ≤ eps + ε := by
  rw [tsum_fintype] at Hineq ⊢
  rw [← Finset.mul_sum] at Hineq
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, dite_true, Fin.val_last, lt_irrefl, dite_false,
    Fin.eta]
  rw [← Finset.mul_sum, ← mul_add]
  set S := ∑ i : Fin 4, ε2 i
  have h5 : ((4 : ℕ) : ℝ≥0∞) + 1 = 5 := by norm_num
  rw [h5]
  have hS4 : S ≤ 4 * ε := by
    have := mul_le_mul_right Hineq 4
    rwa [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      at this
  calc 1 / 5 * (S + (ε + 5 * eps))
      ≤ 1 / 5 * (4 * ε + (ε + 5 * eps)) := by gcongr
    _ = 1 / 5 * (5 * (ε + eps)) := by ring
    _ = eps + ε := by
      rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul,
        add_comm]

section impl3

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF]

/-- Rocq: `new_counter3`. -/
def new_counter3 : val := cpl_val(λ _, ref(#0))

/-- Rocq: `allocate_tape3`. -/
def allocate_tape3 : val := cpl_val(λ _, v(&r1.rand_allocate_tape) #4)

/-- Rocq: `incr_counter_tape3`. -/
def incr_counter_tape3 : val := cpl_val(
  rec f l α :=
    let n := v(&r1.rand_tape) α #4 in
    if n < #4
    then (faa(l, n), n)
    else f l α)

/-- Rocq: `read_counter3`. -/
def read_counter3 : val := cpl_val(λ l, !l)

/-- Rocq: `counterG3`. -/
class counterG3 (GF' : BundledGFunctors) where
  counterG3_randG : r1.randG GF'
  counterG3_frac_authR : ElemG GF' frac_authF_nat

attribute [instance_reducible] counterG3.counterG3_frac_authR

variable (L : r1.randG GF) [ElemG GF frac_authF_nat]

/-- Rocq: `counter_inv_pred3`. -/
def counter_inv_pred3 (c : val) (γ2 : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt (z : ℤ)) ∗
    own_auth_nat γ2 z)

instance counter_inv_pred3_timeless (c : val) (γ2 : GName) :
    Timeless (counter_inv_pred3 c γ2) := by
  unfold counter_inv_pred3; infer_instance

/-- Rocq: `is_counter3`. -/
def is_counter3 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred3 c γ1)

instance is_counter3_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter3 N c γ1) := by
  unfold is_counter3; infer_instance

/-- Rocq: `new_counter_spec3`. -/
theorem new_counter_spec3 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter3) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter3 N c γ1 ∗ own_frag_nat γ1 1 0 }} := by
  unfold is_counter3
  iintro %Φ - HΦ
  unfold new_counter3
  wp_pures
  wp_alloc l as Hl
  imod frac_auth_nat_alloc with ⟨%γ1, H5, H6⟩
  imod inv_alloc N E (counter_inv_pred3 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred3
    iexists l, 0
    iframe
    ipureintro
    rfl
  iapply HΦ
  iexists γ1
  iframe Hinv' H6

/-- Rocq: `allocate_tape_spec3`. -/
theorem allocate_tape_spec3 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (_Hsubset : ↑N ⊆ E) :
    {{ is_counter3 N c γ1 }} cpl(v(&allocate_tape3) #()) @ E
    {{ v, RET v; ∃ ls : List ℕ, ⌜ls.filter filter_f = []⌝ ∗ r1.rand_tapes L v (4, ls) }} := by
  iintro %Φ #Hinv HΦ
  unfold allocate_tape3
  wp_pures
  wp_apply r1.rand_allocate_tape_spec L E 4 $$ [] with %v Hv
  · itrivial
  iapply HΦ
  iexists []
  iframe Hv
  ipureintro
  rfl

/-- Rocq: `incr_counter_tape_spec_some3`. -/
theorem incr_counter_tape_spec_some3 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (α : val) (n : ℕ) (ns : List ℕ) (Hsubset : ↑N ⊆ E) :
    {{ is_counter3 N c γ1 ∗
        (∃ ls : List ℕ, ⌜ls.filter filter_f = n :: ns⌝ ∗ r1.rand_tapes L α (4, ls)) ∗
        (∀ z : ℕ, own_auth_nat γ1 z ={E \ ↑N}=∗ own_auth_nat γ1 (z + n) ∗ Q z) }}
      cpl(v(&incr_counter_tape3) v(&c) v(&α)) @ E
    {{ (z : ℕ), RET cpl_val((#z, #n));
        (∃ ls : List ℕ, ⌜ls.filter filter_f = ns⌝ ∗ r1.rand_tapes L α (4, ls)) ∗ Q z }} := by
  unfold is_counter3 counter_inv_pred3
  iintro %Φ ⟨#Hinv, ⟨%ls, %Hfilter, Hfrag⟩, Hvs⟩ HΦ
  unfold incr_counter_tape3
  iloeb as IH generalizing %ls %Hfilter
  wp_pures
  rcases ls with _ | ⟨hd, ls⟩
  · simp at Hfilter
  wp_apply r1.rand_tape_spec_some L E α 4 hd ls $$ Hfrag with Hfrag
  wp_pures
  by_cases K : hd < 4
  · simp only [K, decide_true]
    wp_pures
    wp_bind (FAA _ _)
    iinv Hinv with >⟨%l, %z, %Hc, H5, H6⟩ Hclose
    subst Hc
    wp_faa
    have hK : filter_f hd = true := by simp [filter_f, K]
    rw [List.filter_cons_of_pos hK] at Hfilter
    obtain ⟨rfl, Hfilter'⟩ := List.cons.inj Hfilter
    imod Hvs $$ H6 with ⟨H6, HQ⟩
    imod Hclose $$ [H5 H6]
    · inext
      iexists l, z + hd
      iframe H6
      isplitr
      · ipureintro; rfl
      rw [Nat.cast_add]
      iexact H5
    imodintro
    wp_pures
    iapply HΦ
    iframe HQ
    iexists ls
    iframe Hfrag
    ipureintro
    exact Hfilter'
  · simp only [K, decide_false]
    wp_pure
    have hK : ¬ filter_f hd = true := by simp [filter_f, K]
    rw [List.filter_cons_of_neg hK] at Hfilter
    iapply IH $$ %ls %Hfilter Hfrag Hvs [HΦ]
    inext
    iexact HΦ

/-- Rocq: `counter_tapes_presample3`. -/
theorem counter_tapes_presample3 (N : Namespace) (E : CoPset) (γ1 : GName) (c α : val)
    (ns : List ℕ) (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (_Hsubset : ↑N ⊆ E)
    (Hineq : ∑' n, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter3 N c γ1 -∗
      (∃ ls : List ℕ, ⌜ls.filter filter_f = ns⌝ ∗ r1.rand_tapes L α (4, ls)) -∗
      ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗
        (∃ ls : List ℕ, ⌜ls.filter filter_f = ns ++ [(n : ℕ)]⌝ ∗
          r1.rand_tapes L α (4, ls))) := by
  iintro #Hinv Hfrag Herr
  imod state_update_epsilon_err E with ⟨%ep, %Heps, Heps⟩
  irevert Hfrag Herr
  iapply ErrorCredit.Induction.amplifying (k := (5 : ℝ≥0)) Heps (by norm_num) $$ [] Heps
  imodintro
  iintro %eps %Heps' #IH Heps ⟨%ls, %Hfilter, Hfrag⟩ Herr
  icombine Heps Herr as Herr'
  imod r1.rand_tapes_presample L E α 4 ls (eps + ε)
      (fun x => if h : (x : ℕ) < 4 then ε2 ⟨x, h⟩ else ε + 5 * eps)
      (presample3_sum ε eps ε2 Hineq) $$ Hfrag Herr'
      with ⟨%n, Herr, Hfrag⟩
  by_cases K : (n : ℕ) < 4
  · -- accept
    simp only [K, dite_true]
    imodintro
    iexists ⟨n, K⟩
    iframe Herr
    iexists ls ++ [(n : ℕ)]
    iframe Hfrag
    ipureintro
    rw [List.filter_append, Hfilter]
    simp [filter_f, K]
  · -- reject
    simp only [K, dite_false]
    ihave ⟨Hε, Heps⟩ := ErrorCredit.split $$ Herr
    iapply IH $$ [Heps] [Hfrag] Hε
    · iapply ErrorCredit.ext $$ Heps
      push_cast
      rfl
    iexists ls ++ [(n : ℕ)]
    iframe Hfrag
    ipureintro
    rw [List.filter_append, Hfilter]
    simp [filter_f, K]

/-- Rocq: `read_counter_spec3`. -/
theorem read_counter_spec3 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter3 N c γ1 ∗
        (∀ z : ℕ, own_auth_nat γ1 z ={E \ ↑N}=∗ own_auth_nat γ1 z ∗ Q z) }}
      cpl(v(&read_counter3) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }} := by
  unfold is_counter3 counter_inv_pred3
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter3
  wp_pure
  iinv Hinv with >⟨%l, %z, %Hc, H5, H6⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  imod Hclose $$ [H5 H6]
  · inext
    iexists l, z
    iframe
    ipureintro; rfl
  imodintro
  iapply HΦ $$ HQ

end impl3

/-! ## `random_counter3` and its obligations -/

section obligations

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF]

attribute [local instance] counterG3.counterG3_frac_authR

/-- Rocq: first `Next Obligation` of `random_counter3` (`counter_tapes_exclusive`). -/
theorem random_counter3_counter_tapes_exclusive (K : counterG3 (r1 := r1) GF) (α : val)
    (ns ns' : List ℕ) :
    ⊢ iprop(∃ ls : List ℕ, ⌜ls.filter filter_f = ns⌝ ∗ r1.rand_tapes K.counterG3_randG α (4, ls)) -∗
      iprop(∃ ls : List ℕ, ⌜ls.filter filter_f = ns'⌝ ∗
        r1.rand_tapes K.counterG3_randG α (4, ls)) -∗ False := by
  iintro ⟨%ls1, -, H1⟩ ⟨%ls2, -, H2⟩
  iapply r1.rand_tapes_exclusive $$ H1 H2

/-- Rocq: second `Next Obligation` of `random_counter3` (`counter_tapes_valid`). -/
theorem random_counter3_counter_tapes_valid (K : counterG3 (r1 := r1) GF) (α : val)
    (ns : List ℕ) :
    ⊢ iprop(∃ ls : List ℕ, ⌜ls.filter filter_f = ns⌝ ∗ r1.rand_tapes K.counterG3_randG α (4, ls)) -∗
      ⌜∀ n ∈ ns, n ≤ 3⌝ := by
  iintro ⟨%ls, %H, -⟩
  ipureintro
  subst H
  intro n hn
  have := (List.mem_filter.1 hn).2
  simp only [filter_f, decide_eq_true_eq] at this
  omega

/-- Rocq: `random_counter3` (a `Program Definition`). -/
@[instance_reducible]
def random_counter3 : random_counter GF where
  new_counter := new_counter3
  allocate_tape := allocate_tape3
  incr_counter_tape := incr_counter_tape3
  read_counter := read_counter3
  counterG := counterG3 (r1 := r1)
  counter_name := GName
  is_counter _ N c γ1 := is_counter3 N c γ1
  counter_tapes K α ns :=
    iprop(∃ ls : List ℕ, ⌜ls.filter filter_f = ns⌝ ∗ r1.rand_tapes K.counterG3_randG α (4, ls))
  counter_content_auth _ γ z := own_auth_nat γ z
  counter_content_frag _ γ f z := own_frag_nat γ f z
  is_counter_persistent _ N c γ1 := is_counter3_persistent N c γ1
  counter_tapes_timeless _ _ _ := inferInstance
  counter_content_auth_timeless _ _ _ := inferInstance
  counter_content_frag_timeless _ _ _ _ := inferInstance
  counter_tapes_exclusive K := random_counter3_counter_tapes_exclusive K
  counter_tapes_valid K := random_counter3_counter_tapes_valid K
  counter_tapes_presample K := counter_tapes_presample3 K.counterG3_randG
  counter_content_auth_exclusive _ := frac_auth_nat_auth_exclusive
  counter_content_less_than _ := frac_auth_nat_less_than
  counter_content_frag_combine _ := frac_auth_nat_frag_combine
  counter_content_agree _ := frac_auth_nat_agree
  counter_content_update _ := frac_auth_nat_update
  new_counter_spec _ := new_counter_spec3
  allocate_tape_spec K := allocate_tape_spec3 K.counterG3_randG
  incr_counter_tape_spec_some K := incr_counter_tape_spec_some3 K.counterG3_randG
  read_counter_spec _ := read_counter_spec3

end obligations

end Coneris.Examples.RandomCounter.Impl3
