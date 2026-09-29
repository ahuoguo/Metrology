module

public import Metrology.Coneris.Examples.RandomCounter2.RandomCounter
public import Metrology.Coneris.Examples.RandomCounter2.Impl1
public import Metrology.Coneris.Lib.HocapRand

/-!
# Random counter, implementation 3

Ported from clutch/theories/coneris/examples/random_counter2/impl3.v

The counter is incremented by a sample of `rand #4`, rejected (and resampled) until it is `< 4`,
from a freshly allocated hocap tape (`Coneris.Lib.HocapRand`). Presampling uses error
amplification (`ec_ind_amp`) to discard the rejected samples.

## Rocq → Lean mapping
* Section `filter`: `filter_f (n:nat) := (n<4)%nat` is the `Bool`-valued
  `filter_f n := decide (n < 4)` (Rocq's `filter` uses the decidability instance of the
  `Prop`); `filtered_list l := filter filter_f l` is `l.filter filter_f`; `Forall_filter_f`
  (same name) with `Forall (λ x, x ≤ 3) ns` as `∀ x ∈ ns, x ≤ 3`.
* Section `impl3`: the context is as in `Impl1`: `[conerisGS GF] [r1 : rand_spec GF]
  (L : r1.randG GF) [Hfa : ElemG GF frac_authTF]` (the functor `frac_authTF` of
  `inG Σ (frac_authR natR)` is `Impl1.frac_authTF`).
* `new_counter3`, `incr_counter3`, `read_counter3`, `counterG3`, `counter_inv_pred3`,
  `is_counter3`, `new_counter_spec3`, `incr_counter_spec3`, `counter_tapes_presample3`,
  `read_counter_spec3`: same names. The programs are transcribed with the `cpl` notation; the
  Rocq binder `"α "` (with a trailing space, distinct from `"α"`) of the inner `rec` is kept
  literally as the string binder `"α "`.
* `iLöb as "IH" forall (ls Hfilter Φ)` is `iloeb as IH generalizing %ls %Hfilter Hfrag`
  (`Φ` does not change in the recursive call and need not be generalized).
* `ec_ind_amp _ 5` is `ErrorCredit.Induction.amplifying` with `k := 5 : ℝ≥0`;
  `state_update_epsilon_err` as in Rocq. Rocq's `iDestruct (ec_valid ..)` (giving `eps < 1`,
  needed there only for the real-number nonnegativity reasoning) is not needed in `ℝ≥0∞`
  and is omitted; `iCombine "Heps Herr"` is `icombine` giving `↯ (eps + ε)`.
* Errors are `ℝ≥0∞`: `∀ x, 0 <= ε2 x` is dropped; the presampling function
  `λ x, match decide (fin_to_nat x < 4) with left p => ε2 (nat_to_fin p) | _ => ε + 5*eps end`
  is `fun x => if h : (x : ℕ) < 4 then ε2 ⟨x, h⟩ else ε + 5 * eps`. The arithmetic side
  condition (Rocq: `lra`) is the helper `presample3_sum`.
* `random_counter3` (Rocq: `Program Definition`) is a definition (not an instance) over
  `[F : rand_spec GF]`, with `counterG := fun _ => counterG3 GF`; its `Next Obligation`s are
  the (identical) obligation theorems of `Impl1` (`random_counter1_counter_content_*`), since
  the ghost state is the same.

## Added
* `presample3_sum` (the `lra` side condition), `is_counter3_persistent` (automatic obligation).

## Omitted
* The commented-out Rocq code (`rand_inv_create_spec`, `fupd_mask_subseteq` steps,
  `tape_name`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.HocapRand Coneris.Examples.RandomCounter2.RandomCounter
open Coneris.Examples.RandomCounter2.Impl1

namespace Coneris.Examples.RandomCounter2.Impl3

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

/-- Helper (Rocq: the `lra` side condition of `counter_tapes_presample3`). -/
theorem presample3_sum (ε eps : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞)
    (Hineq : ∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε) :
    ∑' x : Fin (4 + 1), 1 / ((4 : ℝ≥0∞) + 1) *
      (if h : (x : ℕ) < 4 then ε2 ⟨x, h⟩ else ε + 5 * eps) ≤ eps + ε := by
  rw [tsum_fintype] at Hineq ⊢
  rw [← Finset.mul_sum] at Hineq
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, dite_true, Fin.val_last, lt_irrefl, dite_false, Fin.eta]
  rw [← Finset.mul_sum, ← mul_add]
  set S := ∑ i : Fin 4, ε2 i
  have h5 : (4 : ℝ≥0∞) + 1 = 5 := by norm_num
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

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
  [Hfa : ElemG GF frac_authTF]

/-- Rocq: `new_counter3`. -/
def new_counter3 : val := cpl_val(λ _, ref(#0))

/-- Rocq: `incr_counter3`. -/
def incr_counter3 : val := cpl_val(
  λ l,
    let α := v(&r1.rand_allocate_tape) #4 in
    (rec f "α " :=
        let n := v(&r1.rand_tape) α #4 in
        if n < #4
        then (faa(l, n), n)
        else f α) α)

/-- Rocq: `read_counter3`. -/
def read_counter3 : val := cpl_val(λ l, !l)

/-- Rocq: `counterG3`. -/
class counterG3 (GF : BundledGFunctors) [conerisGS GF] [r1 : rand_spec GF] : Type where
  counterG3_randG : r1.randG GF
  counterG3_frac_authR : ElemG GF frac_authTF

/-- Rocq: `counter_inv_pred3`. -/
def counter_inv_pred3 (c : val) (γ2 : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt z) ∗
    iOwn (F := frac_authTF) γ2 (●F z))

/-- Rocq: `is_counter3`. -/
def is_counter3 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred3 c γ1)

instance is_counter3_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter3 (GF := GF) N c γ1) := by
  unfold is_counter3; infer_instance

/-- Rocq: `new_counter_spec3`. -/
theorem new_counter_spec3 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter3) #()) @ E
    {{ (c : val), RET c; ∃ γ1, is_counter3 (GF := GF) N c γ1 ∗
        iOwn (F := frac_authTF) γ1 (◯F (0 : ℕ)) }} := by
  unfold new_counter3
  iintro %Φ - HΦ
  wp_pures
  wp_alloc l as Hl
  imod iOwn_alloc (F := frac_authTF) ((●F (0 : ℕ)) • (◯F (0 : ℕ))) (FracAuth.valid trivial)
    with ⟨%γ1, H5, H6⟩
  imod inv_alloc N E (counter_inv_pred3 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred3
    iexists l, 0
    iframe Hl H5
    ipureintro
    rfl
  iapply HΦ
  iexists γ1
  unfold is_counter3
  iframe Hinv' H6

/-- Rocq: `incr_counter_spec3`. -/
theorem incr_counter_spec3 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter3 N c γ1 ∗
        (∀ α, (∃ ls : List ℕ, ⌜ls.filter filter_f = []⌝ ∗ r1.rand_tapes L α (4, ls)) -∗
          state_update E E iprop(∃ n,
            (∃ ls : List ℕ, ⌜ls.filter filter_f = [n]⌝ ∗ r1.rand_tapes L α (4, ls)) ∗
            (∀ z : ℕ, iOwn (F := frac_authTF) γ1 (●F z) ={E \ ↑N}=∗
              iOwn (F := frac_authTF) γ1 (●F (z + n)) ∗ Q z n))) }}
      cpl(v(&incr_counter3) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); Q z n }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold incr_counter3
  wp_pures
  wp_apply r1.rand_allocate_tape_spec L E 4 $$ [] with %α Htape
  · itrivial
  wp_pures
  imod Hvs $$ [Htape] with ⟨%n, ⟨%ls, %Hfilter, Hfrag⟩, Hvs⟩
  · iexists []
    iframe Htape
    ipureintro
    rfl
  iloeb as IH generalizing %ls %Hfilter Hfrag
  wp_pures
  rcases ls with _ | ⟨hd, ls⟩
  · simp at Hfilter
  wp_apply r1.rand_tape_spec_some L E α 4 hd ls $$ Hfrag with Hfrag
  wp_pures
  by_cases K : hd < 4
  · simp only [K, decide_true]
    wp_pures
    wp_bind (FAA _ _)
    unfold is_counter3 counter_inv_pred3
    iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
    subst Hc
    wp_faa
    have Hhd : hd = n := by
      have : filter_f hd = true := by simp [filter_f, K]
      rw [List.filter_cons_of_pos this] at Hfilter
      exact (List.cons.inj Hfilter).1
    subst Hhd
    imod Hvs $$ H6 with ⟨H6, HQ⟩
    imod Hclose $$ [H5 H6] with -
    · inext
      iexists l, z + hd
      rw [Nat.cast_add]
      iframe H5 H6
      ipureintro
      rfl
    imodintro
    wp_pures
    iapply HΦ $$ HQ
  · simp only [K, decide_false]
    wp_pure
    wp_pure
    iapply IH $$ %ls %_ Hfrag HΦ Hvs
    have : filter_f hd = false := by simp [filter_f, K]
    rw [List.filter_cons_of_neg (by simp [this])] at Hfilter
    exact Hfilter

/-- Rocq: `counter_tapes_presample3`. -/
theorem counter_tapes_presample3 (N : Namespace) (E : CoPset) (γ1 : GName) (c : val) (α : val)
    (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (_Hsubset : ↑N ⊆ E)
    (Hineq : ∑' n : Fin 4, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter3 N c γ1 -∗
      (∃ ls : List ℕ, ⌜ls.filter filter_f = []⌝ ∗ r1.rand_tapes L α (4, ls)) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗
        (∃ ls : List ℕ, ⌜ls.filter filter_f = [(n : ℕ)]⌝ ∗ r1.rand_tapes L α (4, ls))) := by
  iintro #Hinv Hfrag Herr
  imod state_update_epsilon_err E with ⟨%ep, %Heps, Heps⟩
  irevert Hfrag Herr
  iapply ErrorCredit.Induction.amplifying (k := (5 : ℝ≥0)) Heps (by norm_num) $$ [] Heps
  imodintro
  iintro %eps %Heps' #IH Heps ⟨%ls, %Hfilter, Hfrag⟩ Herr
  icombine Heps Herr as Herr'
  imod r1.rand_tapes_presample L E α 4 ls (eps + ε)
      (fun x => if h : (x : ℕ) < 4 then ε2 ⟨x, h⟩ else ε + 5 * eps)
      (presample3_sum ε eps ε2 Hineq) $$ Hfrag Herr' with ⟨%n, Herr, Hfrag⟩
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
  · simp only [K, dite_false]
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
        (∀ z : ℕ, iOwn (F := frac_authTF) γ1 (●F z) ={E \ ↑N}=∗
          iOwn (F := frac_authTF) γ1 (●F z) ∗ Q z) }}
      cpl(v(&read_counter3) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt n'); Q n' }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter3
  wp_pure
  unfold is_counter3 counter_inv_pred3
  iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  imod Hclose $$ [H5 H6] with -
  · inext
    iexists l, z
    iframe H5 H6
    ipureintro
    rfl
  imodintro
  iapply HΦ $$ HQ

end impl3

/-- Rocq: `random_counter3` (a `Program Definition`). -/
@[instance_reducible]
def random_counter3 {GF : BundledGFunctors} [conerisGS GF] [F : rand_spec GF] :
    random_counter GF where
  new_counter := new_counter3
  incr_counter := incr_counter3
  read_counter := read_counter3
  counterG := fun _ => counterG3 GF
  counter_name := GName
  is_counter L N c γ1 := is_counter3 (Hfa := (L : counterG3 GF).counterG3_frac_authR) N c γ1
  counter_tapes L α n :=
    iprop(∃ ls : List ℕ, ⌜ls.filter filter_f = (match n with | some x => [x] | none => [])⌝ ∗
      F.rand_tapes (L : counterG3 GF).counterG3_randG α (4, ls))
  counter_content_auth L γ z :=
    iOwn (E := (L : counterG3 GF).counterG3_frac_authR) (F := frac_authTF) γ (●F z)
  counter_content_frag L γ f z :=
    iOwn (E := (L : counterG3 GF).counterG3_frac_authR) (F := frac_authTF) γ (◯F{f} z)
  is_counter_persistent L N c γ1 :=
    is_counter3_persistent (Hfa := (L : counterG3 GF).counterG3_frac_authR) N c γ1
  counter_tapes_timeless L α n := by infer_instance
  counter_content_auth_timeless L γ z :=
    letI := (L : counterG3 GF).counterG3_frac_authR; iOwn_timeless
  counter_content_frag_timeless L γ f z :=
    letI := (L : counterG3 GF).counterG3_frac_authR; iOwn_timeless
  counter_tapes_presample L :=
    counter_tapes_presample3 (Hfa := (L : counterG3 GF).counterG3_frac_authR)
      (L : counterG3 GF).counterG3_randG
  counter_content_auth_exclusive L :=
    random_counter1_counter_content_auth_exclusive
      (Hfa := (L : counterG3 GF).counterG3_frac_authR)
  counter_content_less_than L :=
    random_counter1_counter_content_less_than (Hfa := (L : counterG3 GF).counterG3_frac_authR)
  counter_content_frag_combine L :=
    random_counter1_counter_content_frag_combine
      (Hfa := (L : counterG3 GF).counterG3_frac_authR)
  counter_content_agree L :=
    random_counter1_counter_content_agree (Hfa := (L : counterG3 GF).counterG3_frac_authR)
  counter_content_update L :=
    random_counter1_counter_content_update (Hfa := (L : counterG3 GF).counterG3_frac_authR)
  new_counter_spec L :=
    new_counter_spec3 (Hfa := (L : counterG3 GF).counterG3_frac_authR)
  incr_counter_spec L :=
    incr_counter_spec3 (Hfa := (L : counterG3 GF).counterG3_frac_authR)
      (L : counterG3 GF).counterG3_randG
  read_counter_spec L :=
    read_counter_spec3 (Hfa := (L : counterG3 GF).counterG3_frac_authR)

end Coneris.Examples.RandomCounter2.Impl3
