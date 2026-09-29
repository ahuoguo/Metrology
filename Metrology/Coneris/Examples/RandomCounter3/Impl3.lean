module

public import Metrology.Coneris.Examples.RandomCounter3.RandomCounter
public import Metrology.Coneris.Lib.HocapRand

/-!
# Random counter, implementation 3 (rejection sampling on a presampled tape)

Ported from clutch/theories/coneris/examples/random_counter3/impl3.v

## Rocq → Lean mapping
* Section `filter`: `filter_f` (Rocq: the decidable proposition `(n<4)%nat`) is the boolean
  `decide (n < 4)`; `filtered_list`, `Forall_filter_f` keep their names;
  `Forall (λ x, x ≤ 3) ns` is `∀ x ∈ ns, x ≤ 3`; `filter filter_f l` is `l.filter filter_f`.
* Section `impl3`: the context `H:conerisGS Σ, r1:@rand_spec Σ H, L:randG Σ,
  !inG Σ (frac_authR natR)` is `[conerisGS GF] [r1 : rand_spec GF]
  [HE : ElemG GF frac_auth_natF]`, with `(L : r1.randG GF)` an explicit argument (as in
  `Coneris.Lib.HocapRand`) of the statements that use it (`counter_tapes_presample3`,
  `incr_counter_spec3`).
* `new_counter3`, `incr_counter3`, `read_counter3`: transcribed with the `cpl` notation; the
  Rocq binder `"α "` (with a trailing space, distinct from `"α"`) of the inner `rec` is kept
  literally as the string binder `"α "`; `#4%nat` is `#4`; `rand_allocate_tape`,
  `rand_tape` are `r1.rand_allocate_tape`, `r1.rand_tape`.
* `counterG3` (Rocq `Class`, instance field `counterG3_frac_authR ::`) is a Lean class with the
  same fields.
* `counter_inv_pred3`, `is_counter3`, `new_counter_spec3`, `counter_tapes_presample3`,
  `incr_counter_spec3`, `read_counter_spec3`: same names. Errors are `ℝ≥0∞`: the hypotheses
  `∀ x, 0 <= ε2 x` are dropped.
  - `ec_ind_amp _ 5` is `ErrorCredit.Induction.amplifying` with `k := 5 : ℝ≥0`;
    `state_update_epsilon_err` as in Rocq (`ec_valid`, only used by Rocq to derive `ε < 1` for
    `lra`, is not needed in `ℝ≥0∞`).
  - The presampling function `λ x, match decide (fin_to_nat x < 4) with left p => ε2
    (nat_to_fin p) | _ => ε + 5*eps end` is `fun x => if h : (x : ℕ) < 4 then ε2 ⟨x, h⟩ else
    ε + 5 * eps`; the Rocq `SeriesC_finite_foldr ... lra` side condition is the helper
    `presample3_sum`. The combined credit `↯ (eps + ε)` is Rocq's `iCombine "Heps Herr"`.
  - `iLöb as "IH" forall (ls Hfilter Φ) "Hfrag"` is `iloeb as IH generalizing %ls %Hfilter
    Hfrag` (`Φ` does not change in the recursive call).
* `random_counter3` (a `Program Definition`) is a definition; its `Next Obligation`s are the
  theorems `random_counter3_counter_content_*` (proved by the shared `frac_auth_nat_*`
  helpers of `RandomCounter`).

## Added
* `counter_auth3`, `counter_frag3` (the `own` assertions), `presample3_sum`,
  `is_counter3_persistent`.

## Omitted
* The commented-out Rocq code (`rand_inv_create_spec`, `fupd_mask_subseteq` steps).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE CMRA Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.HocapRand Coneris.Examples.RandomCounter3.RandomCounter

namespace Coneris.Examples.RandomCounter3.Impl3

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
  simp only [Fin.val_castSucc, Fin.is_lt, dite_true, Fin.val_last, lt_irrefl, dite_false, Fin.eta]
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
def new_counter3 : val := cpl_val(λ "_", ref(#0))

/-- Rocq: `incr_counter3`. -/
def incr_counter3 : val := cpl_val(
  λ "l",
    let "α" := (v(&r1.rand_allocate_tape) #4) in
    (rec "f" "α " :=
        let "n" := v(&r1.rand_tape) "α" #4 in
        if "n" < #4
        then (faa("l", "n"), "n")
        else "f" "α") "α")

/-- Rocq: `read_counter3`. -/
def read_counter3 : val := cpl_val(λ "l", !"l")

/-- Rocq: `counterG3`. -/
class counterG3 (GF' : BundledGFunctors) : Type where
  counterG3_randG : r1.randG GF'
  counterG3_frac_authR : ElemG GF' frac_auth_natF

variable [HE : ElemG GF frac_auth_natF]

/-- `own γ (●F z)`. -/
abbrev counter_auth3 (γ : GName) (z : ℕ) : IProp GF := iOwn (F := frac_auth_natF) γ (●F z)

/-- `own γ (◯F{f} z)`. -/
abbrev counter_frag3 (γ : GName) (f : Qp) (z : ℕ) : IProp GF :=
  iOwn (F := frac_auth_natF) γ (◯F{f} z)

/-- Rocq: `counter_inv_pred3`. -/
def counter_inv_pred3 (c : val) (γ2 : GName) : IProp GF :=
  iprop(∃ (l : Loc) (z : ℕ), ⌜c = LitV (LitLoc l)⌝ ∗ l ↦ LitV (LitInt (z : ℤ)) ∗
    counter_auth3 γ2 z)

/-- Rocq: `is_counter3`. -/
def is_counter3 (N : Namespace) (c : val) (γ1 : GName) : IProp GF :=
  inv N (counter_inv_pred3 c γ1)

instance is_counter3_persistent (N : Namespace) (c : val) (γ1 : GName) :
    Persistent (is_counter3 (GF := GF) N c γ1) := by
  unfold is_counter3; infer_instance

/-- Rocq: `new_counter_spec3`. -/
theorem new_counter_spec3 (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter3) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter3 (GF := GF) N c γ1 ∗ counter_frag3 γ1 1 0 }} := by
  iintro %Φ - HΦ
  unfold new_counter3
  wp_pures
  wp_alloc l as Hl
  imod iOwn_alloc (F := frac_auth_natF) (CMRA.op (●F (0 : ℕ)) (◯F (0 : ℕ))) with ⟨%γ1, H5, H6⟩
  · exact FracAuth.valid trivial
  imod inv_alloc N E (counter_inv_pred3 (LitV (LitLoc l)) γ1) $$ [Hl H5] with #Hinv'
  · inext
    unfold counter_inv_pred3
    iexists l, 0
    iframe
    ipureintro
    rfl
  imodintro
  iapply HΦ
  iexists γ1
  unfold is_counter3
  iframe
  iexact Hinv'

/-- Rocq: `counter_tapes_presample3`. -/
theorem counter_tapes_presample3 (L : r1.randG GF) (N : Namespace) (E : CoPset) (γ1 : GName)
    (c α : val) (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) (Hineq : ∑' n, 1 / 4 * ε2 n ≤ ε) :
    ⊢ is_counter3 N c γ1 -∗
      (∃ ls : List ℕ, ⌜ls.filter filter_f = []⌝ ∗ r1.rand_tapes L α (4, ls)) -∗
      ↯ ε -∗
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

/-- Rocq: `incr_counter_spec3`. -/
theorem incr_counter_spec3 (L : r1.randG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : GName) (Q : ℝ≥0∞ → (Fin 4 → ℝ≥0∞) → ℕ → ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter3 N c γ1 ∗
        |={E \ ↑N, ∅}=>
          (∃ (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞),
            ↯ ε ∗ ⌜∑' n, 1 / 4 * ε2 n ≤ ε⌝ ∗
            (∀ n : Fin 4, ↯ (ε2 n) ={∅, E \ ↑N}=∗
              (∀ z : ℕ, counter_auth3 γ1 z ={E \ ↑N}=∗
                counter_auth3 γ1 (z + n) ∗ Q ε ε2 z n))) }}
      cpl(v(&incr_counter3) v(&c)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); ∃ ε ε2, Q ε ε2 z n }} := by
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold incr_counter3
  wp_pures
  wp_apply r1.rand_allocate_tape_spec L E 4 $$ [] with %α Htape
  · itrivial
  wp_pures
  ihave H : iprop(state_update (E \ ↑N) (E \ ↑N) iprop(∃ n : Fin 4,
      (∃ ls : List ℕ, ⌜ls.filter filter_f = [(n : ℕ)]⌝ ∗ r1.rand_tapes L α (4, ls)) ∗
      ∃ ε ε2, (∀ z : ℕ, counter_auth3 γ1 z ={E \ ↑N}=∗
        counter_auth3 γ1 (z + n) ∗ Q ε ε2 z n))) $$ [Hvs Htape]
  · imod Hvs with ⟨%ε, %ε2, Herr, %Hsum, Hvs⟩
    imod counter_tapes_presample3 L N ∅ γ1 c α ε ε2 Hsum $$ Hinv [Htape] Herr
      with ⟨%n, Herr, Htape⟩
    · iexists []
      iframe Htape
      ipureintro
      rfl
    imod Hvs $$ Herr with Hvs
    imodintro
    iexists n
    iframe Htape
    iexists ε, ε2
    iexact Hvs
  have Hsub : E \ ↑N ⊆ E := LawfulSet.diff_subset_left
  imod H with ⟨%n, ⟨%ls, %Hfilter, Hfrag⟩, %ε, %ε2, Hvs⟩
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
      iexists l, z + n
      push_cast
      iframe H5 H6
      ipureintro
      rfl
    imodintro
    wp_pures
    iapply HΦ
    iexists ε, ε2
    iexact HQ
  · simp only [K, decide_false]
    wp_pure
    wp_pure
    iapply IH $$ %ls %_ Hfrag HΦ Hvs
    have : filter_f hd = false := by simp [filter_f, K]
    rw [List.filter_cons_of_neg (by simp [this])] at Hfilter
    exact Hfilter

/-- Rocq: `read_counter_spec3`. -/
theorem read_counter_spec3 (N : Namespace) (E : CoPset) (c : val) (γ1 : GName)
    (Q : ℕ → IProp GF) (Hsubset : ↑N ⊆ E) :
    {{ is_counter3 N c γ1 ∗
        (∀ z : ℕ, counter_auth3 γ1 z ={E \ ↑N}=∗ counter_auth3 γ1 z ∗ Q z) }}
      cpl(v(&read_counter3) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }} := by
  unfold is_counter3 counter_inv_pred3
  iintro %Φ ⟨#Hinv, Hvs⟩ HΦ
  unfold read_counter3
  wp_pure
  iinv Hinv with ⟨%l, %z, >%Hc, >H5, >H6⟩ Hclose
  subst Hc
  wp_load
  imod Hvs $$ H6 with ⟨H6, HQ⟩
  imod Hclose $$ [H5 H6]
  · inext
    iexists l, z
    iframe
    ipureintro
    trivial
  imodintro
  iapply HΦ $$ HQ

end impl3

/-! ## `random_counter3` -/

section random_counter3

variable {GF : BundledGFunctors} [conerisGS GF] [F : rand_spec GF]

/-- Rocq: first `Next Obligation` of `random_counter3`. -/
theorem random_counter3_counter_content_auth_exclusive (L : counterG3 GF) (γ : GName)
    (z1 z2 : ℕ) :
    ⊢ counter_auth3 (HE := L.counterG3_frac_authR) γ z1 -∗
      counter_auth3 (HE := L.counterG3_frac_authR) γ z2 -∗ False :=
  @frac_auth_nat_auth_exclusive GF L.counterG3_frac_authR γ z1 z2

/-- Rocq: second `Next Obligation` of `random_counter3`. -/
theorem random_counter3_counter_content_less_than (L : counterG3 GF) (γ : GName) (z z' : ℕ)
    (f : Qp) :
    ⊢ counter_auth3 (HE := L.counterG3_frac_authR) γ z -∗
      counter_frag3 (HE := L.counterG3_frac_authR) γ f z' -∗ ⌜z' ≤ z⌝ :=
  @frac_auth_nat_less_than GF L.counterG3_frac_authR γ z z' f

/-- Rocq: third `Next Obligation` of `random_counter3`. -/
theorem random_counter3_counter_content_frag_combine (L : counterG3 GF) (γ : GName)
    (f f' : Qp) (z z' : ℕ) :
    iprop(counter_frag3 (HE := L.counterG3_frac_authR) γ f z ∗
      counter_frag3 (HE := L.counterG3_frac_authR) γ f' z') ⊣⊢
      counter_frag3 (HE := L.counterG3_frac_authR) γ (f + f') (z + z') :=
  @frac_auth_nat_frag_combine GF L.counterG3_frac_authR γ f f' z z'

/-- Rocq: fourth `Next Obligation` of `random_counter3`. -/
theorem random_counter3_counter_content_agree (L : counterG3 GF) (γ : GName) (z z' : ℕ) :
    ⊢ counter_auth3 (HE := L.counterG3_frac_authR) γ z -∗
      counter_frag3 (HE := L.counterG3_frac_authR) γ 1 z' -∗ ⌜z' = z⌝ :=
  @frac_auth_nat_agree GF L.counterG3_frac_authR γ z z'

/-- Rocq: fifth `Next Obligation` of `random_counter3`. -/
theorem random_counter3_counter_content_update (L : counterG3 GF) (γ : GName) (f : Qp)
    (z1 z2 z3 : ℕ) :
    ⊢ counter_auth3 (HE := L.counterG3_frac_authR) γ z1 -∗
      counter_frag3 (HE := L.counterG3_frac_authR) γ f z2 ==∗
      counter_auth3 (HE := L.counterG3_frac_authR) γ (z1 + z3) ∗
      counter_frag3 (HE := L.counterG3_frac_authR) γ f (z2 + z3) :=
  @frac_auth_nat_update GF L.counterG3_frac_authR γ f z1 z2 z3

/-- Rocq: `random_counter3` (a `Program Definition`). -/
@[instance_reducible]
def random_counter3 : random_counter GF where
  new_counter := new_counter3
  incr_counter := incr_counter3
  read_counter := read_counter3
  counterG := counterG3
  counter_name := GName
  is_counter L N c γ1 := is_counter3 (HE := L.counterG3_frac_authR) N c γ1
  counter_content_auth L γ z := counter_auth3 (HE := L.counterG3_frac_authR) γ z
  counter_content_frag L γ f z := counter_frag3 (HE := L.counterG3_frac_authR) γ f z
  is_counter_persistent L N c γ1 := is_counter3_persistent (HE := L.counterG3_frac_authR) N c γ1
  counter_content_auth_timeless L _ _ := by let := L.counterG3_frac_authR; exact iOwn_timeless
  counter_content_frag_timeless L _ _ _ := by
    let := L.counterG3_frac_authR; exact iOwn_timeless
  counter_content_auth_exclusive := random_counter3_counter_content_auth_exclusive
  counter_content_less_than := random_counter3_counter_content_less_than
  counter_content_frag_combine := random_counter3_counter_content_frag_combine
  counter_content_agree := random_counter3_counter_content_agree
  counter_content_update := random_counter3_counter_content_update
  new_counter_spec L := new_counter_spec3 (HE := L.counterG3_frac_authR)
  incr_counter_spec L :=
    incr_counter_spec3 (HE := L.counterG3_frac_authR) L.counterG3_randG
  read_counter_spec L := read_counter_spec3 (HE := L.counterG3_frac_authR)

end random_counter3

end Coneris.Examples.RandomCounter3.Impl3
