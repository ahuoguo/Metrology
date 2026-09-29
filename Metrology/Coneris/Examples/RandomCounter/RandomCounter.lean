module

public import Metrology.Coneris.ErrorRules

/-!
# An interface for a random counter

Ported from clutch/theories/coneris/examples/random_counter/random_counter.v

## Rocq → Lean mapping
* `Class random_counter `{!conerisGS Σ} := RandCounter {...}` is the Lean
  `class random_counter GF` (over `[conerisGS GF]`) with the same field names:
  `new_counter`, `allocate_tape`, `incr_counter_tape`, `read_counter`, `counterG`,
  `counter_name`, `is_counter`, `counter_tapes`, `counter_content_auth`, `counter_content_frag`,
  `is_counter_persistent`, `counter_tapes_timeless`, `counter_content_auth_timeless`,
  `counter_content_frag_timeless`, `counter_tapes_exclusive`, `counter_tapes_valid`,
  `counter_tapes_presample`, `counter_content_auth_exclusive`, `counter_content_less_than`,
  `counter_content_frag_combine`, `counter_content_agree`, `counter_content_update`,
  `new_counter_spec`, `allocate_tape_spec`, `incr_counter_tape_spec_some`, `read_counter_spec`.
  - As in `Coneris.Lib.HocapRand`, the implicit `{L : counterG Σ}` is an explicit argument
    `(L : counterG GF)`.
  - The `#[global] ... ::` instance fields are fields, re-exported as the global instances
    `random_counter_is_counter_persistent`, `random_counter_counter_tapes_timeless`,
    `random_counter_counter_content_auth_timeless`,
    `random_counter_counter_content_frag_timeless`.
  - `frac` is iris-lean's `Qp`; `(f + f')%Qp` is `f + f'`; `1%Qp` is `1`.
  - The `≡` of `counter_content_frag_combine` is `⊣⊢`.
  - Errors are `ℝ≥0∞`: the hypothesis `∀ x, 0 <= ε2 x` of `counter_tapes_presample` is
    dropped; `SeriesC (λ n, 1 / 4 * ε2 n) <= ε` is `∑' n, 1 / 4 * ε2 n ≤ ε`; `fin 4` is `Fin 4`
    and `fin_to_nat n` is `(n : ℕ)`.
  - `Forall (λ n, n<=3) ns` is `∀ n ∈ ns, n ≤ 3`.
  - `P -∗ Q -∗ R` / `P ==∗ Q` fields are stated as `⊢ P -∗ Q -∗ R` / `⊢ P -∗ Q ==∗ R`.
  - Texan triples `{{{ P }}} e @ E {{{ x, RET v; Q }}}` are iris-lean's
    `{{ P }} e @ E {{ x, RET v; Q }}`; the side condition `↑N ⊆ E` is a hypothesis before the
    triple; `RET (#z, #n)` is `RET cpl_val((#z, #n))`.
* Section `lemmas`: `incr_counter_tape_spec_none`, `incr_counter_tape_spec_none'` (same names),
  for `[rc : random_counter GF]` and `(L : rc.counterG GF)`.
  - In `incr_counter_tape_spec_none`, `Q` has type `ℕ → ℕ → ℝ≥0∞ → (ℕ → ℝ≥0∞) → IProp GF`; the
    hypothesis `⌜∀ n, 0 <= ε2 n⌝` of the premise is dropped (`ℝ≥0∞` errors are nonnegative).
  - In `incr_counter_tape_spec_none'`, the hypothesis `∀ n, 0 <= ε2 n` is dropped. The
    argument `ns`, unused in Rocq too, is kept.
  - The Rocq mask juggling (`fupd_mask_frame`, `difference_difference_r_L`, ...) is done with
    the helpers `fupd_mask_frame_diff_l`, `fupd_mask_frame_diff_r` below.

## Added
* `fupd_mask_frame_diff_l`, `fupd_mask_frame_diff_r` (mask-framing helpers),
  `sum_fin4_le` (the `SeriesC_finite_foldr ... lra` step).
* The `frac_authR natR` ghost state shared by `Impl1`/`Impl2`/`Impl3` (not in this Rocq file;
  each Rocq implementation repeats the same obligations): the functor `frac_authF_nat`,
  `own_auth_nat`, `own_frag_nat` (+ `Timeless` instances), and the lemmas
  `frac_auth_nat_alloc`, `frac_auth_nat_auth_exclusive`, `frac_auth_nat_less_than`,
  `frac_auth_nat_frag_combine`, `frac_auth_nat_agree`, `frac_auth_nat_update` (the five
  `frac_auth` `Next Obligation`s of the implementations).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.dupNamespace false
set_option linter.iris.dupNamespace false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Examples.RandomCounter.RandomCounter

/-- Rocq: `random_counter`. -/
class random_counter (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  new_counter : val
  allocate_tape : val
  incr_counter_tape : val
  read_counter : val
  -- * Ghost state
  /-- The assumptions about `Σ`. -/
  counterG : BundledGFunctors → Type
  /-- `name` is used to associate `locked` with `is_lock`. -/
  counter_name : Type
  -- * Predicates
  is_counter (L : counterG GF) (N : Namespace) (counter : val) (γ : counter_name) : IProp GF
  counter_tapes (L : counterG GF) (α : val) (ns : List ℕ) : IProp GF
  counter_content_auth (L : counterG GF) (γ : counter_name) (z : ℕ) : IProp GF
  counter_content_frag (L : counterG GF) (γ : counter_name) (f : Qp) (z : ℕ) : IProp GF
  -- * General properties of the predicates
  is_counter_persistent (L : counterG GF) (N : Namespace) (c : val) (γ1 : counter_name) :
    Persistent (is_counter L N c γ1)
  counter_tapes_timeless (L : counterG GF) (α : val) (ns : List ℕ) :
    Timeless (counter_tapes L α ns)
  counter_content_auth_timeless (L : counterG GF) (γ : counter_name) (z : ℕ) :
    Timeless (counter_content_auth L γ z)
  counter_content_frag_timeless (L : counterG GF) (γ : counter_name) (f : Qp) (z : ℕ) :
    Timeless (counter_content_frag L γ f z)
  counter_tapes_exclusive (L : counterG GF) (α : val) (ns ns' : List ℕ) :
    ⊢ counter_tapes L α ns -∗ counter_tapes L α ns' -∗ False
  counter_tapes_valid (L : counterG GF) (α : val) (ns : List ℕ) :
    ⊢ counter_tapes L α ns -∗ ⌜∀ n ∈ ns, n ≤ 3⌝
  counter_tapes_presample (L : counterG GF) (N : Namespace) (E : CoPset) (γ : counter_name)
    (c α : val) (ns : List ℕ) (ε : ℝ≥0∞) (ε2 : Fin 4 → ℝ≥0∞) :
    ↑N ⊆ E →
    ∑' n, 1 / 4 * ε2 n ≤ ε →
    ⊢ is_counter L N c γ -∗ counter_tapes L α ns -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin 4, ↯ (ε2 n) ∗ counter_tapes L α (ns ++ [(n : ℕ)]))
  counter_content_auth_exclusive (L : counterG GF) (γ : counter_name) (z1 z2 : ℕ) :
    ⊢ counter_content_auth L γ z1 -∗ counter_content_auth L γ z2 -∗ False
  counter_content_less_than (L : counterG GF) (γ : counter_name) (z z' : ℕ) (f : Qp) :
    ⊢ counter_content_auth L γ z -∗ counter_content_frag L γ f z' -∗ ⌜z' ≤ z⌝
  counter_content_frag_combine (L : counterG GF) (γ : counter_name) (f f' : Qp) (z z' : ℕ) :
    iprop(counter_content_frag L γ f z ∗ counter_content_frag L γ f' z') ⊣⊢
      counter_content_frag L γ (f + f') (z + z')
  counter_content_agree (L : counterG GF) (γ : counter_name) (z z' : ℕ) :
    ⊢ counter_content_auth L γ z -∗ counter_content_frag L γ 1 z' -∗ ⌜z' = z⌝
  counter_content_update (L : counterG GF) (γ : counter_name) (f : Qp) (z1 z2 z3 : ℕ) :
    ⊢ counter_content_auth L γ z1 -∗ counter_content_frag L γ f z2 ==∗
      counter_content_auth L γ (z1 + z3) ∗ counter_content_frag L γ f (z2 + z3)
  -- * Program specs
  new_counter_spec (L : counterG GF) (E : CoPset) (N : Namespace) :
    {{ True }} cpl(v(&new_counter) #()) @ E
    {{ c, RET c; ∃ γ1, is_counter L N c γ1 ∗ counter_content_frag L γ1 1 0 }}
  allocate_tape_spec (L : counterG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : counter_name) :
    ↑N ⊆ E →
    {{ is_counter L N c γ1 }} cpl(v(&allocate_tape) #()) @ E
    {{ v, RET v; counter_tapes L v [] }}
  incr_counter_tape_spec_some (L : counterG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : counter_name) (Q : ℕ → IProp GF) (α : val) (n : ℕ) (ns : List ℕ) :
    ↑N ⊆ E →
    {{ is_counter L N c γ1 ∗ counter_tapes L α (n :: ns) ∗
        (∀ z : ℕ, counter_content_auth L γ1 z ={E \ ↑N}=∗
          counter_content_auth L γ1 (z + n) ∗ Q z) }}
      cpl(v(&incr_counter_tape) v(&c) v(&α)) @ E
    {{ (z : ℕ), RET cpl_val((#z, #n)); counter_tapes L α ns ∗ Q z }}
  read_counter_spec (L : counterG GF) (N : Namespace) (E : CoPset) (c : val)
    (γ1 : counter_name) (Q : ℕ → IProp GF) :
    ↑N ⊆ E →
    {{ is_counter L N c γ1 ∗
        (∀ z : ℕ, counter_content_auth L γ1 z ={E \ ↑N}=∗ counter_content_auth L γ1 z ∗ Q z) }}
      cpl(v(&read_counter) v(&c)) @ E
    {{ (n' : ℕ), RET LitV (LitInt (n' : ℤ)); Q n' }}

section instances

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF]

/-- Rocq: `#[global] is_counter_persistent` (the instance). -/
instance random_counter_is_counter_persistent (L : rc.counterG GF) (N : Namespace) (c : val)
    (γ1 : rc.counter_name) : Persistent (rc.is_counter L N c γ1) :=
  rc.is_counter_persistent L N c γ1

/-- Rocq: `#[global] counter_tapes_timeless` (the instance). -/
instance random_counter_counter_tapes_timeless (L : rc.counterG GF) (α : val) (ns : List ℕ) :
    Timeless (rc.counter_tapes L α ns) :=
  rc.counter_tapes_timeless L α ns

/-- Rocq: `#[global] counter_content_auth_timeless` (the instance). -/
instance random_counter_counter_content_auth_timeless (L : rc.counterG GF)
    (γ : rc.counter_name) (z : ℕ) : Timeless (rc.counter_content_auth L γ z) :=
  rc.counter_content_auth_timeless L γ z

/-- Rocq: `#[global] counter_content_frag_timeless` (the instance). -/
instance random_counter_counter_content_frag_timeless (L : rc.counterG GF)
    (γ : rc.counter_name) (f : Qp) (z : ℕ) : Timeless (rc.counter_content_frag L γ f z) :=
  rc.counter_content_frag_timeless L γ f z

end instances

/-! ## Helpers -/

section helpers

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Helper (Rocq: `fupd_mask_frame` + `difference_difference_r_L`): frame `↑N` around an
update `E ∖ ↑N ⇝ ∅`. -/
theorem fupd_mask_frame_diff_l {E : CoPset} {N : Namespace} (h : ↑N ⊆ E) (P : IProp GF) :
    (|={E \ ↑N, ∅}=> P) ⊢ |={E, ↑N}=> P := by
  have H := fupd_mask_frame_right (PROP := IProp GF) (P := P) (E1 := E \ ↑N) (E2 := ∅)
    (Ef := ↑N) (LawfulSet.disjoint_symm LawfulSet.disjoint_diff_right)
  rwa [← LawfulSet.diff_subset_decomp h, LawfulSet.union_empty_left] at H

/-- Helper (Rocq: `fupd_mask_frame` + `union_difference_L`): frame `↑N` around an
update `∅ ⇝ E ∖ ↑N`. -/
theorem fupd_mask_frame_diff_r {E : CoPset} {N : Namespace} (h : ↑N ⊆ E) (P : IProp GF) :
    (|={∅, E \ ↑N}=> P) ⊢ |={↑N, E}=> P := by
  have H := fupd_mask_frame_right (PROP := IProp GF) (P := P) (E1 := ∅) (E2 := E \ ↑N)
    (Ef := ↑N) LawfulSet.disjoint_empty_left
  rwa [← LawfulSet.diff_subset_decomp h, LawfulSet.union_empty_left] at H

/-- Helper (Rocq: `rewrite SeriesC_finite_foldr/=. lra.`). -/
theorem sum_fin4_le (ε : ℝ≥0∞) (ε2 : ℕ → ℝ≥0∞)
    (Hineq : (ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4 ≤ ε) :
    ∑' n : Fin 4, 1 / 4 * ε2 (n : ℕ) ≤ ε := by
  rw [tsum_fintype, Fin.sum_univ_four]
  refine le_trans (le_of_eq ?_) Hineq
  rw [ENNReal.div_eq_inv_mul]
  simp only [mul_one, ← mul_add, ENNReal.div_eq_inv_mul]
  rfl

end helpers

/-! ## Helpers: the `frac_authR natR` ghost state of the implementations

The three implementations (`impl1`, `impl2`, `impl3`) all use `inG Σ (frac_authR natR)` and
prove the same five `Next Obligation`s about it; the proofs are shared here. -/

/-- Rocq: the functor of `inG Σ (frac_authR natR)`. `natR` is `(ℕ, +)` (iris-lean's
`CommMonoidLike` CMRA, found through the scoped `Iris.Credit` instances). -/
abbrev frac_authF_nat : COFE.OFunctorPre := constOF (FracAuth (A := ℕ))

section frac_auth_nat

variable {GF : BundledGFunctors} [ElemG GF frac_authF_nat]

/-- `own γ (●F z)`. -/
abbrev own_auth_nat (γ : GName) (z : ℕ) : IProp GF := iOwn (F := frac_authF_nat) γ (●F z)

/-- `own γ (◯F{f} z)`. -/
abbrev own_frag_nat (γ : GName) (f : Qp) (z : ℕ) : IProp GF :=
  iOwn (F := frac_authF_nat) γ (◯F{f} z)

/-- Helper: `own γ (●F z)` is timeless (stated explicitly, since instance search does not find
it under binders). -/
instance own_auth_nat_timeless (γ : GName) (z : ℕ) : Timeless (own_auth_nat (GF := GF) γ z) :=
  inferInstance

/-- Helper: `own γ (◯F{f} z)` is timeless. -/
instance own_frag_nat_timeless (γ : GName) (f : Qp) (z : ℕ) :
    Timeless (own_frag_nat (GF := GF) γ f z) :=
  inferInstance

/-- Rocq: `own_alloc (●F 0%nat ⋅ ◯F 0%nat)` (with `frac_auth_valid`). -/
theorem frac_auth_nat_alloc :
    ⊢@{IProp GF} |==> ∃ γ, own_auth_nat γ 0 ∗ own_frag_nat γ 1 0 := by
  imod iOwn_alloc (F := frac_authF_nat) ((●F (0 : ℕ)) • (◯F (0 : ℕ))) (FracAuth.valid trivial)
    with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Rocq: the `counter_content_auth_exclusive` obligation (`auth_auth_op_valid`). -/
theorem frac_auth_nat_auth_exclusive (γ : GName) (z1 z2 : ℕ) :
    ⊢@{IProp GF} own_auth_nat γ z1 -∗ own_auth_nat γ z2 -∗ False := by
  iintro H1 H2
  icombine H1 H2 gives %H
  exact (FracAuth.auth_op_valid H).elim

/-- Rocq: the `counter_content_less_than` obligation (`frac_auth_included_total`,
`nat_included`). -/
theorem frac_auth_nat_less_than (γ : GName) (z z' : ℕ) (f : Qp) :
    ⊢@{IProp GF} own_auth_nat γ z -∗ own_frag_nat γ f z' -∗ ⌜z' ≤ z⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  obtain ⟨w, hw⟩ := CommMonoidLike.included_iff.mp (FracAuth.included_total H)
  change z = z' + w at hw
  omega

/-- Rocq: the `counter_content_frag_combine` obligation (`frac_auth_frag_op`, `own_op`). -/
theorem frac_auth_nat_frag_combine (γ : GName) (f f' : Qp) (z z' : ℕ) :
    iprop(own_frag_nat γ f z ∗ own_frag_nat γ f' z') ⊣⊢@{IProp GF} own_frag_nat γ (f + f') (z + z') := by
  rw [← iOwn_op.to_eq]
  exact (congrArg (iOwn (F := frac_authF_nat) γ) FracAuth.frag_op).symm.to_bi

/-- Rocq: the `counter_content_agree` obligation (`frac_auth_agree_L`). -/
theorem frac_auth_nat_agree (γ : GName) (z z' : ℕ) :
    ⊢@{IProp GF} own_auth_nat γ z -∗ own_frag_nat γ 1 z' -∗ ⌜z' = z⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact (FracAuth.agree H).symm

/-- Rocq: the `counter_content_update` obligation (`frac_auth_update`, `nat_local_update`). -/
theorem frac_auth_nat_update (γ : GName) (f : Qp) (z1 z2 z3 : ℕ) :
    ⊢@{IProp GF} own_auth_nat γ z1 -∗ own_frag_nat γ f z2 ==∗
      own_auth_nat γ (z1 + z3) ∗ own_frag_nat γ f (z2 + z3) := by
  iintro H1 H2
  imod iOwn_update_op (F := frac_authF_nat)
    (a' := (●F (z1 + z3)) • (◯F{f} (z2 + z3))) $$ [H1 H2] with ⟨H1, H2⟩
  · exact FracAuth.update (CommMonoidLike.leftCancelAdd_local_update (by
      show z1 + (z2 + z3) = z1 + z3 + z2
      omega))
  · iframe
  imodintro
  iframe

end frac_auth_nat

/-! ## Lemmas -/

section lemmas

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF] (L : rc.counterG GF)

/-- Rocq: `incr_counter_tape_spec_none`. -/
theorem incr_counter_tape_spec_none (N : Namespace) (E : CoPset) (c : val)
    (γ1 : rc.counter_name) (Q : ℕ → ℕ → ℝ≥0∞ → (ℕ → ℝ≥0∞) → IProp GF) (α : val)
    (Hsubset : ↑N ⊆ E) :
    {{ rc.is_counter L N c γ1 ∗ rc.counter_tapes L α [] ∗
        (|={E \ ↑N, ∅}=>
          ∃ (ε : ℝ≥0∞) (ε2 : ℕ → ℝ≥0∞),
            ↯ ε ∗
            ⌜(ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4 ≤ ε⌝ ∗
            (∀ n : ℕ, ↯ (ε2 n) ={∅, E \ ↑N}=∗
              ∀ z : ℕ, rc.counter_content_auth L γ1 z ={E \ ↑N}=∗
                rc.counter_content_auth L γ1 (z + n) ∗ Q z n ε ε2)) }}
      cpl(v(&rc.incr_counter_tape) v(&c) v(&α)) @ E
    {{ (z n : ℕ), RET cpl_val((#z, #n)); rc.counter_tapes L α [] ∗
        ∃ ε ε2, Q z n ε ε2 }} := by
  iintro %Φ ⟨#Hinv, Hfrag, Hvs⟩ HΦ
  iapply state_update_wp E
    iprop(∃ (ε : ℝ≥0∞) (ε2 : ℕ → ℝ≥0∞) (n : ℕ), rc.counter_tapes L α [n] ∗
      ∀ z : ℕ, rc.counter_content_auth L γ1 z ={E \ ↑N}=∗
        rc.counter_content_auth L γ1 (z + n) ∗ Q z n ε ε2) $$ [Hvs Hfrag] [HΦ]
  · ihave Hvs := fupd_mask_frame_diff_l Hsubset _ $$ Hvs
    imod Hvs with ⟨%ε, %ε2, Herr, %Hineq, Hrest⟩
    imod rc.counter_tapes_presample L N ↑N γ1 c α [] ε (fun x => ε2 (x : ℕ))
      LawfulSet.subset_refl (sum_fin4_le ε ε2 Hineq) $$ Hinv Hfrag Herr with ⟨%n, Herr, Htape⟩
    ihave H := fupd_mask_frame_diff_r Hsubset _ $$ [Hrest Herr]
    · iapply Hrest $$ Herr
    imod H
    imodintro
    simp only [List.nil_append]
    iexists ε, ε2, (n : ℕ)
    iframe
  · iintro ⟨%ε, %ε2, %n, Htape, Hvs⟩
    wp_apply rc.incr_counter_tape_spec_some L N E c γ1 (fun z => Q z n ε ε2) α n [] Hsubset
      $$ [Htape Hvs] with %z ⟨Htape, HQ⟩
    · iframe
      iexact Hinv
    iapply HΦ
    iframe Htape
    iexists ε, ε2
    iexact HQ

/-- Rocq: `incr_counter_tape_spec_none'`. -/
theorem incr_counter_tape_spec_none' (N : Namespace) (E : CoPset) (c : val)
    (γ1 : rc.counter_name) (ε : ℝ≥0∞) (ε2 : ℕ → ℝ≥0∞) (α : val) (ns : List ℕ) (q : Qp) (z : ℕ)
    (Hsubset : ↑N ⊆ E) (Hineq : (ε2 0 + ε2 1 + ε2 2 + ε2 3) / 4 ≤ ε) :
    {{ rc.is_counter L N c γ1 ∗ ↯ ε ∗ rc.counter_tapes L α [] ∗
        rc.counter_content_frag L γ1 q z }}
      cpl(v(&rc.incr_counter_tape) v(&c) v(&α)) @ E
    {{ (z' n : ℕ), RET cpl_val((#z', #n)); ⌜0 ≤ n ∧ n < 4⌝ ∗ ⌜z ≤ z'⌝ ∗ ↯ (ε2 n) ∗
        rc.counter_tapes L α [] ∗ rc.counter_content_frag L γ1 q (z + n) }} := by
  iintro %Φ ⟨#Hinv, Herr, Htapes, Hcontent⟩ HΦ
  let ε2' : ℕ → ℝ≥0∞ := fun x => if x ≤ 3 then ε2 x else 1
  wp_apply incr_counter_tape_spec_none L N E c γ1
    (fun z' n ε' ε2'' => iprop(⌜0 ≤ n ∧ n < 4⌝ ∗ ⌜z ≤ z'⌝ ∗ ⌜ε = ε'⌝ ∗ ⌜ε2'' = ε2'⌝ ∗
      ↯ (ε2' n) ∗ rc.counter_content_frag L γ1 q (z + n))) α Hsubset
    $$ [Herr Htapes Hcontent] with %z' %n ⟨Htapes, %ε', %ε2'', %Hn, %Hz, %Hε, %Hε2, Herr, Hfrag⟩
  · iframe Htapes
    isplitr
    · iexact Hinv
    iapply fupd_mask_intro LawfulSet.empty_subset
    iintro Hclose
    iexists ε, ε2'
    iframe Herr
    isplitr
    · ipureintro
      simpa [ε2'] using Hineq
    iintro %n Herr
    imod Hclose
    imodintro
    iintro %z' Hauth
    by_cases H : n ≤ 3
    · ihave %Hle := rc.counter_content_less_than L γ1 z' z q $$ Hauth Hcontent
      imod rc.counter_content_update L γ1 q z' z n $$ Hauth Hcontent with ⟨Hauth, Hcontent⟩
      imodintro
      iframe Hauth Hcontent Herr
      ipureintro
      exact ⟨⟨Nat.zero_le _, by omega⟩, Hle, rfl, rfl⟩
    · have h1 : ε2' n = 1 := by simp [ε2', H]
      iexfalso
      iapply ErrorCredit.contradict (le_of_eq h1.symm) $$ Herr
  subst Hε Hε2
  iapply HΦ
  iframe Htapes Hfrag
  isplitr
  · ipureintro; exact Hn
  isplitr
  · ipureintro; exact Hz
  have h1 : ε2' n = ε2 n := by simp [ε2', show n ≤ 3 by omega]
  rw [h1]
  iexact Herr

end lemmas

end Coneris.Examples.RandomCounter.RandomCounter
