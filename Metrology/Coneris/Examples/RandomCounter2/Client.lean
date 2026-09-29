module

public import Metrology.Coneris.Examples.RandomCounter2.RandomCounter
public import Metrology.Coneris.Lib.Par
public import Iris.Algebra.Lib.ExclAuth
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A client of the random counter (version 2)

Ported from clutch/theories/coneris/examples/random_counter2/client.v

Two threads increment a shared random counter (`random_counter`, whose tapes can be
presampled) in parallel, each by a uniform sample of `{0,1,2,3}`; with `↯ (1/16)` the final
value of the counter is positive. The error credits are kept in an invariant and spent when a
thread presamples its counter tape (`counter_tapes_presample`) inside `incr_counter_spec`'s
view shift.

## Rocq → Lean mapping
* `T` (constructors `S0`, `S1`), `sampled`, `one_positive`, `TO`: same names. `one_positive`
  (Rocq: `bool_decide (∃ n, ...)`) is `decide` with an explicit `Classical.propDecidable` instance, only there (the `∃ n : nat` is
  not decidable by instance search in Lean); `TO := leibnizO T` is `DiscreteO T`.
* Section `lemmas`: `ghost_var_alloc`, `ghost_var_agree`, `ghost_var_update` (same names), for
  `[ElemG GF excl_authTF]` with `excl_authTF := constOF (ExclAuthR (A := TO))` (Rocq:
  `inG Σ (excl_authR TO)`); `own γ (●E b)` / `own γ (◯E b)` are the abbreviations
  `own_auth γ b` / `own_frag γ b`.
* Section `client`: the context `rc:random_counter`, `L: counterG Σ`, `!spawnG Σ`,
  `!inG Σ (excl_authR TO)` is `[rc : random_counter GF] (L : rc.counterG GF) [spawnG GF]
  [ElemG GF excl_authTF]`.
  - `con_prog`, `counter_nroot`, `inv_nroot`, `con_prog_inv`, `Rpower_4_2`, `con_prog_spec`:
    same names. `nroot.@"counter"` is `ndot nroot "counter"`.
  - `e1 ||| e2` (Rocq, `expr_scope`: `par (λ: <>, e1)%E (λ: <>, e2)%E`) is the scoped program
    notation `e1 ‖ e2` defined here (inside `cpl(..)` the token `|||` is the bitwise `or`),
    elaborating to `&par (λ <>, e1) (λ <>, e2)`.
  - `Rpower 4 x` is `(4 : ℝ≥0∞) ^ x` (`ENNReal.rpow`), `INR` is the cast `ℕ → ℝ`;
    `bool_to_nat (bool_decide P)` is `(decide P).toNat`; `(1/2)%Qp` is `Qp.half 1`.
  - Errors are `ℝ≥0∞`: the nonnegativity side conditions vanish; the Rocq `lra`/
    `SeriesC_finite_foldr` computations are the helpers `four_rpow_mean`,
    `four_rpow_zero_sub_two`, `four_rpow_two_sub_two`.
  - `{{{ ↯ (1/16) }}} con_prog {{{ (n:nat), RET #n; ⌜(0<n)%nat⌝ }}}` is the iris-lean Texan
    triple (mask `⊤`).
  - `0 <? fin_to_nat x` is `0 < (x : ℕ)`.

## Proofs that differ from Rocq
* `wp_par` is applied through the local helper `wp_par'` (the same statement with `par_V`
  unfolded, since `wp_apply` does not unfold `par_V`).
* `case_match` on `one_positive ..` is `cases` on the boolean, with the helper lemmas
  `one_positive_*` replacing the `bool_decide_eq_true_1`/`naive_solver` reasoning.
* `con_prog_spec` takes the counter ghost-state argument `L` explicitly (`include L`), since
  its statement does not mention it (Rocq: the section variable `L` is used by the proof).
* The mask side condition of `counter_tapes_presample` (Rocq:
  `namespaces.coPset_subseteq_difference_r`, `ndot_ne_disjoint`) is the helper
  `counter_nroot_subseteq`.
* The final `iAssert (|={⊤}=> ⌜(n1+n2>0)%nat⌝)` case-splits on `n1 = 0 ∧ n2 = 0` instead of
  `destruct n1, n2`.

## Added
* `excl_authTF`, `own_auth`, `own_frag`, `ite_timeless`, `wp_par'`, the `‖` notation,
  `positive_sampled`, `positive_sampled_S0`, `positive_sampled_S1`, `one_positive_iff`,
  `one_positive_S0_S0`, `one_positive_S1_l`, `one_positive_S1_r`, `one_positive_S1_zero_l`,
  `one_positive_S1_zero_r`, `one_positive_pos_l`, `one_positive_pos_r`, `four_rpow_mean`,
  `four_rpow_zero_sub_two`, `four_rpow_two_sub_two`, `counter_nroot_subseteq`,
  `half_add_half_one` (these helpers are the same as in
  `Coneris.Examples.RandomCounter3.Client`, duplicated here to keep the units independent).
  `deriving DecidableEq` and an `Inhabited` instance for `T` (`Inhabited` lets the proof mode
  commute `▷` with `∃ n1 n2`, as Rocq's `iInv` does).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Examples.RandomCounter2.RandomCounter
open Iris.ExclAuth

namespace Coneris.Examples.RandomCounter2.Client

/-- Rocq: `T`. -/
inductive T : Type where
  | S0 : T
  | S1 : (n : ℕ) → T
  deriving DecidableEq

instance : Inhabited T := ⟨T.S0⟩

open T

/-- Rocq: `sampled`. -/
def sampled : T → Option ℕ
  | S0 => none
  | S1 n => some n

/-- Rocq: `one_positive`. -/
def one_positive (n1 n2 : T) : Bool :=
  @decide (∃ n : ℕ, n > 0 ∧ (sampled n1 = some n ∨ sampled n2 = some n))
    (Classical.propDecidable _)

/-- Rocq: `TO` (`leibnizO T`). -/
abbrev TO : Type := DiscreteO T

/-! ### Facts about `one_positive` -/

/-- Helper: `s` has sampled a positive number. -/
def positive_sampled (s : T) : Prop := ∃ n : ℕ, n > 0 ∧ sampled s = some n

theorem one_positive_iff (s1 s2 : T) :
    one_positive s1 s2 = true ↔ positive_sampled s1 ∨ positive_sampled s2 := by
  simp only [one_positive, decide_eq_true_eq, positive_sampled]
  constructor
  · rintro ⟨n, hn, h | h⟩
    · exact Or.inl ⟨n, hn, h⟩
    · exact Or.inr ⟨n, hn, h⟩
  · rintro (⟨n, hn, h⟩ | ⟨n, hn, h⟩)
    · exact ⟨n, hn, Or.inl h⟩
    · exact ⟨n, hn, Or.inr h⟩

theorem positive_sampled_S0 : ¬ positive_sampled S0 := by
  simp [positive_sampled, sampled]

theorem positive_sampled_S1 (n : ℕ) : positive_sampled (S1 n) ↔ 0 < n := by
  simp [positive_sampled, sampled]

theorem one_positive_S0_S0 : one_positive S0 S0 = false := by
  cases h : one_positive S0 S0
  · rfl
  · rw [one_positive_iff] at h
    exact absurd h (by simp [positive_sampled_S0])

/-- Helper: sampling on the left keeps `one_positive` true. -/
theorem one_positive_S1_l (n : ℕ) (s : T) (h : one_positive S0 s = true) :
    one_positive (S1 n) s = true := by
  rw [one_positive_iff] at h ⊢
  rcases h with h | h
  · exact absurd h positive_sampled_S0
  · exact Or.inr h

/-- Helper: sampling on the right keeps `one_positive` true. -/
theorem one_positive_S1_r (n : ℕ) (s : T) (h : one_positive s S0 = true) :
    one_positive s (S1 n) = true := by
  rw [one_positive_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · exact absurd h positive_sampled_S0

/-- Helper: sampling `0` on the left keeps `one_positive` false. -/
theorem one_positive_S1_zero_l (s : T) (h : one_positive S0 s = false) :
    one_positive (S1 0) s = false := by
  cases h' : one_positive (S1 0) s
  · rfl
  · rw [one_positive_iff] at h'
    rcases h' with h' | h'
    · exact absurd ((positive_sampled_S1 0).1 h') (by omega)
    · have : one_positive S0 s = true := (one_positive_iff _ _).2 (Or.inr h')
      rw [h] at this
      exact absurd this (by simp)

/-- Helper: sampling `0` on the right keeps `one_positive` false. -/
theorem one_positive_S1_zero_r (s : T) (h : one_positive s S0 = false) :
    one_positive s (S1 0) = false := by
  cases h' : one_positive s (S1 0)
  · rfl
  · rw [one_positive_iff] at h'
    rcases h' with h' | h'
    · have : one_positive s S0 = true := (one_positive_iff _ _).2 (Or.inl h')
      rw [h] at this
      exact absurd this (by simp)
    · exact absurd ((positive_sampled_S1 0).1 h') (by omega)

/-- Helper: sampling a positive number makes `one_positive` true (left). -/
theorem one_positive_pos_l (n : ℕ) (hn : 0 < n) (s : T) : one_positive (S1 n) s = true :=
  (one_positive_iff _ _).2 (Or.inl ((positive_sampled_S1 n).2 hn))

/-- Helper: sampling a positive number makes `one_positive` true (right). -/
theorem one_positive_pos_r (n : ℕ) (hn : 0 < n) (s : T) : one_positive s (S1 n) = true :=
  (one_positive_iff _ _).2 (Or.inr ((positive_sampled_S1 n).2 hn))

/-! ## Ghost variables -/

/-- Rocq: the functor of `inG Σ (excl_authR TO)`. -/
abbrev excl_authTF : COFE.OFunctorPre := constOF (ExclAuthR (A := TO))

/-- `own γ (●E b)`. -/
abbrev own_auth {GF : BundledGFunctors} [ElemG GF excl_authTF] (γ : GName) (b : T) :
    IProp GF :=
  iOwn (F := excl_authTF) γ (●E (⟨b⟩ : TO))

/-- `own γ (◯E b)`. -/
abbrev own_frag {GF : BundledGFunctors} [ElemG GF excl_authTF] (γ : GName) (b : T) :
    IProp GF :=
  iOwn (F := excl_authTF) γ (◯E (⟨b⟩ : TO))

section lemmas

variable {GF : BundledGFunctors} [ElemG GF excl_authTF]

/-- Rocq: `ghost_var_alloc`. -/
theorem ghost_var_alloc (b : T) :
    ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b := by
  imod iOwn_alloc (F := excl_authTF) ((●E (⟨b⟩ : TO)) • (◯E (⟨b⟩ : TO)))
    ExclAuth.valid with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Rocq: `ghost_var_agree`. -/
theorem ghost_var_agree (γ : GName) (b c : T) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree H)

/-- Rocq: `ghost_var_update`. -/
theorem ghost_var_update (γ : GName) (b' b c : T) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' := by
  iintro H1 H2
  ihave H := (iOwn_op (F := excl_authTF)).2 $$ [H1 H2]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with ⟨H1, H2⟩
  imodintro
  iframe

end lemmas

/-! ## Parallel composition -/

/-- `e1 ||| e2` (Rocq: `par (λ: <>, e1)%E (λ: <>, e2)%E` in `expr_scope`) as a program
notation. -/
scoped syntax:55 cpl_exp:56 " ‖ " cpl_exp:55 : cpl_exp

macro_rules
  | `(cpl($e1 ‖ $e2)) => `(cpl(&par (λ <>, $e1) (λ <>, $e2)))

/-- Helper (not in Rocq): `wp_par` with `par_V` unfolded, so that `wp_apply` finds it. -/
theorem wp_par' {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
    (Ψ1 Ψ2 : val → IProp GF) (e1 e2 : expr) (Φ : val → IProp GF) :
    ⊢ WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
      (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (PairV v1 v2)) -∗
      WP cpl(&par v(λ <>, &e1) v(λ <>, &e2)) {{ Φ }} :=
  wp_par Ψ1 Ψ2 e1 e2 Φ

/-- Helper (Rocq infers it): an `if` of timeless propositions is timeless. -/
instance ite_timeless {GF : BundledGFunctors} (c : Prop) [Decidable c] (P Q : IProp GF)
    [Timeless P] [Timeless Q] : Timeless (if c then P else Q) := by
  split <;> infer_instance

/-! ## Error arithmetic -/

/-- Helper: the mean of the error function used in `con_prog_spec` (Rocq:
`rewrite SeriesC_finite_foldr/=. rewrite Rpower_plus Rpower_1; lra.`). -/
theorem four_rpow_mean (t : ℝ) :
    ∑' x : Fin 4, 1 / 4 *
      (if 0 < (x : ℕ) then (0 : ℝ≥0∞) else (4 : ℝ≥0∞) ^ (1 + t)) ≤ 4 ^ t := by
  rw [tsum_fintype, Fin.sum_univ_succ]
  simp only [Fin.val_zero, lt_irrefl, ↓reduceIte, Fin.val_succ, Nat.zero_lt_succ, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [ENNReal.rpow_add 1 t (by norm_num) (by norm_num), ENNReal.rpow_one, ← mul_assoc,
    one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- Helper: `Rpower 4 (INR 0 - 2) = 1 / 16`. -/
theorem four_rpow_zero_sub_two : (4 : ℝ≥0∞) ^ (((0 : ℕ) : ℝ) - 2) = 1 / 16 := by
  rw [Nat.cast_zero, zero_sub, ENNReal.rpow_neg, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast]
  norm_num

/-- Helper: `Rpower 4 (INR 2 - 2) = 1`. -/
theorem four_rpow_two_sub_two : (4 : ℝ≥0∞) ^ (((2 : ℕ) : ℝ) - 2) = 1 := by
  norm_num

/-- Helper: `(1/2 + 1/2)%Qp = 1`. -/
theorem half_add_half_one : Qp.half 1 + Qp.half 1 = 1 := Qp.half_add_half 1

/-! ## The client -/

/-- Rocq: `counter_nroot`. -/
def counter_nroot : Namespace := ndot nroot "counter"

/-- Rocq: `inv_nroot`. -/
def inv_nroot : Namespace := ndot nroot "inv"

/-- Helper (Rocq: `namespaces.coPset_subseteq_difference_r` and `ndot_ne_disjoint`): the counter
can be presampled inside the mask where the invariant is open. -/
theorem counter_nroot_subseteq : (↑counter_nroot : CoPset) ⊆ ⊤ \ ↑inv_nroot :=
  fun x hx => CoPset.in_diff.mpr ⟨CoPset.mem_full, fun hx0 =>
    ndot_ne_disjoint nroot (show ("counter" : String) ≠ "inv" by decide) x ⟨hx, hx0⟩⟩

/-- Rocq: `Rpower_4_2`. -/
theorem Rpower_4_2 : (4 : ℝ≥0∞) ^ (2 : ℝ) = 16 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  norm_num

section client

variable {GF : BundledGFunctors} [conerisGS GF] [rc : random_counter GF] (L : rc.counterG GF)

/-- Rocq: `con_prog`. -/
def con_prog : expr := cpl(
  let "c" := v(&rc.new_counter) #() in
  ((v(&rc.incr_counter) "c") ‖
   v(&rc.incr_counter) "c");
  v(&rc.read_counter) "c")

variable [spawnG GF] [ElemG GF excl_authTF]

/-- Rocq: `con_prog_inv`. -/
def con_prog_inv (γ1 γ2 : GName) : IProp GF :=
  iprop(∃ (n1 n2 : T),
    own_auth γ1 n1 ∗ own_auth γ2 n2 ∗
    if one_positive n1 n2
    then ↯ 0
    else
      ∃ flip_num : ℕ,
        ↯ ((4 : ℝ≥0∞) ^ ((flip_num : ℝ) - 2)) ∗
        ⌜flip_num = (decide (sampled n1 = some 0)).toNat +
          (decide (sampled n2 = some 0)).toNat⌝)

include L in
/-- Rocq: `con_prog_spec`. -/
theorem con_prog_spec :
    {{ ↯ (1 / 16) }} con_prog
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (⌜0 < n⌝ : IProp GF) }} := by
  iintro %Φ Hε HΦ
  unfold con_prog
  wp_apply rc.new_counter_spec L ⊤ counter_nroot $$ [] with %c ⟨%γ, #Hcounter, Hfrag⟩
  · itrivial
  rw [show rc.counter_content_frag L γ 1 0 =
      rc.counter_content_frag L γ (Qp.half 1 + Qp.half 1) (0 + 0) by rw [half_add_half_one]]
  ihave ⟨Hc1, Hc2⟩ := (rc.counter_content_frag_combine L γ _ _ 0 0).2 $$ Hfrag
  wp_pures
  imod ghost_var_alloc S0 with ⟨%γ1, Hauth1, Hfrag1⟩
  imod ghost_var_alloc S0 with ⟨%γ2, Hauth2, Hfrag2⟩
  imod inv_alloc inv_nroot ⊤ (con_prog_inv γ1 γ2) $$ [Hauth1 Hauth2 Hε] with #Hinv
  · inext
    unfold con_prog_inv
    iexists S0, S0
    iframe Hauth1 Hauth2
    rw [one_positive_S0_S0, ite_eq_right Bool.false_ne_true]
    iexists 0
    rw [four_rpow_zero_sub_two]
    iframe Hε
    ipureintro
    simp [sampled]
  have Hsub : (↑counter_nroot : CoPset) ⊆ ⊤ \ ↑inv_nroot := counter_nroot_subseteq
  have Hcsub : (↑counter_nroot : CoPset) ⊆ ⊤ := CoPset.subseteq_top
  have Hisub : (↑inv_nroot : CoPset) ⊆ ⊤ := CoPset.subseteq_top
  wp_apply wp_par'
    (fun _ => iprop(∃ n : ℕ, own_frag γ1 (S1 n) ∗ rc.counter_content_frag L γ (Qp.half 1) n))
    (fun _ => iprop(∃ n : ℕ, own_frag γ2 (S1 n) ∗ rc.counter_content_frag L γ (Qp.half 1) n))
    $$ [Hfrag1 Hc1] [Hfrag2 Hc2]
  · -- thread 1
    wp_apply rc.incr_counter_spec L counter_nroot ⊤ c γ
      (fun _ _ => iprop(∃ n : ℕ, own_frag γ1 (S1 n) ∗ rc.counter_content_frag L γ (Qp.half 1) n))
      Hcsub $$ [Hfrag1 Hc1] with %z %n H
    · isplitr
      · iexact Hcounter
      iintro %α Htape
      iapply state_update_inv_acc _ ⊤ (con_prog_inv γ1 γ2) inv_nroot Hisub $$ Hinv
      iintro HI
      unfold con_prog_inv
      icases HI with ⟨%n1, %n2, >Hauth1, >Hauth2, >Herr⟩
      ihave %Heq := ghost_var_agree $$ Hauth1 Hfrag1
      subst Heq
      cases H : one_positive S0 n2
      · -- no positive sample yet
        rw [ite_eq_right Bool.false_ne_true]
        icases Herr with ⟨%flip_num, Herr, %Hflip⟩
        simp only [show sampled S0 = none from rfl, reduceCtorEq, decide_false,
          Bool.toNat_false, zero_add] at Hflip
        subst Hflip
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c α _
          (fun x : Fin 4 => if 0 < (x : ℕ) then (0 : ℝ≥0∞)
            else (4 : ℝ≥0∞) ^ (1 + (((decide (sampled n2 = some 0)).toNat : ℝ) - 2)))
          Hsub (four_rpow_mean _) $$ Hcounter Htape Herr with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ1 (S1 (n : ℕ)) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        imodintro
        isplitl [Htape Hfrag1 Hc1]
        · iexists (n : ℕ)
          iframe Htape
          iintro %z Hauth
          imod rc.counter_content_update L γ _ z 0 n $$ Hauth Hc1 with ⟨Hauth, Hc1⟩
          rw [Nat.zero_add]
          imodintro
          iframe
        · inext
          iexists S1 (n : ℕ), n2
          iframe Hauth1 Hauth2
          by_cases H0 : 0 < (n : ℕ)
          · rw [one_positive_pos_l _ H0, ite_eq_left rfl]
            simp only [H0, ↓reduceIte]
            iexact Herr
          · have Hn0 : (n : ℕ) = 0 := by omega
            rw [Hn0, one_positive_S1_zero_l _ H, ite_eq_right Bool.false_ne_true]
            simp only [lt_irrefl, ↓reduceIte]
            iexists 1 + (decide (sampled n2 = some 0)).toNat
            isplitl
            · iapply ErrorCredit.ext _ $$ Herr
              push_cast
              ring_nf
            · ipureintro
              simp [sampled]
      · -- a positive sample already exists
        rw [ite_eq_left rfl]
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c α _
          (fun _ : Fin 4 => (0 : ℝ≥0∞)) Hsub (by simp) $$ Hcounter Htape Herr
          with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ1 (S1 (n : ℕ)) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        imodintro
        isplitl [Htape Hfrag1 Hc1]
        · iexists (n : ℕ)
          iframe Htape
          iintro %z Hauth
          imod rc.counter_content_update L γ _ z 0 n $$ Hauth Hc1 with ⟨Hauth, Hc1⟩
          rw [Nat.zero_add]
          imodintro
          iframe
        · inext
          iexists S1 (n : ℕ), n2
          rw [one_positive_S1_l _ _ H, ite_eq_left rfl]
          iframe
    iexact H
  · -- thread 2
    wp_apply rc.incr_counter_spec L counter_nroot ⊤ c γ
      (fun _ _ => iprop(∃ n : ℕ, own_frag γ2 (S1 n) ∗ rc.counter_content_frag L γ (Qp.half 1) n))
      Hcsub $$ [Hfrag2 Hc2] with %z %n H
    · isplitr
      · iexact Hcounter
      iintro %α Htape
      iapply state_update_inv_acc _ ⊤ (con_prog_inv γ1 γ2) inv_nroot Hisub $$ Hinv
      iintro HI
      unfold con_prog_inv
      icases HI with ⟨%n1, %n2, >Hauth1, >Hauth2, >Herr⟩
      ihave %Heq := ghost_var_agree $$ Hauth2 Hfrag2
      subst Heq
      cases H : one_positive n1 S0
      · -- no positive sample yet
        rw [ite_eq_right Bool.false_ne_true]
        icases Herr with ⟨%flip_num, Herr, %Hflip⟩
        simp only [show sampled S0 = none from rfl, reduceCtorEq, decide_false,
          Bool.toNat_false, add_zero] at Hflip
        subst Hflip
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c α _
          (fun x : Fin 4 => if 0 < (x : ℕ) then (0 : ℝ≥0∞)
            else (4 : ℝ≥0∞) ^ (1 + (((decide (sampled n1 = some 0)).toNat : ℝ) - 2)))
          Hsub (four_rpow_mean _) $$ Hcounter Htape Herr with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ2 (S1 (n : ℕ)) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        imodintro
        isplitl [Htape Hfrag2 Hc2]
        · iexists (n : ℕ)
          iframe Htape
          iintro %z Hauth
          imod rc.counter_content_update L γ _ z 0 n $$ Hauth Hc2 with ⟨Hauth, Hc2⟩
          rw [Nat.zero_add]
          imodintro
          iframe
        · inext
          iexists n1, S1 (n : ℕ)
          iframe Hauth1 Hauth2
          by_cases H0 : 0 < (n : ℕ)
          · rw [one_positive_pos_r _ H0, ite_eq_left rfl]
            simp only [H0, ↓reduceIte]
            iexact Herr
          · have Hn0 : (n : ℕ) = 0 := by omega
            rw [Hn0, one_positive_S1_zero_r _ H, ite_eq_right Bool.false_ne_true]
            simp only [lt_irrefl, ↓reduceIte]
            iexists (decide (sampled n1 = some 0)).toNat + 1
            isplitl
            · iapply ErrorCredit.ext _ $$ Herr
              push_cast
              ring_nf
            · ipureintro
              simp [sampled]
      · -- a positive sample already exists
        rw [ite_eq_left rfl]
        imod rc.counter_tapes_presample L counter_nroot (⊤ \ ↑inv_nroot) γ c α _
          (fun _ : Fin 4 => (0 : ℝ≥0∞)) Hsub (by simp) $$ Hcounter Htape Herr
          with ⟨%n, Herr, Htape⟩
        imod ghost_var_update γ2 (S1 (n : ℕ)) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        imodintro
        isplitl [Htape Hfrag2 Hc2]
        · iexists (n : ℕ)
          iframe Htape
          iintro %z Hauth
          imod rc.counter_content_update L γ _ z 0 n $$ Hauth Hc2 with ⟨Hauth, Hc2⟩
          rw [Nat.zero_add]
          imodintro
          iframe
        · inext
          iexists n1, S1 (n : ℕ)
          rw [one_positive_S1_r _ _ H, ite_eq_left rfl]
          iframe
    iexact H
  · iintro %v1 %v2 ⟨⟨%n1, Hfrag1, Hc1⟩, ⟨%n2, Hfrag2, Hc2⟩⟩
    inext
    wp_pures
    ihave Hc := (rc.counter_content_frag_combine L γ _ _ n1 n2).1 $$ [Hc1 Hc2]
    · iframe
    rw [half_add_half_one]
    ihave Hpos : iprop(|={⊤}=> ⌜n1 + n2 > 0⌝) $$ [Hfrag1 Hfrag2]
    · unfold con_prog_inv
      iinv Hinv with ⟨%m1, %m2, >Hauth1, >Hauth2, >Herr⟩ Hclose
      ihave %Heq1 := ghost_var_agree $$ Hauth1 Hfrag1
      ihave %Heq2 := ghost_var_agree $$ Hauth2 Hfrag2
      subst Heq1 Heq2
      by_cases hz : n1 = 0 ∧ n2 = 0
      · obtain ⟨rfl, rfl⟩ := hz
        rw [one_positive_S1_zero_l _ (one_positive_S1_zero_r _ one_positive_S0_S0),
          ite_eq_right Bool.false_ne_true]
        icases Herr with ⟨%flip_num, Herr, %Hflip⟩
        simp [sampled] at Hflip
        subst Hflip
        iexfalso
        iapply ErrorCredit.contradict (le_of_eq four_rpow_two_sub_two.symm) $$ Herr
      imod Hclose $$ [Hauth1 Hauth2 Herr]
      · inext
        iexists S1 n1, S1 n2
        iframe
      imodintro
      ipureintro
      omega
    imod Hpos with %Hpos
    wp_apply rc.read_counter_spec L counter_nroot ⊤ c γ (fun n => iprop(⌜n > 0⌝)) Hcsub
      $$ [Hc] with %n' %Hn'
    · isplitr
      · iexact Hcounter
      iintro %z Hauth
      ihave %Hz := rc.counter_content_agree L γ z (n1 + n2) $$ Hauth Hc
      imodintro
      iframe Hauth
      ipureintro
      omega
    iapply HΦ
    ipureintro
    omega

end client

end Coneris.Examples.RandomCounter2.Client
