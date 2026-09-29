module

public import Metrology.Coneris.Lib.Par
public import Metrology.Coneris.ErrorRules
public import Iris.Algebra.Lib.ExclAuth
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Two dice

Ported from clutch/theories/coneris/examples/two_die.v (first part: the ghost-variable lemmas,
`two_die_prog`, sections `simple` and `complex`). The Rocq file is split into
`Coneris.Examples.TwoDie` (this file), `TwoDiePart2` (`two_die_prog'`, section `simple'`),
`TwoDiePart3` (`T`, `sampled`, `one_positive`, `added_1`, section `lemmasT`,
`parallel_add_inv'`) and `TwoDiePart4` (`complex_parallel_add_spec'`), all in the namespace
`Coneris.Examples.TwoDie`.

Two threads each roll a six-sided die (`rand #5`); the program returns the sum
(`two_die_prog`) or counts the positive results with `FAA` (`two_die_prog'`). The result is
positive except with probability `1/36`; `↯ (1/6)` suffices with a simple proof that spends the
credit in the first thread only.

## Rocq → Lean map (all four files)
* All Rocq names are kept: `ghost_var_alloc`, `ghost_var_agree`, `ghost_var_update` (section
  `lemmas`, `excl_authR (option natO)`), `ghost_var_alloc'`, `ghost_var_agree'`,
  `ghost_var_update'` (section `lemmas'`, `excl_authR boolO`), `two_die_prog`,
  `simple_parallel_add_spec`, `parallel_add_inv`, `complex_parallel_add_spec`, `two_die_prog'`,
  `simple_parallel_add_inv'`, `simple_parallel_add_spec'`, `T` (constructors `S0`, `S1`, `S2`),
  `sampled`, `one_positive`, `added_1`, `TO`, `ghost_var_allocT`, `ghost_var_agreeT`,
  `ghost_var_updateT` (section `lemmasT`), `parallel_add_inv'`, `complex_parallel_add_spec'`.
* `inG Σ (excl_authR A)` (for `A = option natO, boolO, TO`) is `ElemG GF (excl_authF A)` with
  `excl_authF A := constOF (ExclAuthR (A := DiscreteO A))` (iris-lean's Leibniz OFE);
  `own γ (●E a)` / `own γ (◯E a)` are `own_auth γ a` / `own_frag γ a` (abbreviations for
  `iOwn γ (●E ⟨a⟩)` / `iOwn γ (◯E ⟨a⟩)`). The three copies of the ghost-variable lemmas are
  instances of the generic helpers `excl_auth_alloc`, `excl_auth_agree`, `excl_auth_update`.
* `e1 ||| e2` (Rocq, `expr_scope`) is the scoped program notation `e1 ‖ e2` (as in
  `Foxtrot.Lib.Par`; inside `cpl(..)` the token `|||` is the bitwise `or`), elaborating to
  `&par (λ <>, e1) (λ <>, e2)`; `let, ("v1", "v2") := e in e'` is `let (v1, v2) := e; e'`.
* Texan triples `{{{ P }}} e {{{ (n:nat), RET #n; Q }}}` are
  `{{ P }} e {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); Q }}`.
* Errors are `ℝ≥0∞`: `Rpower 6 (INR flip_num - 2)` is `(6 : ℝ≥0∞) ^ ((flip_num : ℝ) - 2)`
  (`ENNReal.rpow` with a real, possibly negative, exponent: no truncation); `↯ 0%R` is `↯ 0`.
  The nonnegativity side conditions of `wp_couple_rand_adv_comp1'` vanish. The error functions
  `λ x, if bool_decide (fin_to_nat x = 0) then .. else 0` are `fun x => if (x : ℕ) = 0 then .. else 0`.
* `bool_decide P` for the undecidable-by-instance propositions (`∃ x, n1 = Some x ∧ 0 < x`, the
  bodies of `one_positive` and `added_1`) uses classical decidability
  (`attribute [local instance] Classical.propDecidable`, Rocq: the derived `Decision` instances);
  `bool_to_nat (bool_decide (n = Some 0))` is `(decide (n = some 0)).toNat`. `one_positive` and
  `added_1` return `Bool`, as in Rocq.
* `T` has `deriving DecidableEq` and an `Inhabited` instance (the latter lets the proof mode
  commute `▷` with `∃ s1 s2`, as Rocq's `iInv .. as ">(..)"` does).

## Proofs that differ from Rocq
* `wp_par` is applied through the local helper `wp_par'` (`par_V` unfolded).
* The real arithmetic on `Rpower` (Rocq: `Rpower_plus`, `Rpower_1`, `exp_ln`, `ln_pow`, `lra`)
  is done in the helpers `six_rpow_add_one`, `six_rpow_mean`, `six_rpow_zero_sub_two`,
  `six_rpow_two_sub_two`.
* `case_bool_decide`/`destruct (one_positive _ _) eqn:` are `by_cases`/`cases h : ..`; the
  `bool_decide` rewrites are `ite_eq_left`/`ite_eq_right`/`simp only [..]` with the helper
  equations `added_1_S0`, `added_1_S1`, `added_1_S2`, `one_positive_eq`.
* In `complex_parallel_add_spec'`, the `FAA` step that Rocq writes out four times (twice per
  thread) is the helper lemma `complex_parallel_add_spec'_faa1` / `_faa2` (`TwoDiePart3`).
* `iAssert (⌜0<n⌝)%I as "%"` is `ihave %Hn : iprop(⌜0 < n⌝) $$ [..]`.

## Added
* `excl_authF`, `own_auth`, `own_frag`, `excl_auth_alloc`, `excl_auth_agree`,
  `excl_auth_update`, the `‖` notation, `wp_par'`, `six_rpow_*`, `ite_timeless` (Rocq infers
  timelessness of `if`), `added_1_S0`, `added_1_S1`, `added_1_S2`, `one_positive_eq`,
  `complex_parallel_add_spec'_faa1`, `complex_parallel_add_spec'_faa2`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par
open Iris.ExclAuth

namespace Coneris.Examples.TwoDie

/-! ## Exclusive-authoritative ghost variables -/

/-- Rocq: the functor of `inG Σ (excl_authR (leibnizO A))`. -/
abbrev excl_authF (A : Type) : COFE.OFunctorPre := constOF (ExclAuthR (A := DiscreteO A))

section excl_auth

variable {GF : BundledGFunctors} {A : Type} [ElemG GF (excl_authF A)]

/-- Helper: `ghost_var_alloc` for any `excl_authR (leibnizO A)`. -/
theorem excl_auth_alloc (b : A) :
    ⊢@{IProp GF} |==> ∃ γ, iOwn (F := excl_authF A) γ (●E (⟨b⟩ : DiscreteO A)) ∗
      iOwn (F := excl_authF A) γ (◯E (⟨b⟩ : DiscreteO A)) := by
  imod iOwn_alloc (F := excl_authF A) ((●E (⟨b⟩ : DiscreteO A)) • (◯E (⟨b⟩ : DiscreteO A)))
    ExclAuth.valid with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Helper: `ghost_var_agree` for any `excl_authR (leibnizO A)`. -/
theorem excl_auth_agree (γ : GName) (b c : A) :
    ⊢@{IProp GF} iOwn (F := excl_authF A) γ (●E (⟨b⟩ : DiscreteO A)) -∗
      iOwn (F := excl_authF A) γ (◯E (⟨c⟩ : DiscreteO A)) -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree H)

/-- Helper: `ghost_var_update` for any `excl_authR (leibnizO A)`. -/
theorem excl_auth_update (γ : GName) (b' b c : A) :
    ⊢@{IProp GF} iOwn (F := excl_authF A) γ (●E (⟨b⟩ : DiscreteO A)) -∗
      iOwn (F := excl_authF A) γ (◯E (⟨c⟩ : DiscreteO A)) ==∗
      iOwn (F := excl_authF A) γ (●E (⟨b'⟩ : DiscreteO A)) ∗
      iOwn (F := excl_authF A) γ (◯E (⟨b'⟩ : DiscreteO A)) := by
  iintro H1 H2
  ihave H := (iOwn_op (F := excl_authF A)).2 $$ [H1 H2]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with ⟨H1, H2⟩
  imodintro
  iframe

end excl_auth

/-- `own γ (●E a)` for `excl_authR (leibnizO A)`. -/
abbrev own_auth {GF : BundledGFunctors} {A : Type} [ElemG GF (excl_authF A)] (γ : GName)
    (a : A) : IProp GF :=
  iOwn (F := excl_authF A) γ (●E (⟨a⟩ : DiscreteO A))

/-- `own γ (◯E a)` for `excl_authR (leibnizO A)`. -/
abbrev own_frag {GF : BundledGFunctors} {A : Type} [ElemG GF (excl_authF A)] (γ : GName)
    (a : A) : IProp GF :=
  iOwn (F := excl_authF A) γ (◯E (⟨a⟩ : DiscreteO A))

section lemmas

variable {GF : BundledGFunctors} [ElemG GF (excl_authF (Option ℕ))]

/-- Rocq: `ghost_var_alloc`. -/
theorem ghost_var_alloc (b : Option ℕ) :
    ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b :=
  excl_auth_alloc b

/-- Rocq: `ghost_var_agree`. -/
theorem ghost_var_agree (γ : GName) (b c : Option ℕ) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ :=
  excl_auth_agree γ b c

/-- Rocq: `ghost_var_update`. -/
theorem ghost_var_update (γ : GName) (b' b c : Option ℕ) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' :=
  excl_auth_update γ b' b c

end lemmas

section lemmas'

variable {GF : BundledGFunctors} [ElemG GF (excl_authF Bool)]

/-- Rocq: `ghost_var_alloc'`. -/
theorem ghost_var_alloc' (b : Bool) :
    ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b :=
  excl_auth_alloc b

/-- Rocq: `ghost_var_agree'`. -/
theorem ghost_var_agree' (γ : GName) (b c : Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ :=
  excl_auth_agree γ b c

/-- Rocq: `ghost_var_update'`. -/
theorem ghost_var_update' (γ : GName) (b' b c : Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' :=
  excl_auth_update γ b' b c

end lemmas'

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

/-! ## The simple proof -/

/-- Rocq: `two_die_prog`. -/
def two_die_prog : expr := cpl(
  let (v1, v2) := ((rand(#5)) ‖ rand(#5)); v1 + v2)

section simple

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]

/-- Rocq: `simple_parallel_add_spec`. -/
theorem simple_parallel_add_spec :
    {{ ↯ (1 / 6) }} two_die_prog
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (⌜0 < n⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold two_die_prog
  wp_pures
  wp_apply wp_par' (fun x => iprop(∃ n : ℕ, ⌜x = LitV (LitInt (n : ℤ))⌝ ∗ ⌜0 < n⌝))
    (fun x => iprop(∃ n : ℕ, ⌜x = LitV (LitInt (n : ℤ))⌝ ∗ ⌜0 ≤ n⌝)) $$ [Herr] []
  · wp_apply wp_rand_err_nat 5 5 0 rfl
    isplitl [Herr]
    · iapply ErrorCredit.ext _ $$ Herr
      norm_num
    iintro %x %Hx
    ipureintro
    exact ⟨x, rfl, Nat.pos_of_ne_zero Hx⟩
  · wp_apply wp_rand 5 5 rfl $$ []
    · itrivial
    iintro %x -
    ipureintro
    exact ⟨x, rfl, Nat.zero_le _⟩
  · iintro %v1 %v2 ⟨⟨%n1, %H1, %Hn1⟩, ⟨%n2, %H2, %Hn2⟩⟩
    subst H1 H2
    inext
    wp_pures
    rw [← Nat.cast_add]
    iapply HΦ
    ipureintro
    omega

end simple

/-! ## The complex proof -/

/-- Helper: `Rpower 6 (t + 1) = Rpower 6 t * 6` (Rocq: `Rpower_plus`, `Rpower_1`). -/
theorem six_rpow_add_one (t : ℝ) : (6 : ℝ≥0∞) ^ (t + 1) = 6 ^ t * 6 := by
  rw [ENNReal.rpow_add t 1 (by norm_num) (by norm_num), ENNReal.rpow_one]

/-- Helper: the mean of the error function of `wp_couple_rand_adv_comp1'` used in
`complex_parallel_add_spec` (Rocq: `rewrite SeriesC_finite_foldr; ...; lra`). -/
theorem six_rpow_mean (t : ℝ) :
    ∑' x : Fin (5 + 1), 1 / ((5 : ℕ) + 1 : ℝ≥0∞) *
      (if (x : ℕ) = 0 then (6 : ℝ≥0∞) ^ (t + 1) else 0) ≤ 6 ^ t := by
  rw [tsum_fintype, Fin.sum_univ_succ]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_one_ne_zero, mul_zero,
    Finset.sum_const_zero, add_zero, six_rpow_add_one]
  rw [mul_comm, mul_assoc]
  norm_num
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- Helper: `Rpower 6 (INR 0 - 2) = 1 / 36`. -/
theorem six_rpow_zero_sub_two : (6 : ℝ≥0∞) ^ (((0 : ℕ) : ℝ) - 2) = 1 / 36 := by
  rw [Nat.cast_zero, zero_sub, ENNReal.rpow_neg, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast]
  norm_num

/-- Helper: `Rpower 6 (INR 2 - 2) = 1`. -/
theorem six_rpow_two_sub_two : (6 : ℝ≥0∞) ^ (((2 : ℕ) : ℝ) - 2) = 1 := by
  norm_num

/-- Helper (Rocq infers it): an `if` of timeless propositions is timeless. -/
instance ite_timeless {GF : BundledGFunctors} (c : Prop) [Decidable c] (P Q : IProp GF)
    [Timeless P] [Timeless Q] : Timeless (if c then P else Q) := by
  split <;> infer_instance

section complex

attribute [local instance] Classical.propDecidable

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [ElemG GF (excl_authF (Option ℕ))]

/-- Rocq: `parallel_add_inv`. -/
def parallel_add_inv (γ1 γ2 : GName) : IProp GF :=
  iprop(∃ (n1 n2 : Option ℕ),
    own_auth γ1 n1 ∗ own_auth γ2 n2 ∗
    if (∃ x, n1 = some x ∧ 0 < x) ∨ (∃ x, n2 = some x ∧ 0 < x)
    then ↯ 0
    else
      ∃ flip_num : ℕ,
        ↯ ((6 : ℝ≥0∞) ^ ((flip_num : ℝ) - 2)) ∗
        ⌜flip_num = (decide (n1 = some 0)).toNat + (decide (n2 = some 0)).toNat⌝)

/-- Rocq: `complex_parallel_add_spec`. -/
theorem complex_parallel_add_spec :
    {{ ↯ (1 / 36) }} two_die_prog
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (⌜0 < n⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  imod ghost_var_alloc none with ⟨%γ1, Hauth1, Hfrag1⟩
  imod ghost_var_alloc none with ⟨%γ2, Hauth2, Hfrag2⟩
  imod inv_alloc nroot ⊤ (parallel_add_inv γ1 γ2) $$ [Hauth1 Hauth2 Herr] with #I
  · inext
    unfold parallel_add_inv
    iexists none, none
    iframe
    rw [ite_eq_right (by simp)]
    iexists 0
    rw [six_rpow_zero_sub_two]
    iframe
    ipureintro
    rfl
  unfold two_die_prog parallel_add_inv
  wp_pures
  wp_apply wp_par' (fun x => iprop(∃ n : ℕ, ⌜x = LitV (LitInt (n : ℤ))⌝ ∗ own_frag γ1 (some n)))
    (fun x => iprop(∃ n : ℕ, ⌜x = LitV (LitInt (n : ℤ))⌝ ∗ own_frag γ2 (some n)))
    $$ [Hfrag1] [Hfrag2]
  · iinv I with ⟨%n1, %n2, >Hauth1, >Hauth2, >Herr⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hauth1 Hfrag1
    subst Heq
    by_cases H : (∃ x, (none : Option ℕ) = some x ∧ 0 < x) ∨ (∃ x, n2 = some x ∧ 0 < x)
    · rw [ite_eq_left H]
      wp_apply wp_rand 5 5 rfl $$ []
      · itrivial
      iintro %n -
      imod ghost_var_update γ1 (some (n : ℕ)) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
      imod Hclose $$ [Hauth1 Hauth2 Herr]
      · inext
        iexists some (n : ℕ), n2
        rw [ite_eq_left (by simp_all)]
        iframe
      imodintro
      iexists n
      iframe Hfrag1
      ipureintro
      rfl
    · rw [ite_eq_right H]
      icases Herr with ⟨%flip_num, Herr, %Hflip⟩
      simp only [reduceCtorEq, decide_false, Bool.toNat_false, zero_add] at Hflip
      subst Hflip
      wp_apply wp_couple_rand_adv_comp1' 5 5 _
        (fun x => if (x : ℕ) = 0
          then (6 : ℝ≥0∞) ^ (((decide (n2 = some 0)).toNat : ℝ) - 2 + 1) else 0)
        rfl (six_rpow_mean _) $$ Herr with %n Herr
      imod ghost_var_update γ1 (some (n : ℕ)) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
      imod Hclose $$ [Hauth1 Hauth2 Herr]
      · inext
        iexists some (n : ℕ), n2
        by_cases H1 : (n : ℕ) = 0
        · simp only [H1, ↓reduceIte]
          rw [ite_eq_right (by
            rintro (⟨x, hx, hx'⟩ | hx)
            · simp only [Option.some.injEq] at hx; omega
            · exact H (Or.inr hx))]
          iframe Hauth1 Hauth2
          iexists 1 + (decide (n2 = some 0)).toNat
          isplitl
          · iapply ErrorCredit.ext _ $$ Herr
            push_cast
            ring_nf
          · ipureintro
            simp
        · rw [ite_eq_left (Or.inl ⟨n, rfl, by omega⟩)]
          simp only [H1, ↓reduceIte]
          iframe
      imodintro
      iexists n
      iframe Hfrag1
      ipureintro
      rfl
  · iinv I with ⟨%n1, %n2, >Hauth1, >Hauth2, >Herr⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hauth2 Hfrag2
    subst Heq
    by_cases H : (∃ x, n1 = some x ∧ 0 < x) ∨ (∃ x, (none : Option ℕ) = some x ∧ 0 < x)
    · rw [ite_eq_left H]
      wp_apply wp_rand 5 5 rfl $$ []
      · itrivial
      iintro %n -
      imod ghost_var_update γ2 (some (n : ℕ)) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
      imod Hclose $$ [Hauth1 Hauth2 Herr]
      · inext
        iexists n1, some (n : ℕ)
        rw [ite_eq_left (by simp_all)]
        iframe
      imodintro
      iexists n
      iframe Hfrag2
      ipureintro
      rfl
    · rw [ite_eq_right H]
      icases Herr with ⟨%flip_num, Herr, %Hflip⟩
      simp only [reduceCtorEq, decide_false, Bool.toNat_false, add_zero] at Hflip
      subst Hflip
      wp_apply wp_couple_rand_adv_comp1' 5 5 _
        (fun x => if (x : ℕ) = 0
          then (6 : ℝ≥0∞) ^ (((decide (n1 = some 0)).toNat : ℝ) - 2 + 1) else 0)
        rfl (six_rpow_mean _) $$ Herr with %n Herr
      imod ghost_var_update γ2 (some (n : ℕ)) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
      imod Hclose $$ [Hauth1 Hauth2 Herr]
      · inext
        iexists n1, some (n : ℕ)
        by_cases H1 : (n : ℕ) = 0
        · simp only [H1, ↓reduceIte]
          rw [ite_eq_right (by
            rintro (hx | ⟨x, hx, hx'⟩)
            · exact H (Or.inl hx)
            · simp only [Option.some.injEq] at hx; omega)]
          iframe Hauth1 Hauth2
          iexists (decide (n1 = some 0)).toNat + 1
          isplitl
          · iapply ErrorCredit.ext _ $$ Herr
            push_cast
            ring_nf
          · ipureintro
            simp
        · rw [ite_eq_left (Or.inr ⟨n, rfl, by omega⟩)]
          simp only [H1, ↓reduceIte]
          iframe
      imodintro
      iexists n
      iframe Hfrag2
      ipureintro
      rfl
  · iintro %v1 %v2 ⟨⟨%n, %H1, Hfrag1⟩, ⟨%n', %H2, Hfrag2⟩⟩
    subst H1 H2
    inext
    wp_pures
    iinv I with ⟨%n1, %n2, >Hauth1, >Hauth2, >Herr⟩ Hclose
    ihave %Heq1 := ghost_var_agree $$ Hauth1 Hfrag1
    ihave %Heq2 := ghost_var_agree $$ Hauth2 Hfrag2
    subst Heq1 Heq2
    by_cases hz : n = 0 ∧ n' = 0
    · obtain ⟨rfl, rfl⟩ := hz
      rw [ite_eq_right (by simp)]
      icases Herr with ⟨%flip_num, Herr, %Hflip⟩
      simp only [decide_true, Bool.toNat_true] at Hflip
      subst Hflip
      iexfalso
      iapply ErrorCredit.contradict (le_of_eq six_rpow_two_sub_two.symm) $$ Herr
    imod Hclose $$ [Hauth1 Hauth2 Herr]
    · inext
      iexists some n, some n'
      iframe
    imodintro
    rw [← Nat.cast_add]
    iapply HΦ
    ipureintro
    omega

end complex

end Coneris.Examples.TwoDie
