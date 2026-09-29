module

public import Metrology.Foxtrot.AdequacyInstance
public import Metrology.Foxtrot.BinaryRel.BinarySoundness
public import Metrology.Foxtrot.CouplingRulesMisc

/-!
# `randombytes_uniform` from libsodium: programs and common lemmas

Ported from clutch/theories/foxtrot/examples/libsodium.v (part 1: programs and helpers)

`randombytes_uniform` implementation from libsodium
<https://github.com/jedisct1/libsodium/blob/85ddc5c2c6c7b8f7c99f9af6039e18f1f2ca0daa/src/libsodium/randombytes/randombytes.c#L146>.
The code is simplified (we assume `randombytes_random` distributes uniformly). We also do a
check that the input is a number smaller than `MAX` (usually `2^32`).

## Rocq → Lean map
* `randombytes_uniform`, `ideal_uniform`: same names (parameterised by `MAX : ℕ`, the section
  variable of Rocq).
* The anonymous intermediate programs of the `ctx_refines_transitive` steps of Rocq are named:
  - `rbu_fork` (first step of `randombytes_uniform_refines_ideal`),
  - `rbu_rem` (second step of `randombytes_uniform_refines_ideal` and of
    `ideal_refines_randombytes_uniform`),
  - `rbu_tapes` (first step of `ideal_refines_randombytes_uniform`),
  - `rbu_rem_tape` (third step of `ideal_refines_randombytes_uniform`).
* Rocq's local `Ltac start K j` is the lemma `start` (below): a refinement between two
  `TNat → TNat` functions follows from a WP of the application of the left function to `#n`
  against the application of the right function to `#n` on the spec side.
* Rocq's `foxtrotRΣ` is `foxtrotSigma` (with the instance `foxtrotRGpreS_foxtrotSigma`).

## Deviations
* Rocq's `if: e0 then e1 else e2` has `e2` at level 200, so `if: .. else e ;; e'` has the
  sequence in the `else` branch; in the Lean notation `;` binds looser than `if`, so the
  sequence is parenthesised (`rbu_fork`).
* The binary `-` of the Lean program notation is right-associative (`a - b - c` parses as
  `a - (b - c)`), unlike Rocq's left-associative `-`, so `#MAX - (#MAX `rem` ub) - #1` is
  written `(#MAX - (#MAX % ub)) - #1`.
* Rocq's `` `quot` ``/`` `rem` `` are `/`/`%` in the program notation (`Int.tdiv`/`Int.tmod`).
* The arithmetic facts that Rocq proves inline (by `lia` and `Nat`/`Z` lemmas) are factored
  into the lemmas of the section `arith`.

## Added
* `two_rands_cond1`, `two_rands_cond2`, `two_rands_cond3` (the side conditions of the
  `(x, y) ↦ x + y * n` couplings), `max_sub_rem`, `rej_f` (Rocq: the local `pose .. as f`),
  `rej_f_inj`, `rej_facts`, `rej_f_dom`, `rej_f_accept`, `rej_f_reject`, `rej_coeff_eq`,
  `rej_coeff_gt_one`: arithmetic helpers.
* `fill_nil'`, `fill_binopl`: `rfl` rewriting helpers for evaluation contexts of the spec
  points-to.
* `start` (Rocq's local `Ltac start`).

The proofs are in `LibsodiumFork`, `LibsodiumRem`, `LibsodiumLoop`, `LibsodiumTapes`,
`LibsodiumLoopRev`, and the main theorems in `LibsodiumMain`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel

namespace Foxtrot.Examples.Libsodium

/-- Rocq: `foxtrotRΣ`. -/
instance foxtrotRGpreS_foxtrotSigma : foxtrotRGpreS foxtrotSigma :=
  ⟨foxtrotGpreS_foxtrotSigma⟩

section programs

variable (MAX : ℕ)

/-- Rocq: `randombytes_uniform`. -/
def randombytes_uniform : val := cpl_val(
  λ upper_bound,
    if #MAX ≤ upper_bound then #0 else
      if upper_bound < #2 then #0 else
        let min := (#MAX % upper_bound) in
        let r := ref(#0) in
        (rec f x := r ← rand(#(MAX - 1 : ℕ));
                    if !r < min
                    then f #()
                    else (!r) % upper_bound
        ) #())

/-- Rocq: `ideal_uniform`. -/
def ideal_uniform : val := cpl_val(
  λ upper_bound,
    if ((#MAX ≤ upper_bound) || (upper_bound = #0)) then #0 else
      rand(upper_bound - #1))

/-- Rocq: the first intermediate program of `randombytes_uniform_refines_ideal`. -/
def rbu_fork : val := cpl_val(
  λ upper_bound,
    if #MAX ≤ upper_bound then #0 else
      if upper_bound = #0 then #0 else
        (fork(rand(#MAX / upper_bound - #1)); rand(upper_bound - #1)))

/-- Rocq: the second intermediate program of `randombytes_uniform_refines_ideal` (and of
`ideal_refines_randombytes_uniform`). -/
def rbu_rem : val := cpl_val(
  λ upper_bound,
    if #MAX ≤ upper_bound then #0 else
      if upper_bound = #0 then #0 else
        (rand((#MAX - (#MAX % upper_bound)) - #1)) % upper_bound)

/-- Rocq: the first intermediate program of `ideal_refines_randombytes_uniform`. -/
def rbu_tapes : val := cpl_val(
  λ upper_bound,
    if #MAX ≤ upper_bound then #0 else
      if upper_bound = #0 then #0 else
        let α := alloc(upper_bound - #1) in
        let β := alloc(#MAX / upper_bound - #1) in
        rand(α) (upper_bound - #1))

/-- Rocq: the third intermediate program of `ideal_refines_randombytes_uniform`. -/
def rbu_rem_tape : val := cpl_val(
  λ upper_bound,
    if #MAX ≤ upper_bound then #0 else
      if upper_bound = #0 then #0 else
        (rand(alloc((#MAX - (#MAX % upper_bound)) - #1)) ((#MAX - (#MAX % upper_bound)) - #1)) %
          upper_bound)

end programs

/-! ## Arithmetic facts (Rocq: inline `lia` proofs) -/

section arith

theorem two_rands_cond1 (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    ∀ x y, x < n - 1 + 1 → y < q - 1 + 1 → x + y * n < (n - 1 + 1) * (q - 1 + 1) := by
  intro x y hx hy
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hq] at *
  have : y * n ≤ (q - 1) * n := Nat.mul_le_mul_right _ (by omega)
  have h2 : (q - 1) * n + n = n * q := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  omega

theorem two_rands_cond2 (n M : ℕ) (hn : 0 < n) :
    ∀ x x' y y', x < n - 1 + 1 → x' < n - 1 + 1 → y < M + 1 → y' < M + 1 →
      x + y * n = x' + y' * n → x = x' ∧ y = y' := by
  intro x x' y y' hx hx' _ _ h
  have h1 := congrArg (· % n) h
  have h2 := congrArg (· / n) h
  simp only [Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hn] at h1 h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)] at h2
  omega

theorem two_rands_cond3 (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    ∀ x, x < (n - 1 + 1) * (q - 1 + 1) →
      ∃ a b, a < n - 1 + 1 ∧ b < q - 1 + 1 ∧ a + b * n = x := by
  intro x hx
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hq] at *
  refine ⟨x % n, x / n, Nat.mod_lt _ hn, ?_, ?_⟩
  · exact Nat.div_lt_of_lt_mul hx
  · have := Nat.mod_add_div x n
    rw [mul_comm] at this
    omega

/-- `MAX - MAX % n = n * (MAX / n)` (over `ℤ`). -/
theorem max_sub_rem (MAX n : ℕ) :
    ((MAX : ℤ) - Int.tmod (MAX : ℤ) (n : ℤ)) = ((n * (MAX / n) : ℕ) : ℤ) := by
  rw [← Int.ofNat_tmod]
  have := Nat.mod_add_div MAX n
  omega

/-- Rocq: the local function `f` of the rejection-sampling coupling (`pose (λ x, ..) as f`). It
maps `[0, MAX - MAX mod n)` injectively onto the accepted values `[MAX mod n, MAX)`. -/
def rej_f (MAX n : ℕ) (x : ℕ) : ℕ :=
  if MAX - MAX % n ≤ x then x + MAX else if x < MAX % n then x + MAX - MAX % n else x

theorem rej_f_inj (MAX n : ℕ) : Function.Injective (rej_f MAX n) := by
  have := Nat.mod_le MAX n
  intro x y
  unfold rej_f
  split_ifs <;> omega

theorem rej_facts (MAX n : ℕ) (hn : 0 < n) (hnM : n < MAX) :
    MAX % n < n ∧ n ≤ MAX - MAX % n ∧ MAX - MAX % n = n * (MAX / n) := by
  have h1 := Nat.mod_lt MAX hn
  have h2 := Nat.mod_add_div MAX n
  have hq : 0 < MAX / n := Nat.div_pos (by omega) hn
  have h3 : n ≤ n * (MAX / n) := Nat.le_mul_of_pos_right n hq
  omega

theorem rej_f_dom (MAX n : ℕ) (hn : 0 < n) (hnM : n < MAX) :
    ∀ x, x < (MAX - MAX % n - 1) + 1 → rej_f MAX n x < (MAX - 1) + 1 := by
  obtain ⟨h1, h2, -⟩ := rej_facts MAX n hn hnM
  intro x hx
  unfold rej_f
  split_ifs <;> omega

theorem rej_f_accept (MAX n : ℕ) (hn : 0 < n) (hnM : n < MAX) (m : ℕ)
    (hm : m ≤ MAX - MAX % n - 1) :
    MAX % n ≤ rej_f MAX n m ∧ rej_f MAX n m % n = m % n := by
  obtain ⟨h1, h2, h3⟩ := rej_facts MAX n hn hnM
  unfold rej_f
  split_ifs with ha hb
  · omega
  · refine ⟨by omega, ?_⟩
    rw [show m + MAX - MAX % n = m + n * (MAX / n) by omega, Nat.add_mul_mod_self_left]
  · exact ⟨by omega, rfl⟩

theorem rej_f_reject (MAX n : ℕ) (hn : 0 < n) (hnM : n < MAX) (x : ℕ) (hx : x ≤ MAX - 1)
    (H : ¬ ∃ m, m ≤ MAX - MAX % n - 1 ∧ rej_f MAX n m = x) : x < MAX % n := by
  obtain ⟨h1, h2, -⟩ := rej_facts MAX n hn hnM
  by_contra hc
  apply H
  by_cases hx' : MAX - MAX % n ≤ x
  · refine ⟨x - (MAX - MAX % n), by omega, ?_⟩
    unfold rej_f
    split_ifs <;> omega
  · refine ⟨x, by omega, ?_⟩
    unfold rej_f
    split_ifs
    omega

/-- The amplification factor of the rejection-sampling coupling (Rocq: the argument
`MAX / (MAX - (MAX - MAX mod n))` of `ec_ind_simpl`), as a coefficient of `ℝ≥0`. Since
`0 < r < MAX`, the truncated `ℝ≥0∞` subtraction is the real one and the division is by a
non-zero number. -/
theorem rej_coeff_eq (MAX r : ℕ) (hr : 0 < r) (hrM : r < MAX) :
    ((MAX - 1 + 1 : ℕ) : ℝ≥0∞) / (((MAX - 1 + 1 : ℕ) : ℝ≥0∞) - ((MAX - r - 1 + 1 : ℕ) : ℝ≥0∞)) =
      (((MAX : ℝ≥0) / (r : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  rw [show MAX - 1 + 1 = MAX by omega, show MAX - r - 1 + 1 = MAX - r by omega,
    ← ENNReal.natCast_sub, show MAX - (MAX - r) = r by omega,
    ENNReal.coe_div (by exact_mod_cast hr.ne')]
  simp

/-- Rocq: the side condition `1 < MAX / (MAX - (MAX - MAX mod n))` of `ec_ind_simpl`. -/
theorem rej_coeff_gt_one (MAX r : ℕ) (hr : 0 < r) (hrM : r < MAX) :
    1 < (MAX : ℝ≥0) / (r : ℝ≥0) :=
  (one_lt_div (by exact_mod_cast hr)).2 (by exact_mod_cast hrM)

end arith

/-- Helper (Rocq: `fill_empty`, used by `rewrite -(fill_empty ..)`): `fill [] e = e`, for the
`con_prob_lang` `fill` of the spec points-to (whose `@[simp]` lemma is stated for the generic
language `fill`). -/
theorem fill_nil' (e : expr) : fill [] e = e := rfl

/-- Helper: undo the evaluation context `[BinOpLCtx op v]` introduced by `tp_bind`. -/
theorem fill_binopl (op : bin_op) (v : val) (K : List ectx_item) (e : expr) :
    fill ([BinOpLCtx op v] ++ K) e = fill K (BinOp op e (Val v)) := rfl

/-! ## The `start` tactic of Rocq -/

/-- Rocq: `Ltac start K j` (as a lemma). -/
theorem start (f1 f2 : val)
    (H : ∀ [foxtrotRGS foxtrotSigma] (n : ℕ) (K : List ectx_item) (j : ℕ),
      ⊢@{IProp foxtrotSigma} j ⤇ fill K (App (Val f2) (Val (LitV (LitInt (n : ℤ))))) -∗
        WP (App (Val f1) (Val (LitV (LitInt (n : ℤ))))) {{ v, ∃ m : ℕ,
          ⌜v = LitV (LitInt (m : ℤ))⌝ ∗ j ⤇ fill K (Val (LitV (LitInt (m : ℤ)))) }}) :
    (∅ : varmap type) ⊨ Val f1 ≤ctx≤ Val f2 : TArrow TNat TNat := by
  apply refines_sound foxtrotSigma
  intro _ Δ
  unfold_rel
  iintro %K %j Hspec
  wp_pures
  iexists f2
  iframe Hspec
  imodintro
  dsimp only [interp_TArrow, interp_TNat, lrel_arr, lrel_nat]
  iintro !> %v1 %v2 ⟨%n, %Hv1, %Hv2⟩
  subst Hv1 Hv2
  unfold_rel
  iintro %K' %j' Hspec
  ihave Hwp := H n K' j' $$ Hspec
  iapply wp_wand $$ Hwp
  iintro %v ⟨%m, %Hv, Hspec⟩
  iexists LitV (LitInt (m : ℤ))
  iframe Hspec
  iexists m
  ipureintro
  exact ⟨Hv, rfl⟩

end Foxtrot.Examples.Libsodium
