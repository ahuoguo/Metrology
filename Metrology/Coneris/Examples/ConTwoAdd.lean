module

public import Metrology.Coneris.Lib.Par
public import Metrology.Coneris.ErrorRules
public import Metrology.Coneris.Adequacy
public import Iris.Instances.Lib.GhostVar

/-!
# Two concurrent additions of random numbers

Ported from clutch/theories/coneris/examples/con_two_add.v (first part: programs, predicates,
invariant, `rand_step`, `faa_step`; the rest is in `ConTwoAddPart2`)

## Rocq → Lean map
* Namespace `Coneris.Examples.ConTwoAdd` (shared with `ConTwoAddPart2`). All names are kept:
  `two_add_prog'`, `T` (`S0`, `S1 n`, `S2 n`), `no_thread_added`, `one_thread_added`,
  `both_threads_added`, `no_thread_sampled`, `one_thread_sampled_zero`,
  `at_least_one_thread_sampled_non_zero`, `parallel_add_inv'`, `parallel_add_inv'_symmetric`,
  `rand_step`, `faa_step`.
* `conerisGS Σ, spawnG Σ, ghost_varG Σ T` are `[conerisGS GF] [spawnG GF] [GhostVarG GF T]`;
  `ghost_var γ (1/2) s` is iris-lean's `γ ↪VAR{.own ½} s` with `½ := Qp.half 1` (scoped
  notation). `ghost_var_agree`, `ghost_var_update_halves` are iris-lean's lemmas.
* `#n` for `n : nat` is `LitV (LitInt (n : ℤ))`; the `RET #n` of `rand_step` is
  `RET LitV (LitInt (n : ℤ))` with `n : ℕ` (instantiated with the `fin` sample coerced to `ℕ`).
* Errors are `ℝ≥0∞` (`↯ (1/16)`, `↯ (1/4)`, `↯ 1`, `↯ 0`); the error functions of
  `wp_couple_rand_adv_comp1'` are `ℝ≥0∞`-valued (nonnegativity side goals vanish). No truncated
  subtraction or division by zero is involved.
* `e1 ||| e2` is the local program notation `e1 ‖ e2` and `wp_par` is applied through the
  helper `wp_par'` (`par_V` unfolded), as in `Coneris.Examples.TwoDie`.
* `T` derives `DecidableEq, Inhabited` (`Inhabited` lets the proof mode commute `▷` with the
  existentials of the invariant when opening it, as Rocq's `iInv .. as ">..."` does).

## Proofs that differ from Rocq
* `iInv "I" as ">(...)"` (with implicit closing) is `iinv I with ⟨.., >H, ..⟩ Hclose` followed by
  an explicit `imod Hclose`.
* Rocq frames `Hstate` (stated for `s1 = S0`) into the invariant for `s1 = S1 n` by
  conversion; here the simp lemmas `no_thread_added_S1`, `one_thread_added_S1`,
  `both_threads_added_S1` rewrite the goal first.
* The pure case analyses (`destruct s1, s2; naive_solver`, `inversion`) are `cases .. <;>
  simp_all [..]` / `split at ..`.
* In `faa_step`'s second case, `iMod ec_zero` is kept; the old `↯ 0` of the invariant is dropped.
* The sums (`SeriesC_finite_foldr; lra`) are the helpers `rand3_mean`, `quarter_div_four`.

## Added
`‖` notation, `wp_par'`, `½` notation, `rand3_mean`, `quarter_div_four`, `no_thread_added_S1`,
`one_thread_added_S1`, `both_threads_added_S1` (helpers).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par

namespace Coneris.Examples.ConTwoAdd

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

/-- This is the con_two_add example in the paper of Coneris. Rocq: `two_add_prog'`. -/
def two_add_prog' : expr := cpl(
  let l := ref(#0) in
  ((faa(l, rand(#3)))
   ‖
   (faa(l, rand(#3))));
  !l)

/-! This is the proof sketched for the example con_two_add in the paper of Coneris.

This is **not** the most idiomatic/direct way to encode this proof, but it is structured to
match the structure/presentation in the text, where we tried to avoid pulling in too many high
level Iris ideas.

Each thread moves through a state machine with 3 states:
* `S0` --> initial state
* `S1 n` --> sampled `n`
* `S2 n` --> sampled and added `n` -/

/-- Rocq: `T`. -/
inductive T : Type where
  | S0 : T
  | S1 (n : ℕ) : T
  | S2 (n : ℕ) : T
  deriving DecidableEq, Inhabited

open T

/-! Next we define various (pure) predicates on the states of the threads that capture the
informal english descriptions described in the underbraces in the paper. -/

/-- Rocq: `no_thread_added`. -/
def no_thread_added : T → T → Prop
  | S2 _, _ => False
  | _, S2 _ => False
  | _, _ => True

/-- Rocq: `one_thread_added`. -/
def one_thread_added (n : ℕ) : T → T → Prop
  | S2 _, S2 _ => False
  | S2 n', _ => n = n'
  | _, S2 n' => n = n'
  | _, _ => False

/-- Rocq: `both_threads_added`. -/
def both_threads_added (n : ℕ) : T → T → Prop
  | S2 n1, S2 n2 => n = n1 + n2
  | _, _ => False

/-- Rocq: `no_thread_sampled`. -/
def no_thread_sampled : T → T → Prop
  | S0, S0 => True
  | _, _ => False

/-- Rocq: `one_thread_sampled_zero`. -/
def one_thread_sampled_zero : T → T → Prop
  | S1 0, S0 => True
  | S2 0, S0 => True
  | S0, S1 0 => True
  | S0, S2 0 => True
  | _, _ => False

/-- Rocq: `at_least_one_thread_sampled_non_zero`. -/
def at_least_one_thread_sampled_non_zero (t1 t2 : T) : Prop :=
  (match t1 with
   | S0 => False
   | S1 n => n > 0
   | S2 n => n > 0) ∨
  (match t2 with
   | S0 => False
   | S1 n => n > 0
   | S2 n => n > 0)

/-- `1/2 : Qp`. -/
scoped notation "½" => Qp.half (1 : Qp)

section complex'

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [GhostVarG GF T]

/-- Rocq: `parallel_add_inv'`. The invariant needed for the parallel add.

The first line is ghost state omitted from the paper discussion. See `parallel_add_inv` at the
end of the file for an alternate version that matches even more closely the syntactic form of
the paper. -/
def parallel_add_inv' (γ1 γ2 : GName) (l : Loc) : IProp GF :=
  iprop(∃ (s1 s2 : T), (γ1 ↪VAR{.own ½} s1) ∗ (γ2 ↪VAR{.own ½} s2) ∗
    (((l ↦ LitV (LitInt 0) ∗ ⌜no_thread_added s1 s2⌝) ∨
      (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ ⌜one_thread_added n s1 s2⌝) ∨
      (∃ n : ℕ, l ↦ LitV (LitInt (n : ℤ)) ∗ ⌜n > 0⌝ ∗ ⌜both_threads_added n s1 s2⌝)) ∗
     ((↯ (1 / 16) ∗ ⌜no_thread_sampled s1 s2⌝) ∨
      (↯ (1 / 4) ∗ ⌜one_thread_sampled_zero s1 s2⌝) ∨
      (↯ 1) ∨ -- both_thread_sampled_zero
      (↯ 0 ∗ ⌜at_least_one_thread_sampled_non_zero s1 s2⌝))))

/-- Rocq: `parallel_add_inv'_symmetric`. -/
theorem parallel_add_inv'_symmetric (γ1 γ2 : GName) (l : Loc) :
    parallel_add_inv' (GF := GF) γ1 γ2 l ⊢ parallel_add_inv' γ2 γ1 l := by
  unfold parallel_add_inv'
  iintro ⟨%s1, %s2, Hauth1, Hauth2, Hstate, Hsamp⟩
  iexists s2, s1
  iframe Hauth1 Hauth2
  isplitl [Hstate]
  · icases Hstate with (⟨Hl, %Hp⟩ | ⟨%n, Hl, %Hp⟩ | ⟨%n, Hl, %Hgt, %Hp⟩)
    · ileft
      iframe Hl
      ipureintro
      cases s1 <;> cases s2 <;> simp_all [no_thread_added]
    · iright
      ileft
      iexists n
      iframe Hl
      ipureintro
      cases s1 <;> cases s2 <;> simp_all [one_thread_added]
    · iright
      iright
      iexists n
      iframe Hl
      ipureintro
      refine ⟨Hgt, ?_⟩
      cases s1 <;> cases s2 <;> simp_all [both_threads_added]
      omega
  · icases Hsamp with (⟨Herr, %Hp⟩ | ⟨Herr, %Hp⟩ | Herr | ⟨Herr, %Hp⟩)
    · ileft
      iframe Herr
      ipureintro
      cases s1 <;> cases s2 <;> simp_all [no_thread_sampled]
    · iright
      ileft
      iframe Herr
      ipureintro
      unfold one_thread_sampled_zero at Hp ⊢
      split at Hp <;> simp_all
    · iright
      iright
      ileft
      iexact Herr
    · iright
      iright
      iright
      iframe Herr
      ipureintro
      unfold at_least_one_thread_sampled_non_zero at Hp ⊢
      exact Hp.symm

/-- Helper: the mean of a one-point error function on `rand #3`. -/
theorem rand3_mean (c : ℝ≥0∞) :
    ∑' x : Fin (3 + 1), 1 / ((3 : ℕ) + 1 : ℝ≥0∞) * (if (x : ℕ) = 0 then c else 0) = c / 4 := by
  rw [tsum_fintype, Fin.sum_univ_succ]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_one_ne_zero, mul_zero,
    Finset.sum_const_zero, add_zero]
  norm_num
  rw [ENNReal.div_eq_inv_mul, mul_comm]

/-- Helper: `(1/4)/4 = 1/16`. -/
theorem quarter_div_four : (1 / 4 : ℝ≥0∞) / 4 = 1 / 16 := by
  rw [div_eq_mul_inv, one_div, one_div, ← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

/-- Helper: the state predicates do not distinguish `S0` from `S1 m` (Rocq: by conversion). -/
@[simp] theorem no_thread_added_S1 (m : ℕ) (s : T) :
    no_thread_added (S1 m) s = no_thread_added S0 s := by
  cases s <;> rfl

@[simp, inherit_doc no_thread_added_S1] theorem one_thread_added_S1 (n m : ℕ) (s : T) :
    one_thread_added n (S1 m) s = one_thread_added n S0 s := by
  cases s <;> rfl

@[simp, inherit_doc no_thread_added_S1] theorem both_threads_added_S1 (n m : ℕ) (s : T) :
    both_threads_added n (S1 m) s = both_threads_added n S0 s := by
  cases s <;> rfl

/-- Rocq: `rand_step`. -/
theorem rand_step (γ1 γ2 : GName) (l : Loc) :
    {{ inv nroot (parallel_add_inv' γ1 γ2 l) ∗ (γ1 ↪VAR{.own ½} S0) }}
      (Rand (Val (LitV (LitInt 3))) (Val (LitV LitUnit)))
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); ((γ1 ↪VAR{.own ½} (S1 n)) : IProp GF) }} := by
  iintro %Φ ⟨#I, Hfrag1⟩ HΦ
  unfold parallel_add_inv'
  iinv I with ⟨%s1, %s2, >Hauth1, >Hauth2, >Hstate, >Hsamp⟩ Hclose
  ihave %Heq := ghost_var_agree γ1 _ _ _ _ $$ Hauth1 Hfrag1
  subst Heq
  icases Hsamp with (⟨Herr, %Hpure⟩ | ⟨Herr, %Hpure⟩ | Hbogus | ⟨Herr, %Hpure⟩)
  · have : s2 = S0 := by cases s2 <;> simp_all [no_thread_sampled]
    subst this
    wp_apply wp_couple_rand_adv_comp1' 3 3 _ (fun x => if (x : ℕ) = 0 then 1 / 4 else 0) rfl
      (by rw [rand3_mean, quarter_div_four]) $$ Herr with %x Herr
    imod ghost_var_update_halves (S1 (x : ℕ)) γ1 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
    imod Hclose $$ [Hauth1 Hauth2 Hstate Herr]
    · inext
      iexists S1 (x : ℕ), S0
      simp only [no_thread_added_S1, one_thread_added_S1, both_threads_added_S1]
      iframe Hauth1 Hauth2 Hstate
      by_cases hx : (x : ℕ) = 0
      · simp only [hx, ↓reduceIte]
        iright
        ileft
        iframe Herr
        ipureintro
        simp [one_thread_sampled_zero]
      · simp only [hx, ↓reduceIte]
        iright
        iright
        iright
        iframe Herr
        ipureintro
        left
        show (x : ℕ) > 0
        omega
    imodintro
    iapply HΦ $$ Hfrag1
  · wp_apply wp_couple_rand_adv_comp1' 3 3 _ (fun x => if (x : ℕ) = 0 then 1 else 0) rfl
      (by rw [rand3_mean, one_div]) $$ Herr with %x Herr
    imod ghost_var_update_halves (S1 (x : ℕ)) γ1 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
    imod Hclose $$ [Hauth1 Hauth2 Hstate Herr]
    · inext
      iexists S1 (x : ℕ), s2
      simp only [no_thread_added_S1, one_thread_added_S1, both_threads_added_S1]
      iframe Hauth1 Hauth2 Hstate
      by_cases hx : (x : ℕ) = 0
      · simp only [hx, ↓reduceIte]
        iright
        iright
        ileft
        iexact Herr
      · simp only [hx, ↓reduceIte]
        iright
        iright
        iright
        iframe Herr
        ipureintro
        left
        show (x : ℕ) > 0
        omega
    imodintro
    iapply HΦ $$ Hfrag1
  · iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Hbogus
  · wp_apply wp_rand 3 3 rfl $$ [] with %x -
    · itrivial
    imod ghost_var_update_halves (S1 (x : ℕ)) γ1 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
    imod Hclose $$ [Hauth1 Hauth2 Hstate Herr]
    · inext
      iexists S1 (x : ℕ), s2
      simp only [no_thread_added_S1, one_thread_added_S1, both_threads_added_S1]
      iframe Hauth1 Hauth2 Hstate
      iright
      iright
      iright
      iframe Herr
      ipureintro
      unfold at_least_one_thread_sampled_non_zero at Hpure ⊢
      simp only [false_or] at Hpure
      exact Or.inr Hpure
    imodintro
    iapply HΦ $$ Hfrag1

/-- Rocq: `faa_step`. -/
theorem faa_step (γ1 γ2 : GName) (l : Loc) (n : ℕ) :
    {{ inv nroot (parallel_add_inv' γ1 γ2 l) ∗ (γ1 ↪VAR{.own ½} (S1 n)) }}
      (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt (n : ℤ)))))
    {{ v, RET v; ((γ1 ↪VAR{.own ½} (S2 n)) : IProp GF) }} := by
  iintro %Φ ⟨#I, Hfrag1⟩ HΦ
  unfold parallel_add_inv'
  iinv I with ⟨%s1, %s2, >Hauth1, >Hauth2, >Hstate, >Hsamp⟩ Hclose
  ihave %Heq := ghost_var_agree γ1 _ _ _ _ $$ Hauth1 Hfrag1
  subst Heq
  icases Hstate with (⟨Hl, %Hcase⟩ | ⟨%n', Hl, %Hcase⟩ | ⟨%n', Hl, %Hgt, %Hp⟩)
  · wp_faa
    imod ghost_var_update_halves (S2 n) γ1 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
    imod Hclose $$ [Hauth1 Hauth2 Hsamp Hl]
    · inext
      iexists S2 n, s2
      iframe Hauth1 Hauth2
      isplitl [Hl]
      · iright
        ileft
        iexists n
        rw [zero_add]
        iframe Hl
        ipureintro
        cases s2 <;> simp_all [one_thread_added, no_thread_added]
      · icases Hsamp with (⟨Hnosamp, %Hp⟩ | ⟨Hone0, %Hp⟩ | Hbogus | ⟨Honenonzero, %Hp⟩)
        · exact absurd Hp (by simp [no_thread_sampled])
        · iright
          ileft
          iframe Hone0
          ipureintro
          unfold one_thread_sampled_zero at Hp ⊢
          split at Hp <;> simp_all
        · iright
          iright
          ileft
          iexact Hbogus
        · iright
          iright
          iright
          iframe Honenonzero
          ipureintro
          exact Hp
    imodintro
    iapply HΦ $$ Hfrag1
  · have hs2 : s2 = S2 n' := by
      cases s2 <;> simp_all [one_thread_added]
    subst hs2
    wp_faa
    ihave %Hatleast : ⌜at_least_one_thread_sampled_non_zero (S2 n) (S2 n')⌝ $$ [Hsamp]
    · icases Hsamp with (⟨_, %Hp⟩ | ⟨_, %Hp⟩ | H1 | ⟨_, %Hp⟩)
      · exact absurd Hp (by simp [no_thread_sampled])
      · exact absurd Hp (by cases n <;> simp [one_thread_sampled_zero])
      · iexfalso
        iapply ErrorCredit.contradict le_rfl $$ H1
      · ipureintro
        exact Hp
    imod ErrorCredit.zero with Hzero
    imod ghost_var_update_halves (S2 n) γ1 _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
    imod Hclose $$ [Hauth1 Hauth2 Hl Hzero]
    · inext
      iexists S2 n, S2 n'
      iframe Hauth1 Hauth2
      isplitl [Hl]
      · iright
        iright
        iexists n' + n
        rw [Nat.cast_add]
        iframe Hl
        ipureintro
        unfold at_least_one_thread_sampled_non_zero at Hatleast
        simp only [both_threads_added]
        omega
      · iright
        iright
        iright
        iframe Hzero
        ipureintro
        exact Hatleast
    imodintro
    iapply HΦ $$ Hfrag1
  · exact absurd Hp (by simp [both_threads_added])

end complex'

end Coneris.Examples.ConTwoAdd
