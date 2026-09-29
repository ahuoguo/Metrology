module

public import Metrology.Coneris.Examples.TwoDiePart2

/-!
# Two dice: the proof of `con_prog` presented in the Coneris paper

Ported from clutch/theories/coneris/examples/two_die.v (third part: `T`, `sampled`,
`one_positive`, `added_1`, sections `lemmasT` and `complex'`)

See `Coneris.Examples.TwoDie` for the Rocq → Lean map, the deviations and the omissions of
the whole Rocq file.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par
open Iris.ExclAuth

namespace Coneris.Examples.TwoDie

attribute [local instance] Classical.propDecidable

/-- Rocq: `T`. -/
inductive T : Type where
  | S0 : T
  | S1 : (n : ℕ) → n > 0 → T
  | S2 : (n : ℕ) → T
  deriving DecidableEq

instance : Inhabited T := ⟨T.S0⟩

open T

/-- Rocq: `sampled`. -/
def sampled : T → Option ℕ
  | S0 => none
  | S1 n _ => some n
  | S2 n => some n

/-- Rocq: `one_positive`. -/
def one_positive (n1 n2 : T) : Bool :=
  decide (∃ n : ℕ, n > 0 ∧ (sampled n1 = some n ∨ sampled n2 = some n))

/-- Rocq: `added_1`. -/
def added_1 (s : T) : Bool :=
  decide (∃ n : ℕ, n > 0 ∧ s = S2 n)

/-- Rocq: `TO` (`leibnizO T`). -/
abbrev TO : Type := DiscreteO T

theorem added_1_S0 : added_1 S0 = false := by
  simp [added_1]

theorem added_1_S1 (n : ℕ) (h : n > 0) : added_1 (S1 n h) = false := by
  simp [added_1]

theorem added_1_S2 (n : ℕ) : added_1 (S2 n) = decide (n > 0) := by
  simp [added_1]

theorem one_positive_eq (s1 s2 : T) :
    one_positive s1 s2 = true ↔ ∃ n : ℕ, n > 0 ∧ (sampled s1 = some n ∨ sampled s2 = some n) := by
  simp [one_positive]

section lemmasT

variable {GF : BundledGFunctors} [ElemG GF (excl_authF T)]

/-- Rocq: `ghost_var_allocT`. -/
theorem ghost_var_allocT (b : T) :
    ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b :=
  excl_auth_alloc b

/-- Rocq: `ghost_var_agreeT`. -/
theorem ghost_var_agreeT (γ : GName) (b c : T) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ :=
  excl_auth_agree γ b c

/-- Rocq: `ghost_var_updateT`. -/
theorem ghost_var_updateT (γ : GName) (b' b c : T) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' :=
  excl_auth_update γ b' b c

end lemmasT

section complex'

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [ElemG GF (excl_authF T)]

/-- Rocq: `parallel_add_inv'`. -/
def parallel_add_inv' (γ1 γ2 : GName) (l : Loc) : IProp GF :=
  iprop(∃ (s1 s2 : T) (n : ℕ),
    own_auth γ1 s1 ∗ own_auth γ2 s2 ∗
    l ↦ LitV (LitInt (n : ℤ)) ∗
    (if added_1 s1 || added_1 s2 then ⌜0 < n⌝ else True) ∗
    if one_positive s1 s2
    then ↯ 0
    else
      ∃ flip_num : ℕ,
        ↯ ((6 : ℝ≥0∞) ^ ((flip_num : ℝ) - 2)) ∗
        ⌜flip_num = (decide (sampled s1 = some 0)).toNat +
          (decide (sampled s2 = some 0)).toNat⌝)

/-- Helper (Rocq: inlined, twice, in `complex_parallel_add_spec'`): the `FAA` of the first
thread, after it sampled a positive `x`. -/
theorem complex_parallel_add_spec'_faa1 (γ1 γ2 : GName) (l : Loc) (x : ℕ) (hx : x > 0) :
    inv nroot (parallel_add_inv' γ1 γ2 l) ∗ own_frag γ1 (S1 x hx) ⊢
      WP cpl(faa(#l, #1)) {{ _v, ∃ n : ℕ, own_frag (GF := GF) γ1 (S2 n) }} := by
  iintro ⟨#I, Hfrag1⟩
  unfold parallel_add_inv'
  iinv I with ⟨%s1, %s2, %n, >Hauth1, >Hauth2, >Hl, >H, >Herr⟩ Hclose
  ihave %Heq := ghost_var_agreeT $$ Hauth1 Hfrag1
  subst Heq
  wp_faa
  imod ghost_var_updateT γ1 (S2 x) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
  have hp : one_positive (S1 x hx) s2 = true :=
    (one_positive_eq _ _).2 ⟨x, hx, Or.inl rfl⟩
  have hp' : one_positive (S2 x) s2 = true :=
    (one_positive_eq _ _).2 ⟨x, hx, Or.inl rfl⟩
  rw [hp]
  imod Hclose $$ [Hauth1 Hauth2 Hl Herr]
  · inext
    iexists S2 x, s2, n + 1
    rw [hp', added_1_S2, decide_eq_true hx]
    simp only [Bool.true_or, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    iframe
    ipureintro
    omega
  imodintro
  iexists x
  iexact Hfrag1

/-- Helper (Rocq: inlined, twice, in `complex_parallel_add_spec'`): the `FAA` of the second
thread, after it sampled a positive `x`. -/
theorem complex_parallel_add_spec'_faa2 (γ1 γ2 : GName) (l : Loc) (x : ℕ) (hx : x > 0) :
    inv nroot (parallel_add_inv' γ1 γ2 l) ∗ own_frag γ2 (S1 x hx) ⊢
      WP cpl(faa(#l, #1)) {{ _v, ∃ n : ℕ, own_frag (GF := GF) γ2 (S2 n) }} := by
  iintro ⟨#I, Hfrag2⟩
  unfold parallel_add_inv'
  iinv I with ⟨%s1, %s2, %n, >Hauth1, >Hauth2, >Hl, >H, >Herr⟩ Hclose
  ihave %Heq := ghost_var_agreeT $$ Hauth2 Hfrag2
  subst Heq
  wp_faa
  imod ghost_var_updateT γ2 (S2 x) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
  have hp : one_positive s1 (S1 x hx) = true :=
    (one_positive_eq _ _).2 ⟨x, hx, Or.inr rfl⟩
  have hp' : one_positive s1 (S2 x) = true :=
    (one_positive_eq _ _).2 ⟨x, hx, Or.inr rfl⟩
  rw [hp]
  imod Hclose $$ [Hauth1 Hauth2 Hl Herr]
  · inext
    iexists s1, S2 x, n + 1
    rw [hp', added_1_S2, decide_eq_true hx]
    simp only [Bool.or_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    iframe
    ipureintro
    omega
  imodintro
  iexists x
  iexact Hfrag2

end complex'

end Coneris.Examples.TwoDie
