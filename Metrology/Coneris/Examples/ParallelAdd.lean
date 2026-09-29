module

public import Metrology.Coneris.Lib.Par
public import Metrology.Coneris.Lib.Flip
public import Metrology.Coneris.ErrorRules
public import Iris.Algebra.Lib.ExclAuth
public import Iris.Algebra.Lib.FracAuth
public import Iris.Algebra.Numbers
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Parallel additions of coin flips

Ported from clutch/theories/coneris/examples/parallel_add.v (first part: the ghost-state
lemmas and section `simple_parallel_add`; the rest is in `ParallelAddPart2`..`Part4`)

## Rocq → Lean map (all four parts)
* Namespace `Coneris.Examples.ParallelAdd` (shared by the four modules). All names are kept:
  `ghost_var_alloc`/`_agree`/`_update` (+ primed, `Z`, `_frac` variants), `resource_nonneg`,
  `simple_parallel_add`, `simple_parallel_add_inv`, `simple_parallel_add_spec`, `half_FAA`,
  `parallel_add`, `is_Some_true`, `parallel_add_inv`, `parallel_add_spec`, `parallel_add_spec'`
  (Part2/Part3), `loc_nroot`, `both_nroot`, `half_FAA'`, `parallel_add'`, `wp_half_FAA'`,
  `parallel_add_spec'''` (Part4).
* `inG Σ (excl_authR A)` (for `A = boolO`, `optionO boolO`, `ZR`) is
  `ElemG GF (excl_authF A)` with `excl_authF A := constOF (ExclAuthR (A := DiscreteO A))`;
  `own γ (●E a)`/`own γ (◯E a)` are `own_auth γ a`/`own_frag γ a`.
* `ZR` is `ℤ` with iris-lean's constant-core CMRA `CommMonoidLike.instCMRA` (scoped instances
  in this namespace; iris-lean has no global `(ℤ, +)` CMRA); `Z_local_update` is
  `CommMonoidLike.leftCancelAdd_local_update`. `inG Σ (frac_authR ZR)` is
  `ElemG GF frac_authF`, `own γ (●F z)`/`own γ (◯F{q} z)` are `own_authF γ z`/`own_fragF γ q z`
  (so `◯F z` is `own_fragF γ 1 z`).
* `bool_to_Z` (stdpp) is a local helper; `bool_to_nat` is `Coneris.Lib.Flip.bool_to_nat`;
  `ssrbool.isSome` is `Option.isSome`.
* `conerisGS Σ, spawnG Σ` are `[conerisGS GF] [spawnG GF]`. `e1 ||| e2` is the local program
  notation `e1 ‖ e2` and `wp_par` is applied through the helper `wp_par'` (as in
  `Coneris.Examples.TwoDie`).
* Errors are `ℝ≥0∞`. `Rpower 2 x` is `(2 : ℝ≥0∞) ^ x` (`ENNReal.rpow`) in the invariants and
  `(2 : ℝ) ^ x` (`Real.rpow`) in `resource_nonneg`, which is stated over `ℝ` as in Rocq (in
  `ℝ≥0∞` the nonnegativity side goals it serves vanish). The Rocq invariant field
  `err : nonnegreal` with `nonneg err = 1 - Rpower 2 (INR flip_num - 2)` is `err : ℝ≥0∞` with
  `err = 1 - 2 ^ ((flip_num : ℝ) - 2)`: since `flip_num ≤ 2`, `2 ^ (flip_num - 2) ≤ 1` and the
  truncated subtraction agrees with Rocq. Likewise `2 * x - 1` in `parallel_add_spec'` is only
  used for `1/2 ≤ x`.

## Proofs that differ from Rocq (this part)
* The three copies of the `excl_auth` lemmas share the helpers `excl_auth_alloc`,
  `excl_auth_agree`, `excl_auth_update`.
* `ghost_var_update_frac` uses `iOwn_update_op` with `FracAuth.update` (as iris-lean's
  `HeapLang/Lib/Counter.lean`).
* In `simple_parallel_add_spec`, `replace (2/3) with (/3 + /3)` + `ec_split` is `ErrorCredit.split`
  after `ErrorCredit.ext`; `rewrite bool_decide_eq_true_2` is `rw [decide_eq_true ..]` on the
  evaluated comparison (a `Fin` comparison after `wp_pures`).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par
open Iris.ExclAuth

namespace Coneris.Examples.ParallelAdd

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

/-- Rocq: `bool_to_Z` (stdpp). -/
def bool_to_Z (b : Bool) : ℤ := if b then 1 else 0

/-! ## `ZR`: the CMRA `(ℤ, +)`

Rocq's `ZR` is iris-lean's "constant core" CMRA `CommMonoidLike.instCMRA` at `ℤ`; the instances
are scoped to this namespace. -/

scoped instance : COFE ℤ := COFE.ofDiscrete _
scoped instance : OFE.Discrete ℤ := ⟨fun h => h⟩
scoped instance : Std.LawfulLeftIdentity (α := ℤ) (· + ·) (0 : ℤ) := ⟨Int.zero_add⟩
scoped instance : LeftCancelAdd ℤ := ⟨fun h => Int.add_left_cancel h⟩
scoped instance : CMRA ℤ := CommMonoidLike.instCMRA
scoped instance : UCMRA ℤ := CommMonoidLike.instUCMRA
scoped instance : CMRA.Discrete ℤ := CommMonoidLike.instDiscrete

/-- Rocq: `ZR`. -/
abbrev ZR : Type := ℤ

/-! ## Ghost-state lemmas -/

/-- Rocq: the functor of `inG Σ (excl_authR A)` for a Leibniz `A`. -/
abbrev excl_authF (A : Type) : COFE.OFunctorPre := constOF (ExclAuthR (A := DiscreteO A))

/-- `own γ (●E a)`. -/
abbrev own_auth {GF : BundledGFunctors} {A : Type} [ElemG GF (excl_authF A)] (γ : GName)
    (a : A) : IProp GF :=
  iOwn (F := excl_authF A) γ (●E (⟨a⟩ : DiscreteO A))

/-- `own γ (◯E a)`. -/
abbrev own_frag {GF : BundledGFunctors} {A : Type} [ElemG GF (excl_authF A)] (γ : GName)
    (a : A) : IProp GF :=
  iOwn (F := excl_authF A) γ (◯E (⟨a⟩ : DiscreteO A))

section excl_auth

variable {GF : BundledGFunctors} {A : Type} [ElemG GF (excl_authF A)]

/-- Helper: the common proof of `ghost_var_alloc`, `ghost_var_alloc'`, `ghost_var_allocZ`. -/
theorem excl_auth_alloc (b : A) : ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b := by
  imod iOwn_alloc (F := excl_authF A) ((●E (⟨b⟩ : DiscreteO A)) • (◯E (⟨b⟩ : DiscreteO A)))
    ExclAuth.valid with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Helper: the common proof of `ghost_var_agree`, `ghost_var_agree'`, `ghost_var_agreeZ`. -/
theorem excl_auth_agree (γ : GName) (b c : A) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree H)

/-- Helper: the common proof of `ghost_var_update`, `ghost_var_update'`,
`ghost_var_updateZ`. -/
theorem excl_auth_update (γ : GName) (b' b c : A) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' := by
  iintro H1 H2
  ihave H := (iOwn_op (F := excl_authF A)).2 $$ [H1 H2]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with ⟨H1, H2⟩
  imodintro
  iframe

end excl_auth

section lemmas

variable {GF : BundledGFunctors} [ElemG GF (excl_authF Bool)]

/-- Rocq: `ghost_var_alloc`. -/
theorem ghost_var_alloc (b : Bool) : ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b :=
  excl_auth_alloc b

/-- Rocq: `ghost_var_agree`. -/
theorem ghost_var_agree (γ : GName) (b c : Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ :=
  excl_auth_agree γ b c

/-- Rocq: `ghost_var_update`. -/
theorem ghost_var_update (γ : GName) (b' b c : Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' :=
  excl_auth_update γ b' b c

/-- Rocq: `resource_nonneg` (`Local`). Stated over `ℝ` as in Rocq (`Rpower` is `Real.rpow`);
it is not needed for the `ℝ≥0∞` error credits below. -/
theorem resource_nonneg (b : Bool) :
    (0 : ℝ) ≤ 1 - (2 : ℝ) ^ ((Coneris.Lib.Flip.bool_to_nat b : ℝ) - 1) := by
  cases b
  · simp only [Coneris.Lib.Flip.bool_to_nat, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero,
      zero_sub, Real.rpow_neg_one]
    norm_num
  · simp [Coneris.Lib.Flip.bool_to_nat]

end lemmas

section lemmas'

variable {GF : BundledGFunctors} [ElemG GF (excl_authF (Option Bool))]

/-- Rocq: `ghost_var_alloc'`. -/
theorem ghost_var_alloc' (b : Option Bool) :
    ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b :=
  excl_auth_alloc b

/-- Rocq: `ghost_var_agree'`. -/
theorem ghost_var_agree' (γ : GName) (b c : Option Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ :=
  excl_auth_agree γ b c

/-- Rocq: `ghost_var_update'`. -/
theorem ghost_var_update' (γ : GName) (b' b c : Option Bool) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' :=
  excl_auth_update γ b' b c

end lemmas'

section lemmasZ

variable {GF : BundledGFunctors} [ElemG GF (excl_authF ZR)]

/-- Rocq: `ghost_var_allocZ`. -/
theorem ghost_var_allocZ (b : ZR) : ⊢@{IProp GF} |==> ∃ γ, own_auth γ b ∗ own_frag γ b :=
  excl_auth_alloc b

/-- Rocq: `ghost_var_agreeZ`. -/
theorem ghost_var_agreeZ (γ : GName) (b c : ZR) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c -∗ ⌜b = c⌝ :=
  excl_auth_agree γ b c

/-- Rocq: `ghost_var_updateZ`. -/
theorem ghost_var_updateZ (γ : GName) (b' b c : ZR) :
    ⊢@{IProp GF} own_auth γ b -∗ own_frag γ c ==∗ own_auth γ b' ∗ own_frag γ b' :=
  excl_auth_update γ b' b c

end lemmasZ

/-- Rocq: the functor of `inG Σ (frac_authR ZR)`. -/
abbrev frac_authF : COFE.OFunctorPre := constOF (FracAuth (A := ZR))

/-- `own γ (●F z)`. -/
abbrev own_authF {GF : BundledGFunctors} [ElemG GF frac_authF] (γ : GName) (z : ZR) :
    IProp GF :=
  iOwn (F := frac_authF) γ (●F z)

/-- `own γ (◯F{q} z)`. -/
abbrev own_fragF {GF : BundledGFunctors} [ElemG GF frac_authF] (γ : GName) (q : Qp) (z : ZR) :
    IProp GF :=
  iOwn (F := frac_authF) γ (◯F{q} z)

section lemmasfrac

variable {GF : BundledGFunctors} [ElemG GF frac_authF]

/-- Rocq: `ghost_var_alloc_frac`. -/
theorem ghost_var_alloc_frac (b : ZR) :
    ⊢@{IProp GF} |==> ∃ γ, own_authF γ b ∗ own_fragF γ 1 b := by
  imod iOwn_alloc (F := frac_authF) ((●F b : FracAuth (A := ZR)) • (◯F b))
    (FracAuth.valid trivial) with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Rocq: `ghost_var_agree_frac`. -/
theorem ghost_var_agree_frac (γ : GName) (b c : ZR) :
    ⊢@{IProp GF} own_authF γ b -∗ own_fragF γ 1 c -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact FracAuth.agree H

/-- Rocq: `ghost_var_update_frac`. -/
theorem ghost_var_update_frac (γ : GName) (b' b c : ZR) (q : Qp) :
    ⊢@{IProp GF} own_authF γ b -∗ own_fragF γ q c ==∗
      own_authF γ (b + b') ∗ own_fragF γ q (c + b') := by
  iintro H1 H2
  imod iOwn_update_op (F := frac_authF)
    (a' := CMRA.op (●F (b + b') : FracAuth (A := ZR)) (◯F{q} (c + b'))) $$ [$H1 $H2]
    with ⟨H1, H2⟩
  · exact FracAuth.update (CommMonoidLike.leftCancelAdd_local_update
      (show (b : ℤ) + (c + b') = (b + b') + c by rw [Int.add_comm c b', Int.add_assoc]))
  imodintro
  iframe

end lemmasfrac

/-! ## Section `simple_parallel_add` -/

section simple_parallel_add

/-- Rocq: `simple_parallel_add`. -/
def simple_parallel_add : expr := cpl(
  let r := ref(#0) in
  ((if #0 < rand(#2) then faa(r, #1) else #())
   ‖
   (if #0 < rand(#2) then faa(r, #1) else #()));
  !r)

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [ElemG GF (excl_authF Bool)]

/-- Rocq: `simple_parallel_add_inv`. -/
def simple_parallel_add_inv (l : Loc) (γ1 γ2 : GName) : IProp GF :=
  iprop(∃ (b1 b2 : Bool) (z : ℤ),
    own_auth γ1 b1 ∗ own_auth γ2 b2 ∗ l ↦ LitV (LitInt z) ∗
    ⌜z = bool_to_Z b1 + bool_to_Z b2⌝)

/-- Rocq: `simple_parallel_add_spec`. Simple spec, where the error is directly distributed. -/
theorem simple_parallel_add_spec :
    {{ ↯ (2 / 3) }} simple_parallel_add
    {{ (z : ℤ), RET LitV (LitInt z); (⌜z = 2⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold simple_parallel_add
  wp_alloc l as Hl
  wp_pures
  imod ghost_var_alloc false with ⟨%γ1, Hγ1a, Hγ1f⟩
  imod ghost_var_alloc false with ⟨%γ2, Hγ2a, Hγ2f⟩
  imod inv_alloc nroot ⊤ (simple_parallel_add_inv l γ1 γ2) $$ [Hl Hγ1a Hγ2a] with #I
  · inext
    unfold simple_parallel_add_inv
    iexists false, false, 0
    iframe
    ipureintro
    rfl
  ihave ⟨Herr1, Herr2⟩ := ErrorCredit.split (ε₁ := 3⁻¹) (ε₂ := 3⁻¹) $$ [Herr]
  · iapply ErrorCredit.ext _ $$ Herr
    rw [← two_mul, ENNReal.div_eq_inv_mul, mul_comm]
  unfold simple_parallel_add_inv
  wp_apply wp_par' (fun _ => own_frag γ1 true) (fun _ => own_frag γ2 true)
    $$ [Herr1 Hγ1f] [Herr2 Hγ2f]
  · wp_apply wp_rand_err_nat 2 2 0 rfl
    isplitl [Herr1]
    · iapply ErrorCredit.ext _ $$ Herr1
      norm_num
    iintro %x %Hx
    wp_pures
    rw [decide_eq_true (Fin.lt_def.2 (by simp only [Fin.val_zero]; omega) : (0 : Fin (2 + 1)) < x)]
    wp_pures
    iinv I with ⟨%b1, %b2, %z, >Hγ1a, >Hγ2a, >Hl, >%Hz⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hγ1a Hγ1f
    subst Heq
    wp_faa
    imod ghost_var_update γ1 true _ _ $$ Hγ1a Hγ1f with ⟨Hγ1a, Hγ1f⟩
    imod Hclose $$ [Hγ1a Hγ2a Hl]
    · inext
      iexists true, b2, z + 1
      iframe
      ipureintro
      simp only [bool_to_Z] at Hz ⊢
      simp at Hz ⊢
      omega
    imodintro
    iexact Hγ1f
  · wp_apply wp_rand_err_nat 2 2 0 rfl
    isplitl [Herr2]
    · iapply ErrorCredit.ext _ $$ Herr2
      norm_num
    iintro %x %Hx
    wp_pures
    rw [decide_eq_true (Fin.lt_def.2 (by simp only [Fin.val_zero]; omega) : (0 : Fin (2 + 1)) < x)]
    wp_pures
    iinv I with ⟨%b1, %b2, %z, >Hγ1a, >Hγ2a, >Hl, >%Hz⟩ Hclose
    ihave %Heq := ghost_var_agree $$ Hγ2a Hγ2f
    subst Heq
    wp_faa
    imod ghost_var_update γ2 true _ _ $$ Hγ2a Hγ2f with ⟨Hγ2a, Hγ2f⟩
    imod Hclose $$ [Hγ1a Hγ2a Hl]
    · inext
      iexists b1, true, z + 1
      iframe
      ipureintro
      simp only [bool_to_Z] at Hz ⊢
      simp at Hz ⊢
      omega
    imodintro
    iexact Hγ2f
  · iintro %v1 %v2 ⟨Hγ1f, Hγ2f⟩
    inext
    wp_pures
    iinv I with ⟨%b1, %b2, %z, >Hγ1a, >Hγ2a, >Hl, >%Hz⟩ Hclose
    ihave %Heq1 := ghost_var_agree $$ Hγ1a Hγ1f
    ihave %Heq2 := ghost_var_agree $$ Hγ2a Hγ2f
    subst Heq1 Heq2
    wp_load
    imod Hclose $$ [Hγ1a Hγ2a Hl]
    · inext
      iexists true, true, z
      iframe
      ipureintro
      exact Hz
    imodintro
    iapply HΦ
    ipureintro
    simpa [bool_to_Z] using Hz

end simple_parallel_add

end Coneris.Examples.ParallelAdd
