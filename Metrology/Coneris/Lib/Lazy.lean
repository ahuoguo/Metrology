module

public import Metrology.Coneris.Lib.Flip
public import Metrology.Coneris.Lib.Par

/-!
# Library for lazy sampling

Ported from clutch/theories/coneris/lib/lazy.v

## Rocq → Lean mapping
* `new_lazyrand`, `read_lazyrand` (Rocq `expr`s), `is_lazyrand`, `new_lazyrand_spec`,
  `read_lazyrand_old_spec`, `read_lazyrand_fresh_spec`, `foo`, `foo_inv`, `foo_spec`: same
  names. Programs are transcribed with the `cpl` notation: `ref NONEV` is `ref(v(none()))`,
  `let, ("r", "N") := "c" in ..` is `let (r, N) := c; ..`, `match: .. with NONE => .. | SOME "n"
  => .. end` is `match .. with | none() => .. | some(n) => ..`, and `e1 ||| e2` (expression
  scope) is `par_E e1 e2` from `Coneris.Lib.Par`.
* `(#l, #N)%V` is `PairV (LitV (LitLoc l)) (LitV (LitInt N))`; `option nat` is `Option ℕ`.
* `read_lazyrand_fresh_spec`: `ε : nonnegreal`, `F : fin (S N) → nonnegreal` are `ℝ≥0∞`;
  `SeriesC (λ n, 1 / S N * F n) = ε` is `∑' n, 1 / ((N : ℝ≥0∞) + 1) * F n = ε`.
* `foo_spec`: `nnreal_half`, `nnreal_one`, `nnreal_zero` are `1 / 2`, `1`, `0`; the invariant is
  allocated at `nroot` with `inv_alloc`; `spawnG Σ` is `[spawnG GF]`.

## Proofs that differ from Rocq
* The substitutions into the closed programs `new_lazyrand`/`read_lazyrand` (Rocq: `simpl` and
  folding `read_lazyrand` back with `rewrite`) are computed by the helpers `subst_new_lazyrand`,
  `subst_read_lazyrand`.
* `foo_spec` applies `par_spec` (Rocq: `wp_par`) directly, since after `wp_pures` the thunks of
  `par_E` are closures and the goal is `par f1 f2` in constructor form. The case split on the
  sample (`inv_fin`) is `fin_cases`; the impossible branch uses `ErrorCredit.contradict`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Lib.Flip

namespace Coneris.Lib.Lazy

/-! ## A lazy rand -/

/-- Rocq: `new_lazyrand`. -/
def new_lazyrand : expr := cpl(
  λ N,
    (ref(v(none())), N))

/-- Rocq: `read_lazyrand`. -/
def read_lazyrand : expr := cpl(
  λ c,
    let (r, N) := c;
    match !r with
    | none() => let n := rand(N);
                r <- some(n);
                n
    | some(n) => n)

section defs

variable {GF : BundledGFunctors} [conerisGS GF]

/-- Rocq: `is_lazyrand`. -/
def is_lazyrand (v : val) (N : ℕ) (n : Option ℕ) : IProp GF :=
  iprop(∃ l : Loc, ⌜v = PairV (LitV (LitLoc l)) (LitV (LitInt (N : ℤ)))⌝ ∗
    (match n with
     | none => l ↦ NONEV
     | some m => l ↦ SOMEV (LitV (LitInt (m : ℤ)))))

/-- Rocq: `new_lazyrand_spec`. -/
theorem new_lazyrand_spec (N : ℕ) :
    {{ True }} cpl(&new_lazyrand #N) {{ v, RET v; is_lazyrand (GF := GF) v N none }} := by
  iintro %Φ - HΦ
  unfold new_lazyrand
  wp_pures
  wp_alloc l as Hl
  wp_pures
  iapply HΦ
  unfold is_lazyrand
  iexists l
  iframe Hl
  ipureintro
  rfl

/-- Rocq: `read_lazyrand_old_spec`. -/
theorem read_lazyrand_old_spec (v : val) (N m : ℕ) :
    {{ is_lazyrand v N (some m) }} cpl(&read_lazyrand v(&v))
    {{ n, RET n; ⌜n = LitV (LitInt (m : ℤ))⌝ ∗ is_lazyrand (GF := GF) v N (some m) }} := by
  unfold read_lazyrand is_lazyrand
  iintro %Φ ⟨%l, %Hv, Hl⟩ HΦ
  subst Hv
  wp_pures
  wp_load
  wp_pures
  iapply HΦ
  isplitr
  · ipureintro
    rfl
  iexists l
  iframe Hl
  ipureintro
  rfl

/-- Rocq: `read_lazyrand_fresh_spec`. -/
theorem read_lazyrand_fresh_spec (v : val) (N : ℕ) (ε : ℝ≥0∞) (F : Fin (N + 1) → ℝ≥0∞)
    (Hf : ∑' n : Fin (N + 1), 1 / ((N : ℝ≥0∞) + 1) * F n = ε) :
    {{ is_lazyrand v N none ∗ ↯ ε }} cpl(&read_lazyrand v(&v))
    {{ (n : Fin (N + 1)), RET LitV (LitInt ((n : ℕ) : ℤ));
      ∃ m : ℕ, ⌜(n : ℕ) = m⌝ ∗ is_lazyrand (GF := GF) v N (some m) ∗ ↯ (F n) }} := by
  unfold read_lazyrand is_lazyrand
  iintro %Φ ⟨⟨%l, %Hv, Hl⟩, Herr⟩ HΦ
  subst Hv
  wp_pures
  wp_load
  wp_pures
  wp_apply wp_couple_rand_adv_comp1 N (N : ℤ) ε F (by simp) Hf $$ Herr with %n Herr
  wp_pures
  wp_store
  imodintro
  iapply HΦ
  iexists (n : ℕ)
  isplitr
  · ipureintro
    rfl
  iframe Herr
  iexists l
  iframe Hl
  ipureintro
  rfl

end defs


/-! ## Applications -/

/-- Rocq: `foo`. -/
def foo : expr := cpl(
  let r := ref(#0);
  &(par_E
    cpl(let x := &new_lazyrand #1;
        let y := !r;
        if (&read_lazyrand x ≠ y) then #() else #() #())
    cpl(r <- #1)))

section applications

/-- Helper: `new_lazyrand` is closed (Rocq's `simpl` computes the substitution). -/
theorem subst_new_lazyrand (x : String) (w : val) : subst x w new_lazyrand = new_lazyrand := by
  unfold new_lazyrand
  by_cases h : x = "N" <;> simp [subst, h]

/-- Helper: `read_lazyrand` is closed (Rocq's `simpl` computes the substitution). -/
theorem subst_read_lazyrand (x : String) (w : val) :
    subst x w read_lazyrand = read_lazyrand := by
  unfold read_lazyrand
  by_cases h : x = "c"
  · simp [subst, h]
  · simp [subst, h]
    tauto

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]

/-- Rocq: `foo_inv`. -/
def foo_inv (l : Loc) : IProp GF :=
  iprop(l ↦ LitV (LitInt 0) ∨ l ↦ LitV (LitInt 1))

/-- Rocq: `foo_spec`. -/
theorem foo_spec :
    {{ ↯ (1 / 2) }} foo {{ v, RET v; (True : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold foo par_E
  wp_alloc r as Hr
  wp_pures
  rw [subst_new_lazyrand, subst_read_lazyrand]
  imod inv_alloc nroot ⊤ (foo_inv r) $$ [Hr] with #I
  · inext
    unfold foo_inv
    ileft
    iexact Hr
  iapply par_spec (fun _ => emp) (fun _ => emp) $$ [Herr] [] [HΦ]
  · wp_lam
    wp_apply new_lazyrand_spec 1 $$ [] with %v Hv
    · itrivial
    wp_pures
    rw [subst_read_lazyrand]
    wp_bind (Load _)
    iinv I with G
    unfold foo_inv
    icases G with (Hr0 | Hr1)
    · wp_load
      imodintro
      isplitl [Hr0]
      · inext
        ileft
        iexact Hr0
      wp_pure
      wp_pure
      rw [subst_read_lazyrand]
      wp_bind (App read_lazyrand _)
      wp_apply read_lazyrand_fresh_spec v 1 (1 / 2) (fun x => if (x : ℕ) = 0 then 1 else 0)
        (by rw [flip_SeriesC_unif]; norm_num) $$ [Hv Herr] with %n ⟨%m, %Hm, Hv, Herr⟩
      · iframe
      fin_cases n
      · iexfalso
        iapply ErrorCredit.contradict (by simp) $$ Herr
      · wp_pures
        iclear Hv Herr
        imodintro
        iempintro
    · wp_load
      imodintro
      isplitl [Hr1]
      · inext
        iright
        iexact Hr1
      wp_pure
      wp_pure
      rw [subst_read_lazyrand]
      wp_bind (App read_lazyrand _)
      wp_apply read_lazyrand_fresh_spec v 1 (1 / 2) (fun x => if (x : ℕ) = 1 then 1 else 0)
        (by rw [flip_SeriesC_unif]; norm_num) $$ [Hv Herr] with %n ⟨%m, %Hm, Hv, Herr⟩
      · iframe
      fin_cases n
      · wp_pures
        iclear Hv Herr
        imodintro
        iempintro
      · iexfalso
        iapply ErrorCredit.contradict (by simp) $$ Herr
  · wp_lam
    iinv I with G
    unfold foo_inv
    icases G with (Hr | Hr)
    · wp_store
      imodintro
      isplitl
      · inext
        iright
        iexact Hr
      · iempintro
    · wp_store
      imodintro
      isplitl
      · inext
        iright
        iexact Hr
      · iempintro
  · iintro !> %v1 %v2 - !>
    iapply HΦ
    itrivial

end applications

end Coneris.Lib.Lazy
