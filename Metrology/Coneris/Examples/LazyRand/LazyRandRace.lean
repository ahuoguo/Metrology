module

public import Metrology.Coneris.Examples.LazyRand.LazyRandInterface
public import Metrology.Coneris.Lib.Par
public import Iris.Algebra.Lib.ExclAuth

/-!
# A race on a lazily sampled random value

Ported from clutch/theories/coneris/examples/lazy_rand/lazy_rand_race.v

## Rocq → Lean mapping
* Section `lemmas`: the context `inG Σ (excl_authR boolO)` is `[ElemG GF excl_authTF]` with
  `excl_authTF := constOF (ExclAuthR (A := boolO))` and `boolO := DiscreteO Bool` (Rocq:
  `leibnizO bool`). `own γ (●E b)` is `iOwn (F := excl_authTF) γ (●E ⟨b⟩)`. `ghost_var_alloc`,
  `ghost_var_agree`, `ghost_var_update`: same names; `P -∗ Q ==∗ R` is `⊢ P -∗ Q ==∗ R`.
* Section `race`: the context `c : lazy_rand 1` is `[c : lazy_rand 1 GF]`; `race_prog`,
  `race_prog_spec`: same names.
* The expression-scope `e1 ||| e2` of `race_prog` (Rocq: `par (λ: <>, e1)%E (λ: <>, e2)%E`) is
  the local program notation `e1 ‖ e2` (inside `cpl(...)`, `|||` is the bitwise `or`); after
  the pure steps it is the value-scope form of `wp_par` (the helper `wp_par'`), as in Rocq.
* `nroot.@"1"` is `nroot.@"1"`; `subseteq_difference_r` + `ndot_ne_disjoint` is the helper
  `ndot_subseteq_top_diff`.
* Errors are `ℝ≥0∞`: the side condition `∀ x, 0 <= ε2 x` of `rand_tape_presample` is
  dropped (it is not a field of `lazy_rand` in Lean); `ec_contradict` is
  `ErrorCredit.contradict`; `SeriesC_finite_foldr` + `lra` is `tsum_fintype` +
  `Fin.sum_univ_two` + `norm_num`.
* `RET ((#n,#n),(#n,#n))%Z` is `RET cpl_val(((#n, #n), (#n, #n)))`.

## Proofs that differ from Rocq
The two threads of `race_prog_spec` have literally the same Rocq proof, up to the thread id
`0`/`1`; here it is proved once, for any thread id `tid ≤ 1`, in the helper `race_thread_spec`.
The Rocq `iDestruct (rand_auth_duplicate with "[$]") as "#?"` keeps `rand_auth` (the
conclusion is persistent); here this is the helper `rand_auth_duplicate'`.

## Added
* Helpers `boolO`, `excl_authTF`, `wp_par'`, `ndot_subseteq_top_diff`, `rand_auth_duplicate'`,
  `race_P` (the lambda passed to `lazy_rand_init`/`lazy_rand_spec` in Rocq, named so that its
  `Timeless` instance is found), `race_inv` (the invariant `Hinv2`), `race_thread_spec`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par Coneris.Examples.LazyRand.LazyRandInterface
open Iris.ExclAuth

namespace Coneris.Examples.LazyRand.LazyRandRace

/-- Rocq: `boolO` (`leibnizO bool`). -/
abbrev boolO : Type := DiscreteO Bool

/-- Rocq: the functor of `inG Σ (excl_authR boolO)`. -/
abbrev excl_authTF : COFE.OFunctorPre := constOF (ExclAuthR (A := boolO))

section lemmas

variable {GF : BundledGFunctors} [ElemG GF excl_authTF]

/-- Rocq: `ghost_var_alloc`. -/
theorem ghost_var_alloc (b : Bool) :
    ⊢@{IProp GF} |==> ∃ γ, iOwn (F := excl_authTF) γ (●E (⟨b⟩ : boolO)) ∗
      iOwn (F := excl_authTF) γ (◯E (⟨b⟩ : boolO)) := by
  imod iOwn_alloc (F := excl_authTF) ((●E (⟨b⟩ : boolO)) • (◯E (⟨b⟩ : boolO))) ExclAuth.valid
    with ⟨%γ, H1, H2⟩
  imodintro
  iexists γ
  iframe

/-- Rocq: `ghost_var_agree`. -/
theorem ghost_var_agree (γ : GName) (b c : Bool) :
    ⊢@{IProp GF} iOwn (F := excl_authTF) γ (●E (⟨b⟩ : boolO)) -∗
      iOwn (F := excl_authTF) γ (◯E (⟨c⟩ : boolO)) -∗ ⌜b = c⌝ := by
  iintro H1 H2
  icombine H1 H2 gives %H
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree H)

/-- Rocq: `ghost_var_update`. -/
theorem ghost_var_update (γ : GName) (b' b c : Bool) :
    ⊢@{IProp GF} iOwn (F := excl_authTF) γ (●E (⟨b⟩ : boolO)) -∗
      iOwn (F := excl_authTF) γ (◯E (⟨c⟩ : boolO)) ==∗
      iOwn (F := excl_authTF) γ (●E (⟨b'⟩ : boolO)) ∗
        iOwn (F := excl_authTF) γ (◯E (⟨b'⟩ : boolO)) := by
  iintro H1 H2
  ihave H := (iOwn_op (F := excl_authTF)).2 $$ [H1 H2]
  · iframe
  imod iOwn_update ExclAuth.update $$ H with ⟨H1, H2⟩
  imodintro
  iframe

end lemmas

/-! ## The race -/

/-- `e1 ‖ e2` (Rocq: `e1 ||| e2` in `expr_scope`, i.e. `par (λ: <>, e1)%E (λ: <>, e2)%E`) as a
program notation. -/
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

/-- Helper (Rocq: `subseteq_difference_r` + `ndot_ne_disjoint`). -/
theorem ndot_subseteq_top_diff :
    (↑(nroot.@"1") : CoPset) ⊆ ⊤ \ (↑(nroot.@"inv") : CoPset) := fun x hx =>
  CoPset.in_diff.mpr ⟨CoPset.mem_full, fun hx0 =>
    ndot_ne_disjoint nroot (show ("inv" : String) ≠ "1" by decide) x ⟨hx0, hx⟩⟩

section race

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [c : lazy_rand 1 GF]
  [ElemG GF excl_authTF]

/-- Helper: the Rocq `iDestruct (rand_auth_duplicate with "[$]") as "#?"`, which keeps
`rand_auth` since the conclusion is persistent. -/
theorem rand_auth_duplicate' (n : ℕ × ℕ) (γ : c.rand_view_gname) :
    c.rand_auth (some n) γ ⊢ c.rand_auth (some n) γ ∗ c.rand_frag n.1 n.2 γ :=
  persistent_entails_left (wand_entails (c.rand_auth_duplicate n γ))

/-- Rocq: `race_prog`. -/
def race_prog : expr := cpl(
  let r := v(&c.init_lazy_rand) #() in
  (v(&c.lazy_read_rand) r (v(&c.allocate_tape) #()) #0)
  ‖
  (v(&c.lazy_read_rand) r (v(&c.allocate_tape) #()) #1))

/-- Helper: the predicate `P` of the lazy rand invariant in `race_prog_spec`. -/
def race_P (γ : GName) (x : Option (ℕ × ℕ)) : IProp GF :=
  iprop((⌜x = none⌝ ∗ iOwn (F := excl_authTF) γ (◯E (⟨false⟩ : boolO))) ∨
    ∃ x1 : ℕ, ⌜x = some (x1, x1)⌝ ∗ iOwn (F := excl_authTF) γ (◯E (⟨true⟩ : boolO)))

instance race_P_timeless (γ : GName) (x : Option (ℕ × ℕ)) :
    Timeless (race_P (GF := GF) γ x) := by
  unfold race_P; infer_instance

/-- Helper: the invariant `Hinv2` of `race_prog_spec`. -/
def race_inv (γ : GName) : IProp GF :=
  iprop((iOwn (F := excl_authTF) γ (●E (⟨false⟩ : boolO)) ∗ ↯ (1 / 2)) ∨
    iOwn (F := excl_authTF) γ (●E (⟨true⟩ : boolO)))

/-- Helper: the proof of either thread of `race_prog_spec` (Rocq: the first two bullets). -/
theorem race_thread_spec (tid : ℕ) (Htid : tid ≤ 1) (cv : val) (γ : GName)
    (γ_tape : c.rand_tape_gname) (γ_view : c.rand_view_gname) (γ_lock : c.rand_lock_gname) :
    ⊢ c.rand_inv (nroot.@"1") cv (race_P γ) γ_tape γ_view γ_lock -∗
      inv (nroot.@"inv") (race_inv γ) -∗
      WP cpl(v(&c.lazy_read_rand) v(&cv) (v(&c.allocate_tape) #()) #tid)
        {{ res, ∃ n : ℕ, ⌜cpl_val((#n, #n)) = res⌝ ∗ c.rand_frag n n γ_view }} := by
  iintro #Hinv #Hinv2
  wp_apply c.lazy_rand_alloc_tape (nroot.@"1") cv (race_P γ) γ_tape γ_view γ_lock $$ Hinv
    with %α Ht
  wp_apply c.lazy_rand_spec (nroot.@"1") cv (race_P γ) γ_tape γ_view γ_lock
    (fun x y => iprop(⌜x = y⌝ ∗ c.rand_frag x x γ_view))
    (fun x y => iprop(⌜x = y⌝ ∗ c.rand_frag x x γ_view)) α tid $$ [Ht]
    with %res' %tid' HQ
  · isplitr
    · iexact Hinv
    iintro %n H1 Hauth
    iapply state_update_inv_acc _ ⊤ _ (nroot.@"inv") CoPset.subseteq_top $$ Hinv2
    iunfold race_P at H1
    unfold race_inv
    iintro >(⟨H2, Herr⟩ | H2)
    · icases H1 with (⟨%Hn, Hf⟩ | ⟨%x1, %Hn, Hf⟩)
      · subst Hn
        imod c.rand_tape_presample (nroot.@"1") cv (race_P γ) γ_tape γ_view γ_lock _ α (1 / 2)
          (fun x => if (x : ℕ) = tid then 0 else 1) ndot_subseteq_top_diff ?_ $$ Hinv Ht Herr
          with ⟨%n, Herr, Ht⟩
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 Htid with rfl | rfl <;>
            simp [tsum_fintype, Fin.sum_univ_two, one_add_one_eq_two]
        by_cases hn : (n : ℕ) = tid
        · simp only [hn, ↓reduceIte]
          subst hn
          imod ghost_var_update γ true false false $$ H2 Hf with ⟨H1, H2⟩
          imodintro
          isplitl [Ht Hauth H2]
          · iexists (n : ℕ)
            iframe Ht
            iintro _Ht
            imod c.rand_auth_update ((n : ℕ), (n : ℕ)) γ_view (by have := n.isLt; simp; omega)
              $$ Hauth with Hauth
            ihave ⟨Hauth, #Hfr⟩ := rand_auth_duplicate' ((n : ℕ), (n : ℕ)) γ_view $$ Hauth
            imodintro
            iframe Hauth Hfr
            isplitl
            · unfold race_P
              iright
              iexists (n : ℕ)
              iframe H2
              ipureintro
              rfl
            · ipureintro
              rfl
          · inext
            iright
            iexact H1
        · simp only [hn, ↓reduceIte]
          iexfalso
          iapply ErrorCredit.contradict le_rfl $$ Herr
      · ihave %H := ghost_var_agree $$ H2 Hf
        simp at H
    · icases H1 with (⟨%Hn, Hf⟩ | ⟨%x1, %Hn, Hf⟩)
      · ihave %H := ghost_var_agree $$ H2 Hf
        simp at H
      · subst Hn
        ihave ⟨Hauth, #Hfr⟩ := rand_auth_duplicate' (x1, x1) γ_view $$ Hauth
        imodintro
        dsimp only
        iframe Hauth Hfr
        isplitl [Hf]
        · isplitl
          · unfold race_P
            iright
            iexists x1
            iframe Hf
            ipureintro
            rfl
          · ipureintro
            rfl
        · inext
          iright
          iexact H2
  · icases HQ with (⟨%Heq, #H⟩ | ⟨%Heq, #H⟩) <;> subst Heq <;> iexists res' <;> iframe H <;>
      ipureintro <;> rfl

/-- Rocq: `race_prog_spec`. -/
theorem race_prog_spec :
    {{ ↯ (1 / 2) }} (race_prog (GF := GF))
    {{ (n : ℕ), RET cpl_val(((#n, #n), (#n, #n))); (⌜n ≤ 1⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold race_prog
  imod ghost_var_alloc false with ⟨%γ, Hauth, Hfrag⟩
  wp_apply c.lazy_rand_init (nroot.@"1") (race_P γ) $$ [Hfrag]
    with %cv ⟨%γ_tape, %γ_view, %γ_lock, #Hinv⟩
  · unfold race_P
    ileft
    iframe Hfrag
    ipureintro
    rfl
  imod inv_alloc (nroot.@"inv") ⊤ (race_inv γ) $$ [Herr Hauth] with #Hinv2
  · inext
    unfold race_inv
    ileft
    iframe
  wp_pures
  wp_apply wp_par'
    (fun res => iprop(∃ n : ℕ, ⌜cpl_val((#n, #n)) = res⌝ ∗ c.rand_frag n n γ_view))
    (fun res => iprop(∃ n : ℕ, ⌜cpl_val((#n, #n)) = res⌝ ∗ c.rand_frag n n γ_view))
    $$ [] []
  · iapply race_thread_spec 0 (by omega) cv γ γ_tape γ_view γ_lock $$ Hinv Hinv2
  · iapply race_thread_spec 1 le_rfl cv γ γ_tape γ_view γ_lock $$ Hinv Hinv2
  iintro %v1 %v2 ⟨⟨%n1, %H1, #Hf1⟩, ⟨%n2, %H2, #Hf2⟩⟩
  subst H1 H2
  ihave %Heq := c.rand_frag_frag_agree n1 n2 n1 n2 γ_view $$ Hf1 Hf2
  obtain ⟨rfl, -⟩ := Heq
  ihave %Hle := c.rand_frag_valid n1 n1 γ_view $$ Hf1
  iapply HΦ
  inext
  ipureintro
  exact Hle

end race

end Coneris.Examples.LazyRand.LazyRandRace
