module

public import Metrology.Coneris.Lib.HocapRandAlt
public import Metrology.Coneris.Lib.HocapRandAtomicPart2

/-!
# An alternative hocap rand spec, part 3: the rejection sampler

Ported from clutch/theories/coneris/lib/hocap_rand_alt.v (section `impl3`).

## Rocq → Lean mapping
* `rand_inv_pred3`, `is_rand3`, `rand_tapes3`, `rand_token3`, `rand_spec3` (Rocq:
  `#[local] Program Definition`, a definition here); the `Next Obligation`s are the helper
  theorems `rand_spec3_*`. `filter (λ x, x <= tb) ns'` is
  `ns'.filter (fun x => decide (x ≤ tb))`.
* `rand_inv_pred3 γ` is `rand_inv_pred_gen (tb + 1) γ` (see `Coneris.Lib.HocapRandAlt`).
* The presampling obligation is the same amplification argument (`ec_ind_amp`, iris-lean's
  `ErrorCredit.Induction.amplifying`, with `k = S (S tb)`) as in
  `Coneris.Lib.HocapRandAtomicPart2`, whose pure helpers `rej_err` and `rej_err_sum` (the Rocq
  error function and series manipulation, identical in both Rocq files) are reused.

## Proofs that differ from Rocq
* `rand_tape_spec_some`: Rocq first opens the invariant to learn that `α` is a label; here the
  step `rand(α) #(S tb)` is the helper `rand_inv_gen_rand`, which does this itself.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris.Lib.AbstractTape Coneris.Lib.HocapRandAtomic

namespace Coneris.Lib.HocapRandAlt

section impl3

variable {GF : BundledGFunctors} [conerisGS GF] [GhostMapG GF val Unit val_map]
  [abstract_tapesGS GF] (tb : ℕ)

/-- Rocq: `rand_inv_pred3`. -/
def rand_inv_pred3 (γ : GName × GName) : IProp GF := rand_inv_pred_gen (tb + 1) γ

/-- Rocq: `is_rand3`. -/
def is_rand3 (N : Namespace) (γ : GName × GName) : IProp GF := inv N (rand_inv_pred3 tb γ)

/-- Rocq: `rand_tapes3`. -/
def rand_tapes3 (α : val) (ns : List ℕ) (γ : GName × GName) : IProp GF :=
  iprop((∃ ns' : List ℕ, ⌜ns'.filter (fun x => decide (x ≤ tb)) = ns⌝ ∗
      (α ◯↪N (tb + 1; ns') @ γ.2)) ∗
    ⌜∀ x ∈ ns, x ≤ tb⌝)

/-- Rocq: `rand_token3`. -/
def rand_token3 (α : val) (γ : GName × GName) : IProp GF :=
  ghost_map_elem (H := val_map) γ.1 (DFrac.own 1) α ()

/-- Rocq: `rand_allocate_tape` of `rand_spec3`. -/
def rand_allocate_tape3 : val := cpl_val(λ <>, alloc(#((tb + 1 : ℕ))))

/-- Rocq: `rand_tape` of `rand_spec3`. -/
def rand_tape3 : val :=
  cpl_val(rec f α := let res := rand(α) #((tb + 1 : ℕ)); if res ≤ #tb then res else f α)

instance is_rand3_persistent (N : Namespace) (γ : GName × GName) :
    Persistent (is_rand3 (GF := GF) tb N γ) := by
  unfold is_rand3; infer_instance

instance rand_tapes3_timeless (α : val) (ns : List ℕ) (γ : GName × GName) :
    Timeless (rand_tapes3 (GF := GF) tb α ns γ) := by
  unfold rand_tapes3; infer_instance

instance rand_token3_timeless (α : val) (γ : GName × GName) :
    Timeless (rand_token3 (GF := GF) α γ) := by
  unfold rand_token3; infer_instance

omit [conerisGS GF] [GhostMapG GF val Unit val_map] in
/-- Rocq: first `Next Obligation` of `rand_spec3`. -/
theorem rand_spec3_rand_tapes_exclusive (α : val) (ns ns' : List ℕ) (γ : GName × GName) :
    ⊢@{IProp GF} rand_tapes3 tb α ns γ -∗ rand_tapes3 tb α ns' γ -∗ False := by
  unfold rand_tapes3
  iintro ⟨⟨%l1, -, H1⟩, -⟩ ⟨⟨%l2, -, H2⟩, -⟩
  iapply abstract_tapes_frag_exclusive $$ H1 H2

omit [conerisGS GF] [abstract_tapesGS GF] in
/-- Rocq: second `Next Obligation` of `rand_spec3`. -/
theorem rand_spec3_rand_token_exclusive (α : val) (γ : GName × GName) :
    ⊢@{IProp GF} rand_token3 α γ -∗ rand_token3 α γ -∗ False :=
  rand_token_gen_exclusive α γ.1

omit [conerisGS GF] [GhostMapG GF val Unit val_map] in
/-- Rocq: third `Next Obligation` of `rand_spec3`. -/
theorem rand_spec3_rand_tapes_valid (α : val) (ns : List ℕ) (γ : GName × GName) :
    ⊢@{IProp GF} rand_tapes3 tb α ns γ -∗ ⌜∀ n ∈ ns, n ≤ tb⌝ := by
  unfold rand_tapes3
  iintro ⟨-, %H⟩
  ipureintro
  exact H

/-- Rocq: fourth `Next Obligation` of `rand_spec3`. -/
theorem rand_spec3_rand_tapes_presample (N : Namespace) (E : CoPset) (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (tb + 1) → ℝ≥0∞) (γ : GName × GName) (HN : ↑N ⊆ E)
    (Hsum : ∑' n, 1 / ((tb : ℝ≥0∞) + 1) * ε2 n ≤ ε) :
    ⊢@{IProp GF} is_rand3 tb N γ -∗ rand_tapes3 tb α ns γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes3 tb α (ns ++ [(n : ℕ)]) γ) := by
  unfold is_rand3 rand_inv_pred3
  iintro #Hinv H1 Herr
  iunfold rand_tapes3 at H1
  icases H1 with ⟨H1, %Hf⟩
  imod state_update_epsilon_err E with ⟨%ep, %Hep, Heps⟩
  have hk : (1 : NNReal) < (tb : NNReal) + 2 := by
    have : (0 : NNReal) ≤ tb := by positivity
    exact lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left this)
  iapply ErrorCredit.Induction.amplifying (P := iprop((∃ ns' : List ℕ,
      ⌜ns'.filter (fun x => decide (x ≤ tb)) = ns⌝ ∗ (α ◯↪N (tb + 1; ns') @ γ.2)) -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (tb + 1), ↯ (ε2 n) ∗ rand_tapes3 tb α (ns ++ [(n : ℕ)]) γ)))
    Hep hk $$ [] Heps H1 Herr
  iintro !> %eps %_ #IH Heps ⟨%ls, %Hfilter, Hfrag⟩ Herr
  icombine Herr Heps as Herr'
  imod rand_inv_gen_presample (tb + 1) N E α ls (ε + eps)
      (rej_err tb ε2 (ε + ((tb : ℝ≥0∞) + 2) * eps)) γ HN (rej_err_sum tb ε ε2 Hsum eps)
      $$ Hinv Hfrag Herr' with ⟨%x, Herr, Hfrag⟩
  by_cases hx : (x : ℕ) < tb + 1
  · -- accept
    ihave Herr := ErrorCredit.ext (show rej_err tb ε2 (ε + ((tb : ℝ≥0∞) + 2) * eps) x =
      ε2 ⟨x, hx⟩ by simp [rej_err, hx]) $$ Herr
    imodintro
    iexists ⟨x, hx⟩
    iframe Herr
    iunfold rand_tapes3
    isplitl
    · iexists ls ++ [(x : ℕ)]
      iframe Hfrag
      ipureintro
      rw [List.filter_append, Hfilter]
      simp [Nat.lt_succ_iff.1 hx]
    · ipureintro
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact Hf y hy
      · rw [List.mem_singleton.1 hy]
        exact Nat.lt_succ_iff.1 hx
  · -- reject
    ihave Herr := ErrorCredit.ext (show rej_err tb ε2 (ε + ((tb : ℝ≥0∞) + 2) * eps) x =
      ε + (((tb : NNReal) + 2 : NNReal) : ℝ≥0∞) * eps by simp [rej_err, hx]) $$ Herr
    ihave ⟨Hε, Hk⟩ := ErrorCredit.split $$ Herr
    iapply IH $$ Hk [Hfrag] Hε
    iexists ls ++ [(x : ℕ)]
    iframe Hfrag
    ipureintro
    rw [List.filter_append, Hfilter]
    simp [Nat.lt_succ_iff.not.1 hx]

/-- Rocq: fifth `Next Obligation` of `rand_spec3`. -/
theorem rand_spec3_rand_inv_create_spec (N : Namespace) (E : CoPset) (_HN : ↑N ⊆ E) :
    ⊢@{IProp GF} |={E}=> ∃ γ1, is_rand3 tb N γ1 :=
  rand_inv_gen_create (tb + 1) N E

/-- Rocq: sixth `Next Obligation` of `rand_spec3`. -/
theorem rand_spec3_rand_allocate_tape_spec (N : Namespace) (γ : GName × GName) (E : CoPset)
    (HN : ↑N ⊆ E) :
    {{ is_rand3 (GF := GF) tb N γ }} cpl(v(&(rand_allocate_tape3 tb)) #()) @ E
    {{ v, RET v; rand_token3 v γ ∗ rand_tapes3 tb v [] γ }} := by
  unfold is_rand3 rand_inv_pred3
  iintro %Φ #Hinv HΦ
  wp_lam
  wp_apply rand_inv_gen_alloc (tb + 1) N γ E HN $$ Hinv with %v ⟨Htok, Hfrag⟩
  iapply HΦ
  unfold rand_token3 rand_tapes3
  iframe Htok
  isplitl
  · iexists []
    iframe Hfrag
    ipureintro
    rfl
  · ipureintro
    simp

/-- Rocq: seventh `Next Obligation` of `rand_spec3`. -/
theorem rand_spec3_rand_tape_spec_some (N : Namespace) (γ : GName × GName) (E : CoPset)
    (α : val) (n : ℕ) (ns : List ℕ) (HN : ↑N ⊆ E) :
    {{ is_rand3 (GF := GF) tb N γ ∗ rand_tapes3 tb α (n :: ns) γ }}
      cpl(v(&(rand_tape3 tb)) v(&α)) @ E
    {{ RET LitV (LitInt (n : ℤ)); rand_tapes3 tb α ns γ }} := by
  unfold is_rand3 rand_inv_pred3 rand_tapes3
  iintro %Φ ⟨#Hinv, ⟨%ns', %Hfilter, Hfrag⟩, %Hforall⟩ HΦ
  iloeb as IH generalizing %ns' %Hfilter Hfrag HΦ
  wp_rec
  cases ns' with
  | nil => simp at Hfilter
  | cons m ns'' =>
    wp_bind (Rand _ _)
    wp_apply rand_inv_gen_rand (tb + 1) N γ E α m ns'' HN $$ [Hfrag] with Hfrag
    · iframe Hinv Hfrag
    wp_pures
    by_cases hm : m ≤ tb
    · rw [decide_eq_true hm]
      rw [List.filter_cons_of_pos (by simpa using hm)] at Hfilter
      obtain ⟨rfl, Htail⟩ := List.cons.inj Hfilter
      wp_pures
      iapply HΦ
      isplitl
      · iexists ns''
        iframe Hfrag
        ipureintro
        exact Htail
      · ipureintro
        exact fun x hx => Hforall x (List.mem_cons_of_mem m hx)
    · rw [decide_eq_false hm]
      rw [List.filter_cons_of_neg (by simpa using hm)] at Hfilter
      wp_if
      iapply IH $$ %ns'' %Hfilter Hfrag HΦ

/-- Rocq: `rand_spec3` (a `#[local] Program Definition`). -/
@[instance_reducible]
def rand_spec3 : rand_spec' tb GF where
  rand_allocate_tape := rand_allocate_tape3 tb
  rand_tape := rand_tape3 tb
  rand_tape_name := GName × GName
  is_rand := is_rand3 tb
  rand_tapes := rand_tapes3 tb
  rand_token := rand_token3
  is_rand_persistent := is_rand3_persistent tb
  rand_tapes_timeless := rand_tapes3_timeless tb
  rand_token_timeless := rand_token3_timeless
  rand_tapes_exclusive := rand_spec3_rand_tapes_exclusive tb
  rand_token_exclusive := rand_spec3_rand_token_exclusive
  rand_tapes_valid := rand_spec3_rand_tapes_valid tb
  rand_tapes_presample := rand_spec3_rand_tapes_presample tb
  rand_inv_create_spec := rand_spec3_rand_inv_create_spec tb
  rand_allocate_tape_spec := rand_spec3_rand_allocate_tape_spec tb
  rand_tape_spec_some := rand_spec3_rand_tape_spec_some tb

end impl3

end Coneris.Lib.HocapRandAlt
