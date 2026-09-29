module

public import Metrology.Coneris.Examples.HashDir.ConHashInterface2
public import Metrology.Coneris.Examples.HashDir.ConHashInterface3

/-!
# An implementation of the concurrent hash interface 3 (amortized errors)

Ported from clutch/theories/coneris/examples/hash/con_hash_impl3.v

The interface `con_hash3` (with a bound `max_hash_size` on the number of hashed values and a
per-query amortized error `amortized_error`) is implemented on top of any implementation of
`con_hash2`, by adding an invariant that stores the amortized error credits and a token
counting how many values may still be hashed.

## Rocq → Lean mapping
* The section context `Variable val_size max_hash_size`, `Hypothesis Hpos`,
  `conerisGS Σ, hash2 : con_hash2 val_size, Htoken : inG Σ (authR natR)` is
  `(val_size max_hash_size : ℕ) (Hpos : 0 < max_hash_size)`,
  `[conerisGS GF] [hash2 : con_hash2 GF val_size] [ElemG GF (constOF (Auth ℕ))]`
  (iris-lean's constant-core CMRA `Auth ℕ` on `(ℕ, +)`). The section variables are explicit
  arguments of the definitions (`val_size`, `max_hash_size`, and `Hpos` where it is used).
* `own γ (● n)` / `own γ (◯ n)` are `iOwn (F := constOF (Auth ℕ)) γ (● n)` / `.. (◯ n)`; the
  token ghost name is a `GName`.
* Definitions (same names): `init_hash`, `compute_hash`, `allocate_tape`, `hash_set_frag`,
  `hash_set`, `hash_auth`, `hash_tape`, `hash_frag`, `hash_token`, `con_hash_inv`.
  - In `hash_set`, `ε : nonnegreal` with
    `ε = ((max_hash_size-1) * n/2 - sum_n_m (λ x, INR x) 0 (n-1)) / (val_size + 1)` is
    `ε : ℝ≥0∞` with `ε = amortized_eps val_size max_hash_size n` (the helper
    `amortized_eps n` is the Rocq expression, with `sum_n_m (λ x, INR x) 0 (n-1)` written
    `∑ x ∈ Finset.range n, (x : ℝ≥0∞)`, equal also for `n = 0` since `sum_n_m _ 0 0 = INR 0`).
    The subtraction truncates in `ℝ≥0∞`, but never in a satisfiable `hash_set`: the tokens
    `own γ (● max_hash_size) ∗ own γ (◯ n)` force `n ≤ max_hash_size`, where the difference is
    `n * (max_hash_size - n) / 2 ≥ 0` (`amortized_eps_closed`). In Rocq, a negative value
    would make `hash_set` unsatisfiable, so the two agree on all reachable states.
* Lemmas (same names): `err_pos`, `amortized_inequality` (both are nonnegativity facts,
  trivial in `ℝ≥0∞`; the real content of `amortized_inequality`, that the subtraction does not
  truncate, is `amortized_eps_closed`), `hash_tape_presample`, `con_hash_init`,
  `con_hash_alloc_tape`, `con_hash_spec`.
  - `hash_tape_presample` uses `con_hash2`'s `hash_tape_presample` with `ε = s / (val_size+1)`
    and `εO = 0` (Rocq: `mknonnegreal _ _` and `0%NNR`); the Lean side condition is the
    subtraction-free form of the Rocq one (see `ConHashInterface2`).
  - `ec_valid` (used in Rocq only to build a `nonnegreal`) is not needed.
* `Program Definition con_hash_impl3 : con_hash3 val_size max_hash_size Hpos` is the Lean
  `def con_hash_impl3 : con_hash3 GF val_size max_hash_size Hpos` (a `def`, as in Rocq it is
  not an instance). The gname types are `hash2`'s and `GName` for the token. The obligations
  are the fields `hash_auth_exclusive`, ..., `hash_token_split` (proved from `con_hash2`'s
  lemmas and `own_frag_add`), and the `Timeless`/`Persistent` fields (found by `apply _` in
  Rocq).

## Added
* `amortized_eps`, `nat_aux`, `nat_aux2`, `amortized_eps_closed`, `amortized_error_closed`,
  `amortized_step` (the real arithmetic of `hash_tape_presample`; Rocq does it inline with
  `lra`), `own_frag_add` (Rocq: `own_op` + `auth_frag_op` + `nat_op`), `token_bound` (the Rocq
  `iAssert (⌜s+1 <= max_hash_size⌝)`), `nclose_rand_subseteq` (Rocq: `subseteq_difference_r` +
  `ndot_ne_disjoint` + `nclose_subseteq'`), the instances `hash_set_timeless`,
  `con_hash_inv_persistent`, `hash_token_timeless`. These helpers mirror those of
  `Coneris.Examples.Hash` (not imported, to keep this unit self-contained).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)
open Coneris.Examples.HashDir.ConHashInterface2
open Coneris.Examples.HashDir.ConHashInterface3 (con_hash3 amortized_error)

namespace Coneris.Examples.HashDir.ConHashImpl3

/-! ## Arithmetic -/

/-- Arithmetic helper for `amortized_eps_closed`. -/
theorem nat_aux (k h : ℕ) (hk : k ≤ h) : (h - 1) * k - k * (k - 1) = k * (h - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rcases k with _ | k
  · simp
  · have e1 : k + 1 + d - 1 = k + d := by omega
    have e2 : k + 1 + d - (k + 1) = d := by omega
    rw [e1, e2, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring

/-- Arithmetic helper for `amortized_step`. -/
theorem nat_aux2 (k h : ℕ) (hk : k + 1 ≤ h) :
    (h - 1) + k * (h - k) = 2 * k + (k + 1) * (h - (k + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have e1 : k + 1 + d - 1 = k + d := by omega
  have e2 : k + 1 + d - k = d + 1 := by omega
  have e3 : k + 1 + d - (k + 1) = d := by omega
  rw [e1, e2, e3]
  ring

section arith

variable (val_size max_hash_size : ℕ)

/-- The error stored in `hash_set` for `n` hashed values (Rocq: inline in `hash_set`). -/
def amortized_eps (n : ℕ) : ℝ≥0∞ :=
  (((max_hash_size : ℝ≥0∞) - 1) * n / 2 - ∑ x ∈ Finset.range n, (x : ℝ≥0∞)) /
    ((val_size : ℝ≥0∞) + 1)

/-- The closed form of `amortized_eps` for `k ≤ max_hash_size`: the truncated subtraction in
its definition does not truncate. -/
theorem amortized_eps_closed (k : ℕ) (hk : k ≤ max_hash_size) :
    amortized_eps val_size max_hash_size k =
      ((k * (max_hash_size - k) : ℕ) : ℝ≥0∞) / (2 * ((val_size : ℝ≥0∞) + 1)) := by
  unfold amortized_eps
  have hs : (∑ x ∈ Finset.range k, (x : ℝ≥0∞)) = ((k * (k - 1) : ℕ) : ℝ≥0∞) / 2 := by
    rw [← Finset.sum_range_id_mul_two, Nat.cast_mul, ← Nat.cast_sum]
    push_cast
    rw [ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  have hm : ((max_hash_size : ℝ≥0∞) - 1) * k = (((max_hash_size - 1) * k : ℕ) : ℝ≥0∞) := by
    push_cast [ENNReal.natCast_sub]; rfl
  rw [hs, hm, ← ENNReal.sub_div (fun _ _ => by norm_num), ← ENNReal.natCast_sub,
    nat_aux k max_hash_size hk]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp),
    mul_assoc]

/-- The closed form of `amortized_error`. -/
theorem amortized_error_closed (Hpos : 0 < max_hash_size) :
    amortized_error val_size max_hash_size Hpos =
      ((max_hash_size - 1 : ℕ) : ℝ≥0∞) / (2 * ((val_size : ℝ≥0∞) + 1)) := by
  unfold amortized_error
  rw [ENNReal.natCast_sub, Nat.cast_one]

/-- The error bookkeeping of one presampling (Rocq: the `ec_eq` computation in
`hash_tape_presample`). -/
theorem amortized_step (Hpos : 0 < max_hash_size) (k : ℕ) (hk : k + 1 ≤ max_hash_size) :
    amortized_error val_size max_hash_size Hpos + amortized_eps val_size max_hash_size k =
      (k : ℝ≥0∞) / ((val_size : ℝ≥0∞) + 1) + amortized_eps val_size max_hash_size (k + 1) := by
  rw [amortized_error_closed, amortized_eps_closed _ _ _ (by omega),
    amortized_eps_closed _ _ _ hk, ENNReal.div_add_div_same,
    ← ENNReal.mul_div_mul_left (k : ℝ≥0∞) _ (two_ne_zero) (by simp), ENNReal.div_add_div_same]
  congr 1
  have := nat_aux2 k max_hash_size hk
  exact_mod_cast this

/-- Rocq: `err_pos` (trivial in `ℝ≥0∞`). -/
theorem err_pos (s : ℕ) : 0 ≤ (s : ℝ≥0∞) / ((val_size : ℝ≥0∞) + 1) := bot_le

/-- Rocq: `amortized_inequality`. In `ℝ≥0∞` nonnegativity is trivial; the content of the Rocq
lemma (that the subtraction does not truncate for `k ≤ max_hash_size`) is
`amortized_eps_closed`. -/
theorem amortized_inequality (k : ℕ) (_H : k ≤ max_hash_size) :
    0 ≤ (((max_hash_size : ℝ≥0∞) - 1) * k / 2 - ∑ x ∈ Finset.range k, (x : ℝ≥0∞)) /
      ((val_size : ℝ≥0∞) + 1) :=
  bot_le

end arith

/-- Helper (Rocq: `subseteq_difference_r` + `ndot_ne_disjoint` + `nclose_subseteq'`). -/
theorem nclose_rand_subseteq (N : Namespace) (E : CoPset) (H : ↑N ⊆ E) :
    (↑(N.@"rand") : CoPset) ⊆ E \ ↑(N.@"err") := fun x hx =>
  CoPset.in_diff.mpr ⟨nclose_subseteq' "rand" H x hx, fun hx0 =>
    ndot_ne_disjoint N (show ("err" : String) ≠ "rand" by decide) x ⟨hx0, hx⟩⟩

section con_hash_impl3

variable {GF : BundledGFunctors} [conerisGS GF] [Htoken : ElemG GF (constOF (Auth ℕ))]
variable (val_size max_hash_size : ℕ) [hash2 : con_hash2 GF val_size]

/-- Rocq: `own_op` with `auth_frag_op` and `nat_op` (splitting a token). -/
theorem own_frag_add (γ : GName) (a b : ℕ) :
    iOwn (GF := GF) (F := constOF (Auth ℕ)) γ (◯ (a + b)) ⊣⊢
      iOwn (F := constOF (Auth ℕ)) γ (◯ a) ∗ iOwn (F := constOF (Auth ℕ)) γ (◯ b) := by
  have : (◯ (a + b) : Auth ℕ) = (◯ a : Auth ℕ) • ◯ b := Auth.frag_op
  rw [this]
  exact iOwn_op

/-! ## Code -/

/-- Rocq: `init_hash`. -/
def init_hash : val := hash2.init_hash2
/-- Rocq: `compute_hash`. -/
def compute_hash : val := hash2.compute_hash2
/-- Rocq: `allocate_tape`. -/
def allocate_tape : val := hash2.allocate_tape2

/-- Rocq: `hash_set_frag`. -/
def hash_set_frag (v : ℕ) (γ_set : hash2.hash_set_gname) (γ_set' : hash2.hash_set_gname') :
    IProp GF :=
  hash2.hash_set_frag2 v γ_set γ_set'

/-- Rocq: `hash_set`. -/
def hash_set (n : ℕ) (γ : hash2.hash_set_gname) (γ' : hash2.hash_set_gname')
    (γ_token : GName) : IProp GF :=
  iprop(∃ ε : ℝ≥0∞,
    hash2.hash_set2 n γ γ' ∗
    iOwn (F := constOF (Auth ℕ)) γ_token (● max_hash_size) ∗
    iOwn (F := constOF (Auth ℕ)) γ_token (◯ n) ∗
    ⌜ε = (((max_hash_size : ℝ≥0∞) - 1) * n / 2 - ∑ x ∈ Finset.range n, (x : ℝ≥0∞)) /
      ((val_size : ℝ≥0∞) + 1)⌝ ∗
    ↯ ε)

/-- Rocq: `hash_auth`. -/
def hash_auth (m : hmap) (γ : hash2.hash_view_gname) (γ2 : hash2.hash_set_gname)
    (γ4 : hash2.hash_view_gname') (γ5 : hash2.hash_set_gname') : IProp GF :=
  hash2.hash_auth2 m γ γ2 γ4 γ5

/-- Rocq: `hash_tape`. -/
def hash_tape (α : val) (ns : List ℕ) (γ2 : hash2.hash_set_gname)
    (γ3 : hash2.hash_tape_gname) : IProp GF :=
  hash2.hash_tape2 α ns γ2 γ3

/-- Rocq: `hash_frag`. -/
def hash_frag (v res : ℕ) (γ : hash2.hash_view_gname) (γ2 : hash2.hash_set_gname)
    (γ4 : hash2.hash_view_gname') : IProp GF :=
  hash2.hash_frag2 v res γ γ2 γ4

/-- Rocq: `hash_token`. -/
def hash_token (n : ℕ) (γ : GName) : IProp GF := iOwn (F := constOF (Auth ℕ)) γ (◯ n)

/-- Rocq: `con_hash_inv`. -/
def con_hash_inv (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash2.hash_view_gname) (γ2 : hash2.hash_set_gname)
    (γ_tape : hash2.hash_tape_gname) (γ4 : hash2.hash_view_gname')
    (γ5 : hash2.hash_set_gname') (γ_token : GName) (γ_lock : hash2.hash_lock_gname) :
    IProp GF :=
  iprop(hash2.con_hash_inv2 (N.@"rand") f l hm R γ1 γ2 γ_tape γ4 γ5 γ_lock ∗
    inv (N.@"err") (∃ n, hash_set val_size max_hash_size n γ2 γ5 γ_token))

instance hash_token_timeless (n : ℕ) (γ : GName) :
    Timeless (hash_token (GF := GF) n γ) := by
  unfold hash_token; infer_instance

instance hash_set_timeless (n : ℕ) (γ : hash2.hash_set_gname) (γ' : hash2.hash_set_gname')
    (γ_token : GName) : Timeless (hash_set val_size max_hash_size n γ γ' γ_token) := by
  unfold hash_set
  have : ∀ k : ℕ, Timeless (iOwn (GF := GF) (F := constOF (Auth ℕ)) γ_token (◯ k)) :=
    fun _ => inferInstance
  have : Timeless (iOwn (GF := GF) (F := constOF (Auth ℕ)) γ_token (● max_hash_size)) :=
    inferInstance
  infer_instance

instance con_hash_inv_persistent (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash2.hash_view_gname) (γ2 : hash2.hash_set_gname)
    (γ_tape : hash2.hash_tape_gname) (γ4 : hash2.hash_view_gname')
    (γ5 : hash2.hash_set_gname') (γ_token : GName) (γ_lock : hash2.hash_lock_gname) :
    Persistent (con_hash_inv val_size max_hash_size N f l hm R γ1 γ2 γ_tape γ4 γ5 γ_token
      γ_lock) := by
  unfold con_hash_inv; infer_instance

/-- Helper: the Rocq `iAssert (⌜s+1 <= max_hash_size⌝)` of `hash_tape_presample`. -/
theorem token_bound (γ : GName) (s : ℕ) :
    ⊢@{IProp GF} iOwn (F := constOF (Auth ℕ)) γ (● max_hash_size) -∗
      iOwn (F := constOF (Auth ℕ)) γ (◯ 1) -∗ iOwn (F := constOF (Auth ℕ)) γ (◯ s) -∗
      ⌜s + 1 ≤ max_hash_size⌝ := by
  iintro H1 H2 H3
  ihave H2 := (own_frag_add γ 1 s).2 $$ [H2 H3]
  · isplitl [H2]
    · iexact H2
    · iexact H3
  icases (iOwn_cmraValid_op (GF := GF) (F := constOF (Auth ℕ)) (γ := γ)
      (a1 := (● max_hash_size : Auth ℕ)) (a2 := ◯ (1 + s))) $$ [H1 H2] with %Hv
  · isplitl [H1]
    · iexact H1
    · iexact H2
  ipureintro
  obtain ⟨⟨z, hz⟩, -⟩ := Auth.auth_both_valid_discrete.mp Hv
  change max_hash_size = 1 + s + z at hz
  omega

/-- Rocq: `hash_tape_presample`. -/
theorem hash_tape_presample (Hpos : 0 < max_hash_size) (N : Namespace) (f l hm : val)
    (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] (γ_hv : hash2.hash_view_gname)
    (γ_set : hash2.hash_set_gname) (γ_hv' : hash2.hash_view_gname') (γ_token : GName)
    (γ : hash2.hash_tape_gname) (γ_set' : hash2.hash_set_gname')
    (γ_lock : hash2.hash_lock_gname) (α : val) (ns : List ℕ) (E : CoPset) (Hsubset : ↑N ⊆ E) :
    ⊢ con_hash_inv val_size max_hash_size N f l hm R γ_hv γ_set γ γ_hv' γ_set' γ_token γ_lock -∗
      hash_tape val_size α ns γ_set γ -∗
      ↯ (amortized_error val_size max_hash_size Hpos) -∗
      hash_token 1 γ_token -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        hash_tape val_size α (ns ++ [(n : ℕ)]) γ_set γ ∗
          hash_set_frag val_size (n : ℕ) γ_set γ_set') := by
  unfold hash_tape hash_token con_hash_inv
  iintro #⟨Hinv, Hinv'⟩ Ht Herr Htoken
  have Hsub_err : (↑(N.@"err") : CoPset) ⊆ E := nclose_subseteq' "err" Hsubset
  imod inv_acc Hsub_err $$ Hinv' with ⟨HI, Hclose⟩
  imod HI with ⟨%s, HI⟩
  unfold hash_set
  icases HI with ⟨%ε, Hs, Hauth, Htokens, %H, Herr'⟩
  subst H
  ihave %Hineq := token_bound max_hash_size γ_token s $$ Hauth Htoken Htokens
  ihave Herr := ErrorCredit.combine $$ [Herr Herr']
  · isplitl [Herr]
    · iexact Herr
    · iexact Herr'
  ihave Herr : ↯ ((s : ℝ≥0∞) / ((val_size : ℝ≥0∞) + 1) +
      amortized_eps val_size max_hash_size (s + 1)) $$ [Herr]
  · have Hstep : amortized_error val_size max_hash_size Hpos +
        (((max_hash_size : ℝ≥0∞) - 1) * s / 2 - ∑ x ∈ Finset.range s, (x : ℝ≥0∞)) /
          ((val_size : ℝ≥0∞) + 1) =
        (s : ℝ≥0∞) / ((val_size : ℝ≥0∞) + 1) + amortized_eps val_size max_hash_size (s + 1) :=
      amortized_step val_size max_hash_size Hpos s Hineq
    iapply ErrorCredit.ext Hstep
    iexact Herr
  icases ErrorCredit.split $$ Herr with ⟨Herr, Herr'⟩
  have Hcond : (s : ℝ≥0∞) + 0 * ((val_size : ℝ≥0∞) + 1) ≤
      (s : ℝ≥0∞) / ((val_size : ℝ≥0∞) + 1) * ((val_size : ℝ≥0∞) + 1) + 0 * s := by
    rw [zero_mul, zero_mul, add_zero, add_zero,
      ENNReal.div_mul_cancel (by simp) (by simp)]
  imod hash2.hash_tape_presample (N.@"rand") f l hm R γ_hv γ_set γ_hv' γ γ_set' γ_lock α ns s
    ((s : ℝ≥0∞) / ((val_size : ℝ≥0∞) + 1)) 0 (E \ ↑(N.@"err"))
    (nclose_rand_subseteq N E Hsubset) (by simp) Hcond $$ Hinv Ht Herr Hs
    with ⟨%n, ⟨Hs, -⟩, Ht, Hsf⟩
  ihave Htokens := (own_frag_add γ_token 1 s).2 $$ [Htoken Htokens]
  · isplitl [Htoken]
    · iexact Htoken
    · iexact Htokens
  imod Hclose $$ [Hauth Htokens Hs Herr'] with -
  · inext
    iexists s + 1
    iexists amortized_eps val_size max_hash_size (s + 1)
    rw [Nat.add_comm 1 s]
    iframe
    ipureintro
    rfl
  imodintro
  iexists n
  unfold hash_set_frag
  iframe

/-- Rocq: `con_hash_init`. -/
theorem con_hash_init (N : Namespace) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] :
    {{ R ∅ }} cpl(&(init_hash (GF := GF) val_size) #())
    {{ (f : val), RET f; ∃ (l hm : val) (γ1 : hash2.hash_view_gname)
        (γ2 : hash2.hash_set_gname) (γ3 : hash2.hash_tape_gname) (γ4 : hash2.hash_view_gname')
        (γ5 : hash2.hash_set_gname') (γ_token : GName) (γ_lock : hash2.hash_lock_gname),
        con_hash_inv val_size max_hash_size N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗
        hash_token max_hash_size γ_token }} := by
  iintro %Φ HP HΦ
  have hv : ✓ ((● max_hash_size : Auth ℕ) • ◯ (0 + max_hash_size)) :=
    Auth.auth_both_valid_2 trivial ⟨0, by simp [CMRA.op]; rfl⟩
  imod iOwn_alloc (GF := GF) (F := constOF (Auth ℕ)) _ hv with ⟨%γ_token, Hown⟩
  icases iOwn_op.1 $$ Hown with ⟨Hauth, Hfrag⟩
  icases (own_frag_add γ_token 0 max_hash_size).1 $$ Hfrag with ⟨H0, Hmax⟩
  iapply pgl_wp_fupd
  unfold init_hash
  wp_apply hash2.con_hash_init2 (N.@"rand") R $$ HP
    with %f ⟨%l, %hm, %γ1, %γ2, %γ3, %γ4, %γ5, %γ_lock, #Hinv, Hs⟩
  imod ErrorCredit.zero (GF := GF) with H0err
  imod inv_alloc (N.@"err") ⊤ (iprop(∃ n : ℕ, hash_set val_size max_hash_size n γ2 γ5 γ_token))
    $$ [H0 Hauth Hs H0err] with #Hinv'
  · inext
    iexists 0
    unfold hash_set
    iexists 0
    iframe
    ipureintro
    simp
  imodintro
  iapply HΦ
  iexists l, hm, γ1, γ2, γ3, γ4, γ5, γ_token, γ_lock
  unfold con_hash_inv hash_token
  iframe Hmax
  isplitl
  · iexact Hinv
  · iexact Hinv'

/-- Rocq: `con_hash_alloc_tape`. -/
theorem con_hash_alloc_tape (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash2.hash_view_gname) (γ2 : hash2.hash_set_gname)
    (γ3 : hash2.hash_tape_gname) (γ4 : hash2.hash_view_gname') (γ5 : hash2.hash_set_gname')
    (γ_token : GName) (γ_lock : hash2.hash_lock_gname) :
    {{ con_hash_inv val_size max_hash_size N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock }}
      cpl(&(allocate_tape (GF := GF) val_size) #())
    {{ (α : val), RET α; hash_tape val_size α [] γ2 γ3 }} := by
  unfold con_hash_inv
  iintro %Φ ⟨#H1, #H2⟩ HΦ
  unfold allocate_tape
  wp_apply hash2.con_hash_alloc_tape2 (N.@"rand") f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock $$ H1
    with %α Ht
  iapply HΦ
  unfold hash_tape
  iexact Ht

/-- Rocq: `con_hash_spec`. -/
theorem con_hash_spec (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash2.hash_view_gname) (γ2 : hash2.hash_set_gname)
    (γ3 : hash2.hash_tape_gname) (γ4 : hash2.hash_view_gname') (γ5 : hash2.hash_set_gname')
    (γ_token : GName) (γ_lock : hash2.hash_lock_gname) (Q1 : ℕ → IProp GF)
    (Q2 : ℕ → List ℕ → IProp GF) (α : val) (v : ℕ) :
    {{ con_hash_inv val_size max_hash_size N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock ∗
        (∀ m, R m -∗ hash_auth val_size m γ1 γ2 γ4 γ5 -∗ state_update ⊤ ⊤
          (match m[v]? with
           | some res => iprop(R m ∗ hash_auth val_size m γ1 γ2 γ4 γ5 ∗ Q1 res)
           | none => iprop(∃ n ns, hash_tape val_size α (n :: ns) γ2 γ3 ∗
                (hash_tape val_size α ns γ2 γ3 ={⊤}=∗ R (m.insert v n) ∗
                  hash_auth val_size (m.insert v n) γ1 γ2 γ4 γ5 ∗ Q2 n ns)))) }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); Q1 res ∨ ∃ ns, Q2 res ns }} := by
  unfold con_hash_inv
  iintro %Φ ⟨⟨#H1, #H2⟩, Hvs⟩ HΦ
  iapply hash2.con_hash_spec2 (N.@"rand") f l hm R γ1 γ2 γ3 γ4 γ5 γ_lock Q1 Q2 α v
    $$ [Hvs] HΦ
  isplitr
  · iexact H1
  · unfold hash_auth hash_tape
    iexact Hvs

/-- Rocq: `con_hash_impl3`. -/
@[instance_reducible] def con_hash_impl3 (Hpos : 0 < max_hash_size) : con_hash3 GF val_size max_hash_size Hpos where
  init_hash3 := init_hash val_size
  allocate_tape3 := allocate_tape val_size
  compute_hash3 := compute_hash val_size
  hash_view_gname := hash2.hash_view_gname
  hash_set_gname := hash2.hash_set_gname
  hash_tape_gname := hash2.hash_tape_gname
  hash_lock_gname := hash2.hash_lock_gname
  hash_view_gname' := hash2.hash_view_gname'
  hash_set_gname' := hash2.hash_set_gname'
  hash_token_gname := GName
  con_hash_inv3 N f l hm R _ γ1 γ2 γ3 γ4 γ5 γ6 γ_lock :=
    con_hash_inv val_size max_hash_size N f l hm R γ1 γ2 γ3 γ4 γ5 γ6 γ_lock
  hash_tape3 := hash_tape val_size
  hash_frag3 := hash_frag val_size
  hash_auth3 := hash_auth val_size
  hash_set3 := hash_set val_size max_hash_size
  hash_set_frag3 := hash_set_frag val_size
  hash_token3 := hash_token
  hash_tape_timeless α ns γ2 γ3 := by unfold hash_tape; infer_instance
  hash_auth_timeless m γ γ2 γ4 γ5 := by unfold hash_auth; infer_instance
  hash_frag_timeless v res γ γ2 γ4 := by unfold hash_frag; infer_instance
  hash_set_timeless s γ2 γ5 γ6 := inferInstance
  hash_set_frag_timeless s γ2 γ5 := by unfold hash_set_frag; infer_instance
  hash_token_timeless s γ6 := inferInstance
  con_hash_inv_persistent N f l hm γ1 γ2 γ3 R _ γ4 γ5 γ6 γ_lock := inferInstance
  hash_frag_persistent v res γ γ2 γ4 := by unfold hash_frag; infer_instance
  hash_auth_exclusive m m' γ γ2 γ4 γ5 := hash2.hash_auth_exclusive m m' γ γ2 γ4 γ5
  hash_auth_frag_agree m k v γ γ2 γ4 γ5 := hash2.hash_auth_frag_agree m k v γ γ2 γ4 γ5
  hash_auth_duplicate m k v γ γ2 γ4 γ5 H := hash2.hash_auth_duplicate m k v γ γ2 γ4 γ5 H
  hash_auth_coll_free m γ γ2 γ4 γ5 := by
    unfold hash_auth
    iintro H
    ihave %Hc := hash2.hash_auth_coll_free m γ γ2 γ4 γ5 $$ H
    ipureintro
    exact Hc
  hash_frag_frag_agree k1 k2 v1 v2 γ γ2 γ4 := hash2.hash_frag_frag_agree k1 k2 v1 v2 γ γ2 γ4
  hash_auth_insert m k v γ1 γ2 γ4 γ5 H := hash2.hash_auth_insert m k v γ1 γ2 γ4 γ5 H
  hash_tape_valid α ns γ2 γ3 := hash2.hash_tape_valid α ns γ2 γ3
  hash_tape_exclusive α ns ns' γ2 γ3 := hash2.hash_tape_exclusive α ns ns' γ2 γ3
  hash_token_split n n' γ6 := own_frag_add γ6 n n'
  hash_tape_presample N f l hm R _ γ_hv γ_set γ_hv' γ_token γ γ_set' γ_lock α ns E H :=
    hash_tape_presample val_size max_hash_size Hpos N f l hm R γ_hv γ_set γ_hv' γ_token γ
      γ_set' γ_lock α ns E H
  con_hash_init3 N R _ := con_hash_init val_size max_hash_size N R
  con_hash_alloc_tape3 N f l hm R _ γ1 γ2 γ3 γ4 γ5 γ_token γ_lock :=
    con_hash_alloc_tape val_size max_hash_size N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock
  con_hash_spec3 N f l hm R _ γ1 γ2 γ3 γ4 γ5 γ_token γ_lock Q1 Q2 α v :=
    con_hash_spec val_size max_hash_size N f l hm R γ1 γ2 γ3 γ4 γ5 γ_token γ_lock Q1 Q2 α v

end con_hash_impl3

end Coneris.Examples.HashDir.ConHashImpl3
