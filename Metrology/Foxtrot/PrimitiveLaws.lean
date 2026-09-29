module

public import Metrology.Foxtrot.Pupd
public import Metrology.Foxtrot.EctxLifting
public import Metrology.ConProbLang.ClassInstances
public import Metrology.ConProbLang.Notation
public import Metrology.ConProbLang.Spec.SpecRA
public import Metrology.Iris.ErrorCredits
public import Iris.Instances.Lib.GhostMap
public import Iris.Std.HeapInstances

/-!
# Primitive laws of Foxtrot

Ported from clutch/theories/foxtrot/primitive_laws.v

This file proves the basic laws of the `con_prob_lang` weakest precondition of Foxtrot by
applying the lifting lemmas (left-hand side), and the basic `pupd` rules for the
specification (right-hand side) thread pool `j ⤇ e`, heap `l ↦ₛ v` and tapes `α ↪ₛN (N; ns)`.

## Rocq → Lean map
All Rocq names are kept: `foxtrotGS` (constructor `HeapG`, fields `foxtrotGS_invG`,
`foxtrotGS_heap`, `foxtrotGS_tapes`, `foxtrotGS_heap_name`, `foxtrotGS_tapes_name`,
`foxtrotGS_spec`, `foxtrotGS_error`), `foxtrotGpreS` (constructor `FoxtrotGpreS`),
`heap_auth`, `tapes_auth`, `foxtrotGS_irisGS`, `nat_tape`, `tapeN_to_empty`, `empty_to_tapeN`,
`read_tape_head`, `tapeN_tapeN_contradict`, `tapeN_ineq`, `pupd_epsilon_err`, `pupd_presample`,
`wp_rec_löb`, `wp_alloc`, `wp_allocN_seq`, `wp_load`, `wp_store`, `wp_rand`, `wp_alloc_tape`,
`wp_rand_tape`, `wp_rand_tape_empty`, `wp_rand_tape_wrong_bound`, `wp_fork`,
`wp_cmpxchg_fail`, `wp_cmpxchg_suc`, `wp_xchg`, `wp_faa`, `pupd_step_pure`, `pupd_alloc`,
`pupd_load`, `pupd_store`, `pupd_rand`, `pupd_rand_tape`, `pupd_rand_tape_empty`, `pupd_fork`,
`pupd_cmpxchg_fail`, `pupd_cmpxchg_suc`, `pupd_xchg`, `pupd_faa`, `pupd_alloc_tape`.

## Design choices / deviations (Rocq → Lean)
The LHS part follows `Metrology/Coneris/PrimitiveLaws.lean`:
* `foxtrotGS GF` bundles the invariant ghost state (`InvGS_gen .hasNoLC GF`), the ghost maps of
  the heap (`Loc ↦ val`) and of the tapes (`Loc ↦ tape`) with their ghost names, the spec
  ghost state `specG_con_prob_lang GF` of `Metrology.ConProbLang.Spec.SpecRA` and the
  error-credit ghost state `ECGS GF` of `Metrology.Iris.ErrorCredits`. As in Coneris the
  invariant field is not an instance itself (it is found through `foxtrotGS_irisGS`); the other
  fields are instances (Rocq: `::`). `GF` is an `outParam` (as in `Coneris.conerisGS`).
* The ghost maps are iris-lean's `GhostMapG GF Loc V locF` (`locF` of `SpecRA`,
  `Std.ExtTreeMap Loc · compare`). `ghost_map_insert`/`ghost_map_update` produce
  `Iris.Std.insert m k v`, bridged to `m.insert k v` by `ConProbLang.ext_insert_eq`.
* `foxtrotGpreS` has the Rocq fields, all instances. Note (as in Rocq) that
  `foxtrotGpreS_heap`/`foxtrotGpreS_tapes` and the ghost maps inside `foxtrotGpreS_spec` have the
  same types, so an adequacy proof should name the instance it allocates with.
* `ec_supply ε` is `ecAuth ε` (`●↯ ε`), `↯ ε` is `ec ε`; errors are `ℝ≥0∞`.
* `spec_interp ρ := spec_auth ρ`, where `spec_auth` takes a `con_prob_lang.cfg`.
* Points-to notations (`scoped` in `Foxtrot`, so that they do not clash with the (global)
  Coneris ones): `l ↦{dq} v`, `l ↦□ v`, `l ↦{#q} v`, `l ↦ v` (heap) and `l ↪{dq} t`, `l ↪□ t`,
  `l ↪{#q} t`, `l ↪ t` (tapes), with `t : tape` (Rocq's `(N; fs)` is `⟨N, fs⟩`); they unfold to
  the reducible helpers `heap_elem`/`tapes_elem`. The user-level tape is `l ↪N (M; ns)`
  (`nat_tape`). The spec notations `j ⤇ e`, `l ↦ₛ v`, `α ↪ₛ t`, `α ↪ₛN (N; ns)` are the scoped
  `ConProbLang` ones of `SpecRA`.
* As for Coneris, a tape points-to followed by `∗`/`-∗` must be parenthesised, `(l ↪ t) ∗ P`
  (Mathlib's `↪` shares the token).
* Texan triples are iris-lean's, `{{ P }} (e) @ s; E {{ x, RET v; Q }}`; the Rocq side
  conditions `TCEq N (Z.to_nat z)` are plain equalities `(hN : N = z.toNat)`.
* Rocq `#n` for `n : nat` is `LitV (LitInt (n : ℤ))`; `rand #z` is
  `Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))`, `rand(#lbl:α) #z` is
  `Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))`, `ref e` is `Alloc e`, `alloc #z` is
  `alloc (Val (LitV (LitInt z)))`, `(v, #b)%V` is `PairV v (LitV (LitBool b))`.
* `wp_rand` quantifies `n : ℕ` with postcondition `⌜n ≤ N⌝`, as in Rocq Foxtrot (unlike the
  Coneris port, whose Rocq statement uses `n : fin (S N)`).
* `pupd_step_pure` takes `(H1 : P)` explicitly and `PureExec P n e e'` instance-implicitly (as
  `wp_pure_step_fupd`); `pupd_alloc`/`pupd_store` take `[IntoVal e v]`.
* RHS configurations of the `pupd` proofs are destructed into `(es, σ)`; since the pair then
  does not unify with a `CPState` at reducible transparency in `iapply`, the helper
  `spec_coupl_ret_pair` is used instead of `spec_coupl_ret`.
* `tapeN_ineq` states `Forall (λ n, n ≤ N) ns` as `∀ n ∈ ns, n ≤ N`.
* `wp_allocN_seq` produces `[∗list] i ∈ List.range N, (l +ₗ ((i : ℕ) : ℤ)) ↦ v` (Rocq:
  `seq 0 N`) and is proved by induction with `heap_auth_alloc_N` (as in Coneris).
* The RHS `pupd_*` rules: Rocq's `P ⊢ pupd E E Q` stays an entailment, Rocq's `P -∗ Q -∗ R`
  lemmas are stated `P ⊢ Q -∗ R`. Their proofs (Rocq: `spec_coupl_step_r` with an explicit
  predicate and a pgl proof, repeated for every rule) are factored through the helpers
  `spec_coupl_step_r_dmap` (one RHS thread step whose `prim_step` is an image `dmap f μ`
  of a distribution of mass one) and `prim_step_fill_head` (`prim_step (fill K e)` from
  `head_step e`).
* `pupd_presample` is proved with `spec_coupl_step_l_dret_adv` (Rocq: `spec_coupl_rec` with
  the scheduler `full_info_cons_osch (λ ρ, dmap (λ n, length ρ.1 + n) (dunifP N)) ..`, which
  is the construction inlined in `spec_coupl_step_l_dret_adv`).

## Omitted
* `foxtrotΣ` and `subG_foxtrotGPreS`: iris-lean has no `gFunctors` lists / `subG` (as in
  `Coneris.Adequacy`).
* `Global Hint Extern 0 (TCEq _ (Z.to_nat _ )) => rewrite Nat2Z.id`: the side conditions are
  plain equalities here.
* The commented-out Rocq lemmas (`spec_tapeN_to_empty`, ..., `wp_rand_r`, `wp_alloc_tape_r`,
  `wp_rand_empty_r`, `wp_rand_tape_r`, `wp_rand_wrong_tape_r`).

## Added helpers (not in Rocq)
`heap_elem`, `tapes_elem`, `nat_tape_timeless`, `foxtrotGS_state_interp_eq`,
`foxtrotGS_spec_interp_eq`, `foxtrotGS_err_interp_eq`, `foxtrotGS_fork_post_eq`,
`heap_auth_alloc_N`, `exists_pos_of_mass_one`, `prim_step_fill_head`, `spec_coupl_step_r_dmap`,
`spec_coupl_ret_pair`, `pupd_step_pure_step` (one pure RHS step).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-- Rocq: `foxtrotGS`. -/
class foxtrotGS (GF : outParam BundledGFunctors) where
  HeapG ::
  foxtrotGS_invG : InvGS_gen .hasNoLC GF
  /-- CMRA for the state -/
  foxtrotGS_heap : GhostMapG GF Loc val locF
  foxtrotGS_tapes : GhostMapG GF Loc tape locF
  /-- ghost names for the state -/
  foxtrotGS_heap_name : GName
  foxtrotGS_tapes_name : GName
  /-- CMRA and ghost name for the spec -/
  foxtrotGS_spec : specG_con_prob_lang GF
  /-- CMRA and ghost name for the error -/
  foxtrotGS_error : ECGS GF

attribute [reducible, instance] foxtrotGS.foxtrotGS_heap foxtrotGS.foxtrotGS_tapes
  foxtrotGS.foxtrotGS_spec foxtrotGS.foxtrotGS_error

export foxtrotGS (foxtrotGS_heap_name foxtrotGS_tapes_name)

/-- Rocq: `foxtrotGpreS`. -/
class foxtrotGpreS (GF : BundledGFunctors) where
  FoxtrotGpreS ::
  foxtrotGpreS_iris : InvGpreS GF
  foxtrotGpreS_heap : GhostMapG GF Loc val locF
  foxtrotGpreS_tapes : GhostMapG GF Loc tape locF
  foxtrotGpreS_spec : specGpreS GF
  foxtrotGpreS_err : ECPreGS GF

attribute [reducible, instance] foxtrotGpreS.foxtrotGpreS_iris foxtrotGpreS.foxtrotGpreS_heap
  foxtrotGpreS.foxtrotGpreS_tapes foxtrotGpreS.foxtrotGpreS_spec foxtrotGpreS.foxtrotGpreS_err

section auth

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `heap_auth`. -/
def heap_auth (q : Qp) (m : Std.ExtTreeMap Loc val) : IProp GF :=
  ghost_map_auth (H := locF) foxtrotGS_heap_name (DFrac.own q) m

/-- Rocq: `tapes_auth`. -/
def tapes_auth (q : Qp) (m : Std.ExtTreeMap Loc tape) : IProp GF :=
  ghost_map_auth (H := locF) foxtrotGS_tapes_name (DFrac.own q) m

/-- Helper: the heap points-to `l ↦{dq} v` (Rocq: a notation for `ghost_map_elem`). -/
abbrev heap_elem (l : Loc) (dq : DFrac) (v : val) : IProp GF :=
  ghost_map_elem (H := locF) foxtrotGS_heap_name dq l v

/-- Helper: the tape points-to `l ↪{dq} t` (Rocq: a notation for `ghost_map_elem`). -/
abbrev tapes_elem (l : Loc) (dq : DFrac) (t : tape) : IProp GF :=
  ghost_map_elem (H := locF) foxtrotGS_tapes_name dq l t

end auth

/-- Rocq: `foxtrotGS_irisGS`. -/
@[reducible]
instance foxtrotGS_irisGS {GF : BundledGFunctors} [foxtrotGS GF] :
    foxtrotWpGS con_prob_lang GF where
  foxtrotWpGS_invGS := foxtrotGS.foxtrotGS_invG
  state_interp σ := iprop(heap_auth 1 σ.heap ∗ tapes_auth 1 σ.tapes)
  spec_interp ρ := spec_auth ρ
  fork_post _ := iprop(True)
  err_interp ε := ecAuth ε

section interp

variable {GF : BundledGFunctors} [foxtrotGS GF]

theorem foxtrotGS_state_interp_eq (σ : state) :
    state_interp σ = iprop(heap_auth (GF := GF) 1 σ.heap ∗ tapes_auth 1 σ.tapes) := rfl

theorem foxtrotGS_spec_interp_eq (ρ : CPState) :
    spec_interp ρ = spec_auth (GF := GF) ρ := rfl

theorem foxtrotGS_err_interp_eq (ε : ℝ≥0∞) : err_interp ε = ecAuth (GF := GF) ε := rfl

theorem foxtrotGS_fork_post_eq (v : val) :
    fork_post (Λ := con_prob_lang) v = iprop(True : IProp GF) := rfl

end interp

/-! ## Heap -/

/-- Rocq: `l ↦{dq} v`. -/
scoped notation:50 l:50 " ↦{" dq "} " v:50 => heap_elem l dq v
/-- Rocq: `l ↦□ v`. -/
scoped notation:50 l:50 " ↦□ " v:50 => heap_elem l DFrac.discard v
/-- Rocq: `l ↦{# q} v`. -/
scoped notation:50 l:50 " ↦{#" q "} " v:50 => heap_elem l (DFrac.own q) v
/-- Rocq: `l ↦ v`. -/
scoped notation:50 l:50 " ↦ " v:50 => heap_elem l (DFrac.own 1) v

/-! ## Tapes -/

/-- Rocq: `l ↪{dq} v`. -/
scoped notation:50 l:50 " ↪{" dq "} " v:50 => tapes_elem l dq v
/-- Rocq: `l ↪□ v`. -/
scoped notation:50 l:50 " ↪□ " v:50 => tapes_elem l DFrac.discard v
/-- Rocq: `l ↪{# q} v`. -/
scoped notation:50 l:50 " ↪{#" q "} " v:50 => tapes_elem l (DFrac.own q) v
/-- Rocq: `l ↪ v`. -/
scoped notation:50 l:50 " ↪ " v:50 => tapes_elem l (DFrac.own 1) v

/-! ## User-level tapes -/

/-- Rocq: `nat_tape`. -/
def nat_tape {GF : BundledGFunctors} [foxtrotGS GF] (l : Loc) (N : ℕ) (ns : List ℕ) :
    IProp GF :=
  iprop(∃ fs : List (Fin (N + 1)), ⌜fs.map (↑) = ns⌝ ∗ (l ↪ ⟨N, fs⟩))

/-- Rocq: `l ↪N ( M ; ns )`. -/
scoped notation:50 l:50 " ↪N " "(" M "; " ns ")" => nat_tape l M ns

/-- Helper (Rocq infers it by unfolding `nat_tape`). -/
instance nat_tape_timeless {GF : BundledGFunctors} [foxtrotGS GF] (l : Loc) (N : ℕ)
    (ns : List ℕ) : Timeless (l ↪N (N; ns)) := by
  unfold nat_tape
  infer_instance

section tape_interface

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-! Helper lemmas to go back and forth between the user-level representation of tapes (using
`ℕ`) and the backend (using `Fin`). -/

/-- Rocq: `tapeN_to_empty`. -/
theorem tapeN_to_empty (l : Loc) (M : ℕ) :
    ⊢@{IProp GF} l ↪N (M; []) -∗ (l ↪ ⟨M, []⟩) := by
  unfold nat_tape
  iintro ⟨%fs, %Hmap, Hl'⟩
  obtain rfl := List.map_eq_nil_iff.1 Hmap
  iexact Hl'

/-- Rocq: `empty_to_tapeN`. -/
theorem empty_to_tapeN (l : Loc) (M : ℕ) :
    ⊢@{IProp GF} (l ↪ ⟨M, []⟩) -∗ l ↪N (M; []) := by
  unfold nat_tape
  iintro Hl
  iexists []
  iframe Hl
  ipureintro
  rfl

/-- Rocq: `read_tape_head`. -/
theorem read_tape_head (l : Loc) (M n : ℕ) (ns : List ℕ) :
    ⊢@{IProp GF} l ↪N (M; n :: ns) -∗
      ∃ (x : Fin (M + 1)) (xs : List (Fin (M + 1))), (l ↪ ⟨M, x :: xs⟩) ∗ ⌜(x : ℕ) = n⌝ ∗
        ((l ↪ ⟨M, xs⟩) -∗ l ↪N (M; ns)) := by
  unfold nat_tape
  iintro ⟨%xss, %Hmap, Hl'⟩
  obtain ⟨x, xs, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 Hmap
  iexists x, xs
  iframe Hl'
  isplitr
  · ipureintro; rfl
  iintro Hl
  iexists xs
  iframe Hl
  ipureintro
  rfl

/-- Rocq: `tapeN_tapeN_contradict`. -/
theorem tapeN_tapeN_contradict (l : Loc) (N M : ℕ) (ns ms : List ℕ) :
    ⊢@{IProp GF} l ↪N (N; ns) -∗ l ↪N (M; ms) -∗ False := by
  unfold nat_tape
  iintro ⟨%fs1, -, H1⟩ ⟨%fs2, -, H2⟩
  icases ghost_map_elem_ne _ _ _ _ _ _ $$ H1 H2 with %H
  exact absurd rfl H

/-- Rocq: `tapeN_ineq`. -/
theorem tapeN_ineq (α : Loc) (N : ℕ) (ns : List ℕ) :
    ⊢@{IProp GF} α ↪N (N; ns) -∗ ⌜∀ n ∈ ns, n ≤ N⌝ := by
  unfold nat_tape
  iintro Hα
  icases Hα with ⟨%fs, %Hmap, -⟩
  ipureintro
  subst Hmap
  intro n hn
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hn
  exact Nat.lt_succ_iff.1 x.2

end tape_interface

section lifting

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness} {E : CoPset}

/-- Rocq: `pupd_epsilon_err`. -/
theorem pupd_epsilon_err (E : CoPset) :
    ⊢@{IProp GF} pupd E E iprop(∃ ε, ⌜0 < ε⌝ ∗ ↯ ε) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_err_interp_eq]
  iintro %σ1 %ρ1 %ε ⟨Hσ, Hρ, Hε⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_amplify
  iintro %ε' %Hlt
  by_cases h : ε' < 1
  · iapply spec_coupl_ret
    have heq : ε' = ε + (ε' - ε) := (add_tsub_cancel_of_le (le_of_lt Hlt)).symm
    imod ErrorCredit.supply_increase (ε₂ := ε' - ε) (by rw [← heq]; exact h) $$ Hε with ⟨Hε, Hd⟩
    rw [← heq]
    imod Hclose
    imodintro
    iframe Hσ Hρ Hε
    iexists ε' - ε
    iframe Hd
    ipureintro
    exact tsub_pos_of_lt Hlt
  · iapply spec_coupl_ret_err_ge_1 _ _ _ _ (not_lt.1 h)

/-- Rocq: `pupd_presample`. -/
theorem pupd_presample (N : ℕ) (E : CoPset) (ns : List ℕ) (α : Loc) :
    α ↪N (N; ns) ⊢@{IProp GF} pupd E E iprop(∃ n : ℕ, α ↪N (N; ns ++ [n]) ∗ ⌜n ≤ N⌝) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_state_interp_eq]
  iintro Hα %σ %ρ1 %ε1 ⟨⟨Hh, Ht⟩, Hρ, Hε⟩
  iunfold nat_tape at Hα
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  unfold tapes_auth
  icombine Ht Hα gives %H
  rw [ext_get?_eq] at H
  have Hineq : 0 + Expval (state_step σ α) (fun _ => ε1) ≤ ε1 := by
    rw [zero_add, Expval_const]
    exact mul_le_of_le_one_right zero_le (pmf_SeriesC _)
  have Hpgl : pgl (state_step σ α)
      (fun σ' => ∃ x : Fin (N + 1), σ' = state_upd_tapes (·.insert α ⟨N, fs ++ [x]⟩) σ) 0 := by
    rw [state_step_unfold σ α N fs H, dmap]
    have := pgl_dbind _ (dunifP N) (fun _ => True)
      (fun σ' => ∃ x : Fin (N + 1), σ' = state_upd_tapes (·.insert α ⟨N, fs ++ [x]⟩) σ) 0 0
      (fun a _ => pgl_dret _ _ ⟨a, rfl⟩) (pgl_trivial (dunifP N) 0)
    simpa using this
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_l_dret_adv _ (state_step σ α) 0 (fun _ => ε1) ρ1 σ _ ε1
    (state_step_sch_erasable σ α _ H) ⟨ε1, fun _ => le_rfl⟩ Hineq Hpgl
  iintro %σ2 %⟨x, Hx⟩
  subst Hx
  iapply spec_coupl_ret
  imod ghost_map_update (⟨N, fs ++ [x]⟩ : tape) $$ Ht Hα with ⟨Ht, Hα⟩
  rw [ext_insert_eq]
  simp only [state_upd_tapes_heap', state_upd_tapes_tapes]
  imodintro
  imod Hclose
  imodintro
  iframe Hh Ht Hρ Hε
  iexists (x : ℕ)
  isplitl
  · iunfold nat_tape
    iexists fs ++ [x]
    iframe Hα
    ipureintro
    simp [Hfs]
  · ipureintro
    exact Nat.lt_succ_iff.1 x.2

/-- Rocq: `wp_rec_löb`. Recursive functions: we do not use this lemma as it is easier to use
Löb induction directly, but this demonstrates that we can state the expected reasoning
principle for recursive functions, without any visible `▷`. -/
theorem wp_rec_löb (f x : binder) (e : expr) (Φ Ψ : val → IProp GF) :
    ⊢ □ (□ (∀ v, Ψ v -∗ WP (App (Val (RecV f x e)) (Val v)) @ s; E {{ Φ }}) -∗
        ∀ v, Ψ v -∗ WP (subst' x v (subst' f (RecV f x e) e)) @ s; E {{ Φ }}) -∗
      ∀ v, Ψ v -∗ WP (App (Val (RecV f x e)) (Val v)) @ s; E {{ Φ }} := by
  iintro #Hrec
  iloeb as IH
  iintro %v HΨ
  iapply wp_pure_step_later (Hφ := True.intro)
  inext
  iapply Hrec $$ [] HΨ
  iintro !> %w HΨ
  iapply IH $$ HΨ

/-! ### Heap -/

/-- Rocq: `wp_alloc`. -/
theorem wp_alloc (v : val) :
    {{ True }} (Alloc (Val v)) @ s; E {{ l, RET LitV (LitLoc l); l ↦ v }} := by
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩ !>
  isplitr
  · ipureintro
    solve_red
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N l _ hN hl
  subst hN hl
  rw [show Int.toNat 1 = 1 from rfl, state_upd_heap_singleton]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  unfold heap_auth
  imod ghost_map_insert (fresh_loc σ1.heap) v
    (Std.ExtTreeMap.getElem?_eq_none (fresh_loc_is_fresh σ1.heap)) $$ Hh with ⟨Hh, Hl⟩
  rw [ext_insert_eq]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Helper: allocating a block of `n` fresh heap cells in the ghost heap. -/
theorem heap_auth_alloc_N (m : Std.ExtTreeMap Loc val) (l : Loc) (v : val) (n : ℕ)
    (Hfresh : ∀ i : ℤ, 0 ≤ i → m[l +ₗ i]? = none) :
    ⊢@{IProp GF} heap_auth 1 m ==∗ heap_auth 1 (m ∪ heap_array l (List.replicate n v)) ∗
      [∗list] i ∈ List.range n, (l +ₗ ((i : ℕ) : ℤ)) ↦ v := by
  induction n with
  | zero =>
    have heq : m ∪ heap_array l (List.replicate 0 v) = m := by
      ext k : 1
      simp [map_getElem?_union]
    rw [heq, List.range_zero]
    iintro Hm
    imodintro
    iframe Hm
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n IH =>
    have hnone : (m ∪ heap_array l (List.replicate n v))[l +ₗ (n : ℤ)]? = none := by
      rw [map_getElem?_union]
      rcases h : (heap_array l (List.replicate n v))[l +ₗ (n : ℤ)]? with _ | w
      · simpa using Hfresh n (by omega)
      · obtain ⟨j, hj, hjl, hjv⟩ := (heap_array_lookup _ _ _ _).1 h
        have hj' := congrArg Loc.loc_car hjl
        simp only [loc_add_loc_car, add_right_inj] at hj'
        subst hj'
        simp at hjv
    have heq : m ∪ heap_array l (List.replicate (n + 1) v) =
        (m ∪ heap_array l (List.replicate n v)).insert (l +ₗ (n : ℤ)) v := by
      rw [heap_array_replicate_S_end]
      ext k : 1
      rw [map_getElem?_union, map_getElem?_insert, map_getElem?_insert, map_getElem?_union]
      split <;> simp
    rw [heq, List.range_succ]
    iintro Hm
    imod IH $$ Hm with ⟨Hm, Hl⟩
    unfold heap_auth
    imod ghost_map_insert (l +ₗ (n : ℤ)) v hnone $$ Hm with ⟨Hm, Hn⟩
    rw [ext_insert_eq]
    imodintro
    iframe Hm
    iapply BigSepL.bigSepL_snoc.2
    iframe Hl Hn

/-- Rocq: `wp_allocN_seq`. -/
theorem wp_allocN_seq (N : ℕ) (z : ℤ) (v : val) (hN : N = z.toNat) (hpos : 0 < N) :
    {{ True }} (AllocN (Val (LitV (LitInt z))) (Val v)) @ s; E
    {{ l, RET LitV (LitLoc l); [∗list] i ∈ List.range N, (l +ₗ ((i : ℕ) : ℤ)) ↦ v }} := by
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (AllocNS z N v σ1 _ rfl hN hpos)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N' l _ hN' hl
  subst hN hN' hl
  simp only [state_upd_heap_N, state_upd_heap_heap, state_upd_heap_tapes, to_val_Val,
    Option.elim]
  imod heap_auth_alloc_N σ1.heap (fresh_loc σ1.heap) v z.toNat
    (fun i hi => Std.ExtTreeMap.getElem?_eq_none (fresh_loc_offset_is_fresh σ1.heap i hi))
    $$ Hh with ⟨Hh, Hl⟩
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_load`. -/
theorem wp_load (l : Loc) (dq : DFrac) (v : val) :
    {{ ▷ l ↦{dq} v }} (Load (Val (LitV (LitLoc l)))) @ s; E {{ RET v; l ↦{dq} v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (LoadS l v σ1 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i v' H'
  rw [H] at H'
  cases H'
  simp only [to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_store`. -/
theorem wp_store (l : Loc) (v' v : val) :
    {{ ▷ l ↦ v' }} (Store (Val (LitV (LitLoc l))) (Val v)) @ s; E
    {{ RET LitV LitUnit; l ↦ v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (StoreS l v' v σ1 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  imod ghost_map_update v $$ Hh Hl with ⟨Hh, Hl⟩
  rw [ext_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_rand`. -/
theorem wp_rand (N : ℕ) (z : ℤ) (hN : N = z.toNat) :
    {{ True }} (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (iprop(⌜n ≤ N⌝) : IProp GF) }} := by
  subst hN
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  iintro %σ1 Hσ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandNoTapeS z z.toNat 0 σ1 rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N' n hN'
  subst hN'
  simp only [to_val_Val, Option.elim]
  imodintro
  iframe Hσ
  isplitl
  · iapply HΦ $$ %(n : ℕ)
    ipureintro
    exact Nat.lt_succ_iff.1 n.2
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-! ### Tapes -/

/-- Rocq: `wp_alloc_tape`. -/
theorem wp_alloc_tape (N : ℕ) (z : ℤ) (hN : N = z.toNat) :
    {{ True }} (alloc (Val (LitV (LitInt z)))) @ s; E
    {{ α, RET LitV (LitLbl α); α ↪N (N; []) }} := by
  subst hN
  iintro %Φ - HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (AllocTapeS z z.toNat σ1 _ rfl rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i N' l hl hN'
  subst hl hN'
  unfold tapes_auth
  imod ghost_map_insert (fresh_loc σ1.tapes) (⟨z.toNat, []⟩ : tape)
    (Std.ExtTreeMap.getElem?_eq_none (fresh_loc_is_fresh σ1.tapes)) $$ Ht with ⟨Ht, Hl⟩
  rw [ext_insert_eq]
  simp only [state_upd_tapes_heap', state_upd_tapes_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ
    iapply empty_to_tapeN $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_rand_tape`. -/
theorem wp_rand_tape (N : ℕ) (α : Loc) (n : ℕ) (ns : List ℕ) (z : ℤ) (hN : N = z.toNat) :
    {{ ▷ α ↪N (N; n :: ns) }} (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ RET LitV (LitInt (n : ℤ)); α ↪N (N; ns) ∗ ⌜n ≤ N⌝ }} := by
  subst hN
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  icases read_tape_head α z.toNat n ns $$ Hl with ⟨%x, %xs, Hl, %Hx, Hret⟩
  subst Hx
  unfold tapes_auth
  icombine Ht Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandTapeS α z z.toNat x xs σ1 rfl H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  case RandTapeS =>
    rename_i N' n' ns' hN' h
    subst hN'
    rw [H] at h
    cases h
    imod ghost_map_update (⟨z.toNat, xs⟩ : tape) $$ Ht Hl with ⟨Ht, Hl⟩
    rw [ext_insert_eq]
    simp only [state_upd_tapes_heap', state_upd_tapes_tapes, to_val_Val, Option.elim]
    imodintro
    iframe Hh Ht
    isplitl
    · iapply HΦ
      isplitl
      · iapply Hret $$ Hl
      · ipureintro
        omega
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  all_goals
    rename_i h
    rw [H] at h
    cases h
    try simp_all

/-- Rocq: `wp_rand_tape_empty`. -/
theorem wp_rand_tape_empty (N : ℕ) (z : ℤ) (α : Loc) (hN : N = z.toNat) :
    {{ ▷ α ↪N (N; []) }} (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); α ↪N (N; []) ∗ ⌜n ≤ N⌝ }} := by
  subst hN
  iintro %Φ >Hl HΦ
  ihave Hl := tapeN_to_empty α z.toNat $$ Hl
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold tapes_auth
  icombine Ht Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandTapeEmptyS α z z.toNat 0 σ1 rfl H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  case RandTapeEmptyS =>
    rename_i N' n hN' _
    subst hN'
    simp only [to_val_Val, Option.elim]
    imodintro
    iframe Hh Ht
    isplitl
    · iapply HΦ $$ %n
      isplitl
      · iapply empty_to_tapeN $$ Hl
      · ipureintro
        omega
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  all_goals
    rename_i h
    rw [H] at h
    cases h
    try simp_all

/-- Rocq: `wp_rand_tape_wrong_bound`. -/
theorem wp_rand_tape_wrong_bound (N M : ℕ) (z : ℤ) (α : Loc) (ns : List ℕ) (hN : N = z.toNat)
    (hNM : N ≠ M) :
    {{ ▷ α ↪N (M; ns) }} (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) @ s; E
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); α ↪N (M; ns) ∗ ⌜n ≤ N⌝ }} := by
  subst hN
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  iunfold nat_tape at Hl
  icases Hl with ⟨%fs, %Hfs, Hl⟩
  unfold tapes_auth
  icombine Ht Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (RandTapeOtherS α z M z.toNat fs 0 σ1 rfl H hNM)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  case RandTapeOtherS =>
    rename_i n _ _ _
    simp only [to_val_Val, Option.elim]
    imodintro
    iframe Hh Ht
    isplitl
    · iapply HΦ $$ %n
      isplitl
      · iunfold nat_tape
        iexists fs
        iframe Hl
        ipureintro
        exact Hfs
      · ipureintro
        omega
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  all_goals
    rename_i h
    rw [H] at h
    cases h
    try simp_all

/-- Rocq: `wp_fork`. -/
theorem wp_fork (e : expr) (Φ : val → IProp GF) :
    ⊢ ▷ WP e @ s; ⊤ {{ _v, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP (Fork e) @ s; E {{ Φ }} := by
  iintro He HΦ
  iapply wp_lift_atomic_head_step rfl
  iintro %σ1 Hσ !>
  isplitr
  · ipureintro
    exact head_reducible_of_rel (ForkS e σ1)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  simp only [to_val_Val, Option.elim]
  imodintro
  iframe Hσ HΦ
  iapply BigSepL.bigSepL_singleton.2
  iexact He

/-! ### Concurrency -/

/-- Rocq: `wp_cmpxchg_fail`. -/
theorem wp_cmpxchg_fail (v v1 v2 : val) (l : Loc) (dq : DFrac) (Hsafe : vals_compare_safe v v1)
    (Hne : v ≠ v1) :
    {{ ▷ l ↦{dq} v }} (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) @ s; E
    {{ RET PairV v (LitV (LitBool false)); l ↦{dq} v }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (CmpXchgS σ1 l v v1 v2 _ H Hsafe rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i vl b _ hb H'
  rw [H] at H'
  cases H'
  subst hb
  simp only [Hne, decide_false, Bool.false_eq_true, ↓reduceIte, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_cmpxchg_suc`. -/
theorem wp_cmpxchg_suc (v v1 v2 : val) (l : Loc) (Hsafe : vals_compare_safe v v1)
    (Heq : v = v1) :
    {{ ▷ l ↦ v }} (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) @ s; E
    {{ RET PairV v (LitV (LitBool true)); l ↦ v2 }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (CmpXchgS σ1 l v v1 v2 _ H Hsafe rfl)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i vl b _ hb H'
  rw [H] at H'
  cases H'
  subst hb
  subst Heq
  imod ghost_map_update v2 $$ Hh Hl with ⟨Hh, Hl⟩
  rw [ext_insert_eq]
  simp only [decide_true, ↓reduceIte, state_upd_heap_heap, state_upd_heap_tapes, to_val_Val,
    Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_xchg`. -/
theorem wp_xchg (v1 v2 : val) (l : Loc) :
    {{ ▷ l ↦ v1 }} (Xchg (Val (LitV (LitLoc l))) (Val v2)) @ s; E {{ RET v1; l ↦ v2 }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (XchgS σ1 l v1 v2 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i v1' H'
  rw [H] at H'
  cases H'
  imod ghost_map_update v2 $$ Hh Hl with ⟨Hh, Hl⟩
  rw [ext_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- Rocq: `wp_faa`. -/
theorem wp_faa (i1 i2 : ℤ) (l : Loc) :
    {{ ▷ l ↦ LitV (LitInt i1) }} (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) @ s; E
    {{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }} := by
  iintro %Φ >Hl HΦ
  iapply wp_lift_atomic_head_step rfl
  simp only [foxtrotGS_state_interp_eq]
  iintro %σ1 ⟨Hh, Ht⟩
  unfold heap_auth
  icombine Hh Hl gives %H
  rw [ext_get?_eq] at H
  imodintro
  isplitr
  · ipureintro
    exact head_reducible_of_rel (FAAS σ1 l i1 i2 H)
  iintro !> %e2 %σ2 %efs %Hs
  inv_head_step
  rename_i i1' H'
  rw [H] at H'
  cases H'
  imod ghost_map_update (LitV (LitInt (i1 + i2))) $$ Hh Hl with ⟨Hh, Hl⟩
  rw [ext_insert_eq]
  simp only [state_upd_heap_heap, state_upd_heap_tapes, to_val_Val, Option.elim]
  imodintro
  iframe Hh Ht
  isplitl
  · iapply HΦ $$ Hl
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-! ### Spec (RHS) rules -/

/-- Helper: a distribution of mass one has an element of positive mass. -/
theorem exists_pos_of_mass_one {A : Type} [Countable A] (μ : Distr A) (h : ∑' a, μ a = 1) :
    ∃ a, 0 < μ a := by
  by_contra hne
  push Not at hne
  have : ∑' a, μ a = 0 := ENNReal.tsum_eq_zero.2 fun a => nonpos_iff_eq_zero.1 (hne a)
  rw [this] at h
  exact zero_ne_one h

/-- Helper: the `prim_step` of a head redex `e` in an evaluation context `K`, when the head
step of `e` is the image `dmap f μ` of a distribution of mass one (Rocq: inline, via
`fill_dmap` and `head_prim_step_eq`). -/
theorem prim_step_fill_head {A : Type} [Countable A] (K : List ectx_item) (e : expr) (σ : state)
    (μ : Distr A) (f : A → expr × state × List expr) (Hhead : head_step e σ = dmap f μ)
    (Hmass : ∑' a, μ a = 1) :
    prim_step (Λ := con_prob_lang) (fill K e) σ =
      dmap (fun a => (fill K (f a).1, (f a).2.1, (f a).2.2)) μ := by
  obtain ⟨a, ha⟩ := exists_pos_of_mass_one μ Hmass
  have hpos : 0 < head_step e σ (f a) := by
    rw [Hhead, dmap_pos]
    exact ⟨a, rfl, ha⟩
  have hred : conEctxLanguage.head_reducible (Λ := con_prob_ectx_lang) e σ := ⟨f a, hpos⟩
  have hv : ConProbLang.to_val (Λ := con_prob_lang) e = none := val_head_stuck e σ _ hpos
  have hK : prim_step (Λ := con_prob_lang) (fill K e) σ =
      dmap (fill_lift' (fill K)) (prim_step (Λ := con_prob_lang) e σ) :=
    @ConLanguageCtx.fill_dmap con_prob_lang (fill K) _ e σ hv
  rw [hK]
  have heq : prim_step (Λ := con_prob_lang) e σ = head_step e σ :=
    conEctxLanguage.head_prim_step_eq (Λ := con_prob_ectx_lang) e σ hred
  rw [heq, Hhead, dmap_comp]
  rfl

/-- Helper (Rocq: inline uses of `spec_coupl_step_r`): one step of the RHS thread `j`, whose
`prim_step` is the image `dmap f μ` of a distribution of mass one, with deterministic
resulting tapes `m`. -/
theorem spec_coupl_step_r_dmap {A : Type} [Countable A] (μ : Distr A)
    (f : A → expr × state × List expr) (m : Std.ExtTreeMap Loc tape) (es : List expr)
    (σ σ1 : state) (Z : state → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) (j : ℕ) (e : expr)
    (Hsome : es[j]? = some e) (Hstep : prim_step (Λ := con_prob_lang) e σ = dmap f μ)
    (Hmass : ∑' a, μ a = 1) (Htapes : ∀ a, (f a).2.1.tapes = m) :
    (∀ a, |={∅}=> spec_coupl σ1 ((es.set j (f a).1 ++ (f a).2.2, (f a).2.1) : CPState) ε Z) ⊢
      spec_coupl σ1 ((es, σ) : CPState) ε Z := by
  obtain ⟨a, ha⟩ := exists_pos_of_mass_one μ Hmass
  have Hred : reducible (Λ := con_prob_lang) e σ := ⟨f a, by rw [Hstep, dmap_pos]; exact ⟨a, rfl, ha⟩⟩
  have Hpgl : pgl (prim_step (Λ := con_prob_lang) e σ)
      (fun p => (∃ a, p = f a) ∧ p.2.1.tapes = m) 0 := by
    rw [Hstep, dmap]
    have := pgl_dbind _ μ (fun _ => True) (fun p => (∃ a, p = f a) ∧ p.2.1.tapes = m) 0 0
      (fun a _ => pgl_dret _ _ ⟨⟨a, rfl⟩, Htapes a⟩) (pgl_trivial μ 0)
    simpa using this
  iintro H
  iapply spec_coupl_step_r (fun p => ∃ a, p = f a) 0 m ε ((es, σ) : CPState) σ1 Z ε j e Hred Hsome
    (by rw [zero_add]) Hpgl
  iintro %e' %σ' %efs %⟨⟨a, Ha⟩, -⟩
  have h1 : e' = (f a).1 := congrArg Prod.fst Ha
  have h2 : σ' = (f a).2.1 := congrArg (fun p => p.2.1) Ha
  have h3 : efs = (f a).2.2 := congrArg (fun p => p.2.2) Ha
  subst h1 h2 h3
  iapply H $$ %a

/-- Helper: `spec_coupl_ret` for an explicit pair `(es, σ)` (which `iapply spec_coupl_ret` does
not unify with a `CPState` at reducible transparency). -/
theorem spec_coupl_ret_pair (σ1 : state) (es : List expr) (σ : state)
    (Z : state → CPState → ℝ≥0∞ → IProp GF) (ε : ℝ≥0∞) :
    Z σ1 ((es, σ) : CPState) ε ⊢ spec_coupl σ1 ((es, σ) : CPState) ε Z :=
  spec_coupl_ret σ1 _ Z ε

/-- Helper: a single pure step of the RHS thread `j` (the inductive step of Rocq's
`pupd_step_pure`). -/
theorem pupd_step_pure_step (E : CoPset) (j : ℕ) (e1 e2 : expr)
    (H : pure_step (Λ := con_prob_lang) e1 e2) :
    j ⤇ e1 ⊢@{IProp GF} pupd E E (j ⤇ e2) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro Hj %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j e1 $$ Hs Hj
  have Hstep : prim_step (Λ := con_prob_lang) e1 σ =
      dmap (fun _ : Unit => ((e2, σ, []) : expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    exact pmf_1_eq_dret _ _ (H.pure_step_det σ)
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ σ.tapes es σ σ1 _ ε1 j e1 Hsome Hstep (dret_mass _)
    (fun _ => rfl)
  iintro %_
  imod spec_update_prog es σ j e1 e2 $$ Hs Hj with ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_step_pure`. -/
theorem pupd_step_pure (P : Prop) (n : ℕ) (e e' : expr) (j : ℕ) (K : List ectx_item)
    (E : CoPset) (H1 : P) [H2 : PureExec (Λ := con_prob_lang) P n e e'] :
    j ⤇ fill K e ⊢@{IProp GF} pupd E E (j ⤇ fill K e') := by
  have H := H2.pure_exec H1
  clear H2
  induction H with
  | nsteps_O e => exact pupd_ret E _
  | nsteps_l n e y e' Hstep _ IH =>
    refine .trans ?_ (pupd_bind E E E (j ⤇ fill K y) _)
    iintro Hj
    isplitl [Hj]
    · iapply pupd_step_pure_step E j _ _ (pure_step_ctx (fill K) e y Hstep) $$ Hj
    · iintro Hj
      iapply IH $$ Hj

/-- Rocq: `pupd_alloc`. Alloc, load, and store. -/
theorem pupd_alloc (E : CoPset) (K : List ectx_item) (e : expr) (v : val) (j : ℕ)
    [Hv : IntoVal (Λ := con_prob_lang) e v] :
    j ⤇ fill K (Alloc e) ⊢@{IProp GF} pupd E E iprop(∃ l, j ⤇ fill K (Val (LitV (LitLoc l))) ∗ l ↦ₛ v) := by
  obtain rfl : Val v = e := Hv.into_val
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro Hj %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  have Hhead : head_step (Alloc (Val v)) σ = dmap (fun _ : Unit =>
      ((Val (LitV (LitLoc (fresh_loc σ.heap))), state_upd_heap (·.insert (fresh_loc σ.heap) v) σ,
        []) : expr × state × List expr)) (dret ()) := by
    rw [dmap_dret, ← state_upd_heap_singleton]
    rfl
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_auth_heap_alloc es σ v $$ Hs with ⟨Hs, Hl⟩
  imod spec_update_prog _ _ j _ (fill K (Val (LitV (LitLoc (fresh_loc σ.heap))))) $$ Hs Hj with
    ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  iexists fresh_loc σ.heap
  iframe

/-- Rocq: `pupd_load`. -/
theorem pupd_load (E : CoPset) (K : List ectx_item) (l : Loc) (q : DFrac) (v : val) (j : ℕ) :
    j ⤇ fill K (Load (Val (LitV (LitLoc l)))) ∗ l ↦ₛ{q} v ⊢@{IProp GF}
      pupd E E iprop(j ⤇ fill K (Val v) ∗ l ↦ₛ{q} v) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro ⟨Hj, Hl⟩ %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave %H := spec_auth_lookup_heap es σ l v q $$ Hs Hl
  have Hhead : head_step (Load (Val (LitV (LitLoc l)))) σ =
      dmap (fun _ : Unit => ((Val v, σ, []) : expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    simp [head_step, H]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val v)) $$ Hs Hj with ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_store`. -/
theorem pupd_store (E : CoPset) (K : List ectx_item) (l : Loc) (v' : val) (e : expr) (v : val)
    (j : ℕ) [Hv : IntoVal (Λ := con_prob_lang) e v] :
    j ⤇ fill K (Store (Val (LitV (LitLoc l))) e) ∗ l ↦ₛ v' ⊢@{IProp GF}
      pupd E E iprop(j ⤇ fill K (Val (LitV LitUnit)) ∗ l ↦ₛ v) := by
  obtain rfl : Val v = e := Hv.into_val
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro ⟨Hj, Hl⟩ %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave %H := spec_auth_lookup_heap es σ l v' _ $$ Hs Hl
  have Hhead : head_step (Store (Val (LitV (LitLoc l))) (Val v)) σ =
      dmap (fun _ : Unit => ((Val (LitV LitUnit), state_upd_heap (·.insert l v) σ, []) :
        expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    simp [head_step, H]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val (LitV LitUnit))) $$ Hs Hj with ⟨Hs, Hj⟩
  imod spec_auth_update_heap v _ _ l v' $$ Hs Hl with ⟨Hs, Hl⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_rand`. -/
theorem pupd_rand (j : ℕ) (K : List ectx_item) (N : ℕ) (z : ℤ) (E : CoPset) (hN : N = z.toNat) :
    j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) ⊢@{IProp GF}
      pupd E E iprop(∃ n : ℕ, j ⤇ fill K (Val (LitV (LitInt (n : ℤ)))) ∗ ⌜n ≤ N⌝) := by
  subst hN
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro Hj %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  have Hhead : head_step (Rand (Val (LitV (LitInt z))) (Val (LitV LitUnit))) σ =
      dmap (fun n : Fin (z.toNat + 1) => ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) :
        expr × state × List expr)) (dunifP z.toNat) := rfl
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dunifP z.toNat) _ σ.tapes es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dunifP_mass _)) (dunifP_mass _) (fun _ => rfl)
  iintro %n
  imod spec_update_prog _ _ j _ (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) $$ Hs Hj with
    ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  iexists (n : ℕ)
  iframe Hj
  ipureintro
  exact Nat.lt_succ_iff.1 n.2

/-- Rocq: `pupd_rand_tape`. Technically not used since presampling on the right is not
allowed. -/
theorem pupd_rand_tape (j : ℕ) (K : List ectx_item) (N : ℕ) (z : ℤ) (E : CoPset) (n : ℕ)
    (ns : List ℕ) (α : Loc) (hN : N = z.toNat) :
    j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) ⊢@{IProp GF}
      α ↪ₛN (N; n :: ns) -∗ pupd E E iprop(j ⤇ fill K (Val (LitV (LitInt (n : ℤ)))) ∗
        α ↪ₛN (N; ns)) := by
  subst hN
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro Hj Htape %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  icases read_spec_tape_head α z.toNat n ns $$ Htape with ⟨%x, %xs, Htape, %Hx, Hret⟩
  subst Hx
  ihave %H := spec_auth_lookup_tape es σ α _ _ $$ Hs Htape
  have Hhead : head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ =
      dmap (fun _ : Unit => ((Val (LitV (LitInt ((x : ℕ) : ℤ))),
        state_upd_tapes (·.insert α ⟨z.toNat, xs⟩) σ, []) : expr × state × List expr))
        (dret ()) := by
    rw [dmap_dret]
    simp [head_step, H]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val (LitV (LitInt ((x : ℕ) : ℤ))))) $$ Hs Hj with
    ⟨Hs, Hj⟩
  imod spec_auth_update_tape ⟨z.toNat, xs⟩ _ _ α _ $$ Hs Htape with ⟨Hs, Htape⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe Hσ Hs Hε Hj
  iapply Hret $$ Htape

/-- Rocq: `pupd_rand_tape_empty`. -/
theorem pupd_rand_tape_empty (j : ℕ) (K : List ectx_item) (N : ℕ) (z : ℤ) (E : CoPset)
    (α : Loc) (hN : N = z.toNat) :
    j ⤇ fill K (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) ⊢@{IProp GF}
      α ↪ₛN (N; []) -∗ pupd E E iprop(∃ n : ℕ, ⌜n ≤ N⌝ ∗
        j ⤇ fill K (Val (LitV (LitInt (n : ℤ)))) ∗ α ↪ₛN (N; [])) := by
  subst hN
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro Hj Htape %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave Htape := spec_tapeN_to_empty α z.toNat $$ Htape
  ihave %H := spec_auth_lookup_tape es σ α _ _ $$ Hs Htape
  have Hhead : head_step (Rand (Val (LitV (LitInt z))) (Val (LitV (LitLbl α)))) σ =
      dmap (fun n : Fin (z.toNat + 1) => ((Val (LitV (LitInt ((n : ℕ) : ℤ))), σ, []) :
        expr × state × List expr)) (dunifP z.toNat) := by
    simp [head_step, H]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dunifP z.toNat) _ σ.tapes es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dunifP_mass _)) (dunifP_mass _) (fun _ => rfl)
  iintro %n
  imod spec_update_prog _ _ j _ (fill K (Val (LitV (LitInt ((n : ℕ) : ℤ))))) $$ Hs Hj with
    ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  iexists (n : ℕ)
  iframe Hj
  isplitr
  · ipureintro
    exact Nat.lt_succ_iff.1 n.2
  · iapply empty_to_spec_tapeN $$ Htape

/-- Rocq: `pupd_fork`. -/
theorem pupd_fork (E : CoPset) (K : List ectx_item) (e : expr) (j : ℕ) :
    j ⤇ fill K (Fork e) ⊢@{IProp GF}
      pupd E E iprop(j ⤇ fill K (Val (LitV LitUnit)) ∗ ∃ k, k ⤇ e) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro Hj %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  have Hhead : head_step (Fork e) σ =
      dmap (fun _ : Unit => ((Val (LitV LitUnit), σ, [e]) : expr × state × List expr))
        (dret ()) := by
    rw [dmap_dret]
    rfl
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val (LitV LitUnit))) $$ Hs Hj with ⟨Hs, Hj⟩
  imod spec_fork_prog _ _ e $$ Hs with ⟨Hs, Hk⟩
  imodintro
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_cmpxchg_fail`. -/
theorem pupd_cmpxchg_fail (E : CoPset) (K : List ectx_item) (l : Loc) (q : DFrac)
    (v v1 v2 : val) (j : ℕ) (Hsafe : vals_compare_safe v v1) (Hne : v ≠ v1) :
    j ⤇ fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) ∗ l ↦ₛ{q} v ⊢@{IProp GF}
      pupd E E iprop(j ⤇ fill K (Val (PairV v (LitV (LitBool false)))) ∗ l ↦ₛ{q} v) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro ⟨Hj, Hl⟩ %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave %H := spec_auth_lookup_heap es σ l v q $$ Hs Hl
  have Hhead : head_step (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) σ =
      dmap (fun _ : Unit => ((Val (PairV v (LitV (LitBool false))), σ, []) :
        expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    simp [head_step, H, Hsafe, Hne]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val (PairV v (LitV (LitBool false))))) $$ Hs Hj with
    ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_cmpxchg_suc`. -/
theorem pupd_cmpxchg_suc (E : CoPset) (K : List ectx_item) (l : Loc) (v v1 v2 : val) (j : ℕ)
    (Hsafe : vals_compare_safe v v1) (Heq : v = v1) :
    j ⤇ fill K (CmpXchg (Val (LitV (LitLoc l))) (Val v1) (Val v2)) ∗ l ↦ₛ v ⊢@{IProp GF}
      pupd E E iprop(j ⤇ fill K (Val (PairV v (LitV (LitBool true)))) ∗ l ↦ₛ v2) := by
  subst Heq
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro ⟨Hj, Hl⟩ %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave %H := spec_auth_lookup_heap es σ l v _ $$ Hs Hl
  have Hhead : head_step (CmpXchg (Val (LitV (LitLoc l))) (Val v) (Val v2)) σ =
      dmap (fun _ : Unit => ((Val (PairV v (LitV (LitBool true))),
        state_upd_heap (·.insert l v2) σ, []) : expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    simp [head_step, H, Hsafe]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val (PairV v (LitV (LitBool true))))) $$ Hs Hj with
    ⟨Hs, Hj⟩
  imod spec_auth_update_heap v2 _ _ l v $$ Hs Hl with ⟨Hs, Hl⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_xchg`. -/
theorem pupd_xchg (E : CoPset) (K : List ectx_item) (l : Loc) (v1 v2 : val) (j : ℕ) :
    j ⤇ fill K (Xchg (Val (LitV (LitLoc l))) (Val v2)) ∗ l ↦ₛ v1 ⊢@{IProp GF}
      pupd E E iprop(j ⤇ fill K (Val v1) ∗ l ↦ₛ v2) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro ⟨Hj, Hl⟩ %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave %H := spec_auth_lookup_heap es σ l v1 _ $$ Hs Hl
  have Hhead : head_step (Xchg (Val (LitV (LitLoc l))) (Val v2)) σ =
      dmap (fun _ : Unit => ((Val v1, state_upd_heap (·.insert l v2) σ, []) :
        expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    simp [head_step, H]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val v1)) $$ Hs Hj with ⟨Hs, Hj⟩
  imod spec_auth_update_heap v2 _ _ l v1 $$ Hs Hl with ⟨Hs, Hl⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_faa`. -/
theorem pupd_faa (E : CoPset) (K : List ectx_item) (l : Loc) (i1 i2 : ℤ) (j : ℕ) :
    j ⤇ fill K (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) ∗ l ↦ₛ LitV (LitInt i1)
      ⊢@{IProp GF} pupd E E iprop(j ⤇ fill K (Val (LitV (LitInt i1))) ∗
        l ↦ₛ LitV (LitInt (i1 + i2))) := by
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro ⟨Hj, Hl⟩ %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  ihave %H := spec_auth_lookup_heap es σ l _ _ $$ Hs Hl
  have Hhead : head_step (FAA (Val (LitV (LitLoc l))) (Val (LitV (LitInt i2)))) σ =
      dmap (fun _ : Unit => ((Val (LitV (LitInt i1)),
        state_upd_heap (·.insert l (LitV (LitInt (i1 + i2)))) σ, []) :
        expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    simp [head_step, H]
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_update_prog _ _ j _ (fill K (Val (LitV (LitInt i1)))) $$ Hs Hj with ⟨Hs, Hj⟩
  imod spec_auth_update_heap (LitV (LitInt (i1 + i2))) _ _ l _ $$ Hs Hl with ⟨Hs, Hl⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe

/-- Rocq: `pupd_alloc_tape`. -/
theorem pupd_alloc_tape (E : CoPset) (K : List ectx_item) (j : ℕ) (z : ℤ) (N : ℕ)
    (hN : N = z.toNat) :
    j ⤇ fill K (alloc (Val (LitV (LitInt z)))) ⊢@{IProp GF}
      pupd E E iprop(∃ α, α ↪ₛN (N; []) ∗ j ⤇ fill K (Val (LitV (LitLbl α)))) := by
  subst hN
  unfold pupd pupd_def
  simp only [foxtrotGS_spec_interp_eq]
  iintro Hj %σ1 %⟨es, σ⟩ %ε1 ⟨Hσ, Hs, Hε⟩
  ihave %Hsome := spec_auth_prog_agree es σ j _ $$ Hs Hj
  have Hhead : head_step (alloc (Val (LitV (LitInt z)))) σ =
      dmap (fun _ : Unit => ((Val (LitV (LitLbl (fresh_loc σ.tapes))),
        state_upd_tapes (·.insert (fresh_loc σ.tapes) ⟨z.toNat, []⟩) σ, []) :
        expr × state × List expr)) (dret ()) := by
    rw [dmap_dret]
    rfl
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  iapply spec_coupl_step_r_dmap (dret ()) _ _ es σ σ1 _ ε1 j _ Hsome
    (prim_step_fill_head K _ σ _ _ Hhead (dret_mass _)) (dret_mass _) (fun _ => rfl)
  iintro %_
  imod spec_auth_tape_alloc es σ z.toNat $$ Hs with ⟨Hs, Hα⟩
  imod spec_update_prog _ _ j _ (fill K (Val (LitV (LitLbl (fresh_loc σ.tapes))))) $$ Hs Hj with
    ⟨Hs, Hj⟩
  imodintro
  simp only [List.append_nil]
  iapply spec_coupl_ret_pair
  imod Hclose
  imodintro
  iframe Hσ Hs Hε
  iexists fresh_loc σ.tapes
  iframe Hj
  iapply empty_to_spec_tapeN $$ Hα

end lifting

end Foxtrot
