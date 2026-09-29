module

public import Metrology.Coneris.Examples.HashDir.ConHashInterface3
public import Metrology.Coneris.Lib.Par
public import Iris.Algebra.Lib.ExclAuth

/-!
# A race on hashing the same key

Ported from clutch/theories/coneris/examples/hash/hash_race.v

Two threads hash the key `0` with the same (concurrent, amortized) hash function; both obtain
the same hash value.

## Rocq → Lean mapping
* Section `lemmas`: the context `inG Σ (excl_authR boolO)` is `[ElemG GF excl_authTF]` with
  `excl_authTF := constOF (ExclAuthR (A := boolO))` and `boolO := DiscreteO Bool` (Rocq:
  `leibnizO bool`). `own γ (●E b)` is `iOwn (F := excl_authTF) γ (●E ⟨b⟩)`. `ghost_var_alloc`,
  `ghost_var_agree`, `ghost_var_update`: same names; `P -∗ Q ==∗ R` is `⊢ P -∗ Q ==∗ R`.
* Section `race`: the section variables `val_size max_hash_size`, `Hpos` and the context
  `conerisGS Σ, spawnG Σ, c : con_hash3 Σ val_size max_hash_size Hpos, inG Σ (excl_authR boolO)`
  are implicit arguments `{val_size max_hash_size} {Hpos}` and instances
  `[conerisGS GF] [spawnG GF] [c : con_hash3 GF val_size max_hash_size Hpos]
  [ElemG GF excl_authTF]`. `race_prog`, `race_prog_spec`: same names.
* The expression-scope `e1 ||| e2` of `race_prog` (Rocq: `par (λ: <>, e1)%E (λ: <>, e2)%E`) is
  the local program notation `e1 ‖ e2` (inside `cpl(...)`, `|||` is the bitwise `or`); after
  the pure steps it is the value-scope form of `wp_par` (the helper `wp_par'`), as in Rocq.
* The invariant predicate `λ m, if bool_decide (m !! 0 = None) then own γ (◯E false) else
  own γ (◯E true)` is the helper `race_R γ m` (with a decidable `if`), so that its `Timeless`
  instance is found; the invariant `Hinv2` is the helper `race_inv`.
* `Local Opaque amortized_error`: not needed (`amortized_error` is never unfolded here).
* `nroot.@"1"` is `nroot.@"1"`; `subseteq_difference_r` + `ndot_ne_disjoint` is the helper
  `ndot_subseteq_top_diff`.
* `destruct max_hash_size as [|n]` + `hash_token_split` (to get one token out of
  `hash_token3 max_hash_size`) is `hash_token_split (max_hash_size - 1) 1` with
  `max_hash_size - 1 + 1 = max_hash_size` (from `Hpos`).
* `RET (#z,#z)%Z` is `RET PairV (LitV (LitInt z)) (LitV (LitInt z))`.

## Proofs that differ from Rocq
The two threads of `race_prog_spec` have literally the same Rocq proof; here it is proved once,
in the helper `race_thread_spec`. The Rocq `iDestruct (hash_auth_duplicate with "[$]") as "#?"`
keeps `hash_auth3` (the conclusion is persistent); here this is the helper
`hash_auth_duplicate'`.

## Added
* Helpers `boolO`, `excl_authTF`, `wp_par'`, `ndot_subseteq_top_diff`, `hash_auth_duplicate'`,
  `race_R`, `race_inv`, `race_thread_spec`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)
open Coneris.Examples.HashDir.ConHashInterface3
open Iris.ExclAuth

namespace Coneris.Examples.HashDir.HashRace

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

variable {val_size max_hash_size : ℕ} {Hpos : 0 < max_hash_size}
variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF]
  [c : con_hash3 GF val_size max_hash_size Hpos] [ElemG GF excl_authTF]

/-- Rocq: `race_prog`. -/
def race_prog : expr := cpl(
  let h := v(&c.init_hash3) #() in
  (h #0 (v(&c.allocate_tape3) #()))
  ‖
  (h #0 (v(&c.allocate_tape3) #())))

/-- Helper: the Rocq `iDestruct (hash_auth_duplicate with "[$]") as "#?"`, which keeps
`hash_auth3` since the conclusion is persistent. -/
theorem hash_auth_duplicate' (m : hmap) (k v : ℕ) (γ : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ4 : c.hash_view_gname') (γ5 : c.hash_set_gname')
    (H : m[k]? = some v) :
    c.hash_auth3 m γ γ2 γ4 γ5 ⊢ c.hash_auth3 m γ γ2 γ4 γ5 ∗ c.hash_frag3 k v γ γ2 γ4 :=
  persistent_entails_left (wand_entails (c.hash_auth_duplicate m k v γ γ2 γ4 γ5 H))

/-- Helper: the predicate `R` of the hash invariant in `race_prog_spec` (Rocq: the lambda
`λ m, if bool_decide (m !! 0 = None) then own γ (◯E false) else own γ (◯E true)`). -/
def race_R (γ : GName) (m : hmap) : IProp GF :=
  if m[0]? = none then iOwn (F := excl_authTF) γ (◯E (⟨false⟩ : boolO))
  else iOwn (F := excl_authTF) γ (◯E (⟨true⟩ : boolO))

instance race_R_timeless (γ : GName) (m : hmap) : Timeless (race_R (GF := GF) γ m) := by
  unfold race_R; split <;> infer_instance

theorem race_R_none (γ : GName) (m : hmap) (H : m[0]? = none) :
    race_R (GF := GF) γ m = iOwn (F := excl_authTF) γ (◯E (⟨false⟩ : boolO)) := by
  simp [race_R, H]

theorem race_R_some (γ : GName) (m : hmap) (x : ℕ) (H : m[0]? = some x) :
    race_R (GF := GF) γ m = iOwn (F := excl_authTF) γ (◯E (⟨true⟩ : boolO)) := by
  simp [race_R, H]

/-- Helper: the invariant `Hinv2` of `race_prog_spec`. -/
def race_inv (γ : GName) (γ_token : c.hash_token_gname) : IProp GF :=
  iprop((iOwn (F := excl_authTF) γ (●E (⟨false⟩ : boolO)) ∗
      c.hash_token3 max_hash_size γ_token ∗ ↯ (amortized_error val_size max_hash_size Hpos)) ∨
    iOwn (F := excl_authTF) γ (●E (⟨true⟩ : boolO)))

/-- Helper: the proof of either thread of `race_prog_spec` (Rocq: the first two bullets). -/
theorem race_thread_spec (f l hm : val) (γ : GName) (γ1 : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname) (γ4 : c.hash_view_gname')
    (γ5 : c.hash_set_gname') (γ_token : c.hash_token_gname) (γ_lock : c.hash_lock_gname) :
    ⊢ c.con_hash_inv3 (nroot.@"1") f l hm (race_R γ) γ1 γ2 γ3 γ4 γ5 γ_token γ_lock -∗
      inv (nroot.@"inv") (race_inv γ γ_token) -∗
      WP cpl(&f #0 (v(&c.allocate_tape3) #()))
        {{ res, ∃ res' : ℕ, ⌜LitV (LitInt (res' : ℤ)) = res⌝ ∗ c.hash_frag3 0 res' γ1 γ2 γ4 }} := by
  iintro #Hinv1 #Hinv2
  wp_apply c.con_hash_alloc_tape3 (nroot.@"1") f l hm (race_R γ) γ1 γ2 γ3 γ4 γ5 γ_token γ_lock
    $$ Hinv1 with %α Ht
  wp_apply c.con_hash_spec3 (nroot.@"1") f l hm (race_R γ) γ1 γ2 γ3 γ4 γ5 γ_token γ_lock
    (fun res => c.hash_frag3 0 res γ1 γ2 γ4) (fun res _ => c.hash_frag3 0 res γ1 γ2 γ4) α 0
    $$ [Ht] with %res HQ
  · isplitr
    · iexact Hinv1
    iintro %m Hfrag Hhauth
    cases H : m[0]? with
    | none =>
      rw [race_R_none γ m H]
      dsimp only
      iapply state_update_inv_acc _ ⊤ _ (nroot.@"inv") CoPset.subseteq_top $$ Hinv2
      unfold race_inv
      iintro >(⟨Hauth, Htoken, Herr⟩ | Hauth)
      · obtain ⟨n', hn'⟩ : ∃ n', max_hash_size = n' + 1 := ⟨max_hash_size - 1, by omega⟩
        have Hs := c.hash_token_split n' 1 γ_token
        rw [← hn'] at Hs
        icases Hs.1 $$ Htoken with ⟨Htoken, Htoken1⟩
        imod c.hash_tape_presample (nroot.@"1") f l hm (race_R γ) γ1 γ2 γ4 γ_token γ3 γ5
          γ_lock α [] (⊤ \ ↑(nroot.@"inv")) ndot_subseteq_top_diff $$ Hinv1 Ht Herr Htoken1
          with ⟨%n, Ht, Hsf⟩
        rw [List.nil_append]
        imod ghost_var_update γ true false false $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
        imodintro
        isplitl [Ht Hsf Hhauth Hfrag]
        · iexists (n : ℕ), []
          iframe Ht
          iintro _Ht
          imod c.hash_auth_insert m 0 n γ1 γ2 γ4 γ5 H $$ Hsf Hhauth with Hhauth
          ihave ⟨Hhauth, #Hf⟩ := hash_auth_duplicate' (m.insert 0 n) 0 n γ1 γ2 γ4 γ5
            (by simp) $$ Hhauth
          imodintro
          iframe Hhauth Hf
          rw [race_R_some γ (m.insert 0 n) n (by simp)]
          iexact Hfrag
        · inext
          iright
          iexact Hauth
      · ihave %Hc := ghost_var_agree $$ Hauth Hfrag
        simp at Hc
    | some res =>
      dsimp only
      ihave ⟨Hhauth, #Hf⟩ := hash_auth_duplicate' m 0 res γ1 γ2 γ4 γ5 H $$ Hhauth
      imodintro
      iframe Hhauth Hf Hfrag
  · iexists res
    isplitr
    · ipureintro
      rfl
    icases HQ with (#Hf | ⟨%ns, #Hf⟩) <;> iexact Hf

/-- Rocq: `race_prog_spec`. -/
theorem race_prog_spec :
    {{ ↯ (amortized_error val_size max_hash_size Hpos) }} (race_prog (c := c))
    {{ (z : ℤ), RET PairV (LitV (LitInt z)) (LitV (LitInt z)); (True : IProp GF) }} := by
  iintro %Φ Herr HΦ
  unfold race_prog
  imod ghost_var_alloc false with ⟨%γ, Hauth, Hfrag⟩
  wp_apply c.con_hash_init3 (nroot.@"1") (race_R γ) $$ [Hfrag]
    with %f ⟨%l, %hm, %γ1, %γ2, %γ3, %γ4, %γ5, %γ_token, %γ_lock, #Hinv1, Htoken⟩
  · rw [race_R_none γ ∅ (by simp)]
    iexact Hfrag
  imod inv_alloc (nroot.@"inv") ⊤ (race_inv γ γ_token) $$ [Herr Hauth Htoken] with #Hinv2
  · inext
    unfold race_inv
    ileft
    iframe
  wp_pures
  wp_apply wp_par'
    (fun res => iprop(∃ res' : ℕ, ⌜LitV (LitInt (res' : ℤ)) = res⌝ ∗ c.hash_frag3 0 res' γ1 γ2 γ4))
    (fun res => iprop(∃ res' : ℕ, ⌜LitV (LitInt (res' : ℤ)) = res⌝ ∗ c.hash_frag3 0 res' γ1 γ2 γ4))
    $$ [] []
  · iapply race_thread_spec f l hm γ γ1 γ2 γ3 γ4 γ5 γ_token γ_lock $$ Hinv1 Hinv2
  · iapply race_thread_spec f l hm γ γ1 γ2 γ3 γ4 γ5 γ_token γ_lock $$ Hinv1 Hinv2
  iintro %v1 %v2 ⟨⟨%res, %H1, #Hf1⟩, ⟨%res', %H2, #Hf2⟩⟩
  subst H1 H2
  ihave %K := c.hash_frag_frag_agree 0 0 res res' γ1 γ2 γ4 $$ Hf1 Hf2
  obtain rfl : res = res' := K.1 rfl
  iapply HΦ
  inext
  itrivial

end race

end Coneris.Examples.HashDir.HashRace
