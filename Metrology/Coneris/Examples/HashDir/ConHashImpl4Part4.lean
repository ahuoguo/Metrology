module

public import Metrology.Coneris.Examples.HashDir.ConHashImpl4Part3
public import Iris.Std.GenSetsInstances

/-!
# A concurrent hash with per-key presampling tapes (part 4: the concurrent hash, interface)

Ported from clutch/theories/coneris/examples/hash/con_hash_impl4.v (from `compute_con_hash` to
the end; see `ConHashImpl4`, `ConHashImpl4Part2`, `ConHashImpl4Part3` for the general
mapping).

## Rocq → Lean mapping
* Programs (same names): `compute_con_hash`, `compute_con_hash_specialized`, `init_con_hash`.
  `acquire`/`release`/`newlock` are the operations of the lock `con_hash_lock` of `con_hashG`
  (Rocq: found through the `::` instance field, and explicit `(lock0 := con_hash_lock)` in
  `compute_con_hash_specialized`); here `H.con_hash_lock.acquire` etc., antiquoted.
* `conhashfun` (same name), with the instance `conhashfun_persistent`; `is_lock (L :=
  con_hash_lockG) γ lk R` is `H.con_hash_lock.is_lock H.con_hash_lockG γ lk R`.
* `wp_init_hash`: `keys : gset nat` is `keys : natset` (`Std.ExtTreeSet ℕ compare`, a
  `LawfulFiniteSet` in iris-lean), `dom tm` is `FiniteMap.dom_set tm`, `i < S max` is
  `i < max + 1`; `big_sepM_dom` is `BigSepM.bigSepM_dom`.
* `wp_init_hash_alt`: `[∗ set] k ∈ (set_seq 0 (S max)), P k` is
  `[∗list] k ∈ List.range (max + 1), P k` (as in `ConHashInterface4`); Rocq's
  `big_sepS_subseteq` is `BigSepS.bigSepS_subseteq` followed by `BigSepS.bigSepS_of_list`.
* `wp_conhashfun_prev`: same name.
* `Program Definition con_hash4_implements_interface4 : con_hash4 Σ` is the Lean
  `def con_hash4_implements_interface4 : con_hash4 GF` (not an instance, as in Rocq). The
  `Next Obligation` (`hashkey_presample`) is the helper `conhash_hashkey_presample`; the
  `Timeless`/`Persistent` fields are the instances `hashkey_timeless`,
  `conhashfun_persistent`, `haskey_persistent`.

## Added
* `natset`, `conhash_hashkey_presample` (the `Next Obligation` of
  `con_hash4_implements_interface4`).

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Map Coneris.Lib.Lock
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map nat_map_insert_eq)
open Coneris.Examples.HashDir.ConHashInterface4 (con_hash4)

namespace Coneris.Examples.HashDir.ConHashImpl4

/-- Rocq: `gset nat`. -/
abbrev natset : Type := Std.ExtTreeSet ℕ compare

section con_hash_impl

variable {GF : BundledGFunctors} [conerisGS GF] [H : con_hashG GF]

variable (GF) in
/-- Rocq: `compute_con_hash`. -/
def compute_con_hash : val :=
  cpl_val(λ lk hash v,
    &H.con_hash_lock.acquire lk;
    let output := hash v in
    &H.con_hash_lock.release lk;
    output)

/-- Rocq: `compute_con_hash_specialized`. -/
def compute_con_hash_specialized (lk hash : val) : val :=
  cpl_val(λ v,
    &H.con_hash_lock.acquire &lk;
    let output := &hash v in
    &H.con_hash_lock.release &lk;
    output)

variable (GF) in
/-- Rocq: `init_con_hash`. -/
def init_con_hash : val :=
  cpl_val(λ val_size max_val,
    let hash := &init_hash_state val_size max_val in
    let lk := &H.con_hash_lock.newlock #() in
    &(compute_con_hash GF) lk hash)

/-- Rocq: `conhashfun`. Concurrent hashfun, hiding as many details as possible. -/
def conhashfun (γs : GName × GName × GName) (val_size : ℕ) (f : val) : IProp GF :=
  iprop(∃ (γ : H.con_hash_lock.lock_name) (lk hash : val) (max : ℕ) (N : Namespace),
    ⌜f = compute_con_hash_specialized (GF := GF) lk hash⌝ ∗
    hashfunInv N γs val_size ∗
    H.con_hash_lock.is_lock H.con_hash_lockG γ lk (hashfun γs val_size max hash))

/-- Rocq: `conhashfun_persistent`. -/
instance conhashfun_persistent (γs : GName × GName × GName) (val_size : ℕ) (f : val) :
    Persistent (conhashfun (GF := GF) γs val_size f) := by
  unfold conhashfun; infer_instance

/-- Rocq: `wp_init_hash`. -/
theorem wp_init_hash (val_size max : ℕ) :
    {{ True }} cpl(&(init_con_hash GF) #val_size #max)
    {{ (keys : natset) (γs : GName × GName × GName) conhash, RET conhash;
        (conhashfun γs val_size conhash ∗
        ⌜∀ i : ℕ, i < max + 1 ↔ i ∈ keys⌝ ∗
        [∗set] k ∈ keys, hashkey γs k none : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold init_con_hash
  wp_pures
  wp_apply wp_init_hash_state nroot val_size max $$ [] with %γs %tm %hash ⟨Hfun, #HI, %Hdom, Hkeys⟩
  · itrivial
  wp_pures
  wp_apply H.con_hash_lock.newlock_spec H.con_hash_lockG _ $$ Hfun with %lk %γ #Hlk
  wp_pures
  unfold compute_con_hash
  wp_pures
  imodintro
  iapply HΦ $$ %(FiniteMap.dom_set tm) %γs
  isplitr
  · unfold conhashfun
    iexists γ, lk, hash, max, nroot
    iframe HI Hlk
    ipureintro
    rfl
  isplitr
  · ipureintro
    intro i
    rw [Hdom i, LawfulFiniteMap.mem_dom_set]
    exact Std.ExtTreeMap.mem_iff_isSome_getElem?
  iapply (BigSepM.bigSepM_dom (M := nat_map) (S := natset)).1
  iexact Hkeys

/-- Rocq: `wp_init_hash_alt`. -/
theorem wp_init_hash_alt (val_size max : ℕ) :
    {{ True }} cpl(&(init_con_hash GF) #val_size #max)
    {{ (γs : GName × GName × GName) conhash, RET conhash;
        (conhashfun γs val_size conhash ∗
        [∗list] k ∈ List.range (max + 1), hashkey γs k none : IProp GF) }} := by
  iintro %Φ - HΦ
  wp_apply wp_init_hash val_size max $$ [] with %keys %γs %conhash ⟨#Hf, %Hmax, Hkeys⟩
  · itrivial
  iapply HΦ
  iframe Hf
  iapply (BigSepS.bigSepS_of_list (S := natset) (List.nodup_range)).1
  iapply BigSepS.bigSepS_subseteq ?_ $$ Hkeys
  intro x Hx
  rw [← LawfulSet.mem_ofList, List.mem_range] at Hx
  exact (Hmax x).1 Hx

/-- Rocq: `wp_conhashfun_prev`. -/
theorem wp_conhashfun_prev (f : val) (k n : ℕ) (γs : GName × GName × GName) (val_size : ℕ) :
    {{ conhashfun γs val_size f ∗ hashkey γs k (some n) }} cpl(&f #k)
    {{ RET LitV (LitInt (n : ℤ)); (True : IProp GF) }} := by
  unfold conhashfun
  iintro %Φ ⟨#Hchf, #Hkey⟩ HΦ
  icases Hchf with ⟨%γ, %lk, %hash, %max, %N, %Hf, #HI, #Hlk⟩
  subst Hf
  unfold compute_con_hash_specialized
  wp_pures
  wp_apply H.con_hash_lock.acquire_spec H.con_hash_lockG γ lk _ $$ Hlk with ⟨Hlocked, Hfun⟩
  wp_pures
  wp_apply wp_hashfun_prev N ⊤ hash val_size max k n γs CoPset.subseteq_top
    $$ [Hfun] with Hfun
  · iframe HI Hfun Hkey
  wp_pures
  wp_apply H.con_hash_lock.release_spec H.con_hash_lockG γ lk _ $$ [Hlocked Hfun] with -
  · iframe Hlk Hlocked Hfun
  wp_pures
  iapply HΦ
  itrivial

/-- Rocq: the `Next Obligation` of `con_hash4_implements_interface4` (`hashkey_presample`). -/
theorem conhash_hashkey_presample (k : ℕ) (bad : Finset ℕ) (ε εI εO : ℝ≥0∞)
    (γs : GName × GName × GName) (val_size : ℕ) (f : val)
    (Hsize : ∀ x, x ∈ bad → x < val_size + 1)
    (Heps : εI * bad.card + εO * ((val_size : ℝ≥0∞) + 1 - bad.card) ≤
      ε * ((val_size : ℝ≥0∞) + 1)) :
    ⊢ conhashfun γs val_size f -∗ hashkey γs k none -∗ ↯ ε -∗
      state_update ⊤ ⊤ iprop(∃ n : Fin (val_size + 1),
        ((⌜(n : ℕ) ∉ bad⌝ ∗ ↯ εO) ∨ (⌜(n : ℕ) ∈ bad⌝ ∗ ↯ εI)) ∗
          (hashkey γs k (some (n : ℕ)) : IProp GF)) := by
  unfold conhashfun
  iintro #Hinv Hk Herr
  icases Hinv with ⟨%γ, %lk, %hash, %max, %N, -, #HI, -⟩
  iapply hashkey_presample N ⊤ val_size k bad ε εI εO γs CoPset.subseteq_top Hsize Heps
    $$ HI Hk Herr

end con_hash_impl

section con_hash_interface_impl

variable {GF : BundledGFunctors} [conerisGS GF] [H : con_hashG GF]

/-- Rocq: `con_hash4_implements_interface4`. -/
@[instance_reducible]
def con_hash4_implements_interface4 : con_hash4 GF where
  init_con_hash := init_con_hash GF
  conhashfun := conhashfun
  hashkey := hashkey
  hashkey_timeless _ _ _ := inferInstance
  conhashfun_persistent _ _ _ := inferInstance
  hashkey_Some_persistent _ _ _ := inferInstance
  hashkey_presample := conhash_hashkey_presample
  conhash_init := wp_init_hash_alt
  wp_conhashfun_prev := wp_conhashfun_prev

end con_hash_interface_impl

end Coneris.Examples.HashDir.ConHashImpl4
