module

public import Metrology.Coneris.ErrorRules
public import Iris.Instances.Lib.Invariants

/-!
# A concurrent interface for hash functions with presampling for individual keys

Ported from clutch/theories/coneris/examples/hash/con_hash_interface4.v

## Rocq → Lean mapping
* `Class con_hash4 Σ `{!conerisGS Σ} := Con_Hash4 {...}` is the Lean
  `class con_hash4 GF [conerisGS GF]` with the same field names: `init_con_hash`,
  `conhashfun`, `hashkey`, the `#[global]` instance fields `hashkey_timeless`,
  `conhashfun_persistent`, `hashkey_Some_persistent` (re-exported as global instances
  `con_hash4_*`), and `hashkey_presample`, `conhash_init`, `wp_conhashfun_prev`.
  - `gname` is iris-lean's `GName`.
  - `P -∗ Q` fields are stated as `⊢ P -∗ Q`.
  - `hashkey_presample`: `bad : gset nat` is `bad : Finset ℕ`, `size bad` is `bad.card`;
    `ε εI εO : nonnegreal` are `ℝ≥0∞`; the real subtraction `val_size + 1 - size bad` is the
    truncated `ℝ≥0∞` one, which does not truncate since every element of `bad` is
    `< val_size + 1` (so `bad.card ≤ val_size + 1`). `fin (S val_size)` is `Fin (val_size + 1)`.
  - `conhash_init`: `[∗ set] k ∈ (set_seq 0 (S max)), P k` is
    `[∗list] k ∈ List.range (max + 1), P k` (stdpp's `set_seq 0 (S max)` is the set of the
    duplicate-free list `seq 0 (S max) = List.range (max + 1)`, and `big_sepS_list_to_set`
    identifies the two big separating conjunctions).
  - Texan triples are iris-lean's (mask `⊤`); `#val_size`, `#k` are `#val_size`, `#k`;
    `RET #n` is `RET LitV (LitInt (n : ℤ))`; the two binders `γs conhash` are kept.
* Section `derived_lemmas`: `wp_hash_lookup_safe`, `wp_hash_lookup_avoid_set` (same names).
  `ec_zero` is `ErrorCredit.zero`; `nnreal_zero` is `0`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Examples.HashDir.ConHashInterface4

/-- Rocq: `con_hash4`. A concurrent interface for hash functions with presampling for
individual keys. -/
class con_hash4 (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  init_con_hash : val
  -- * Predicates
  conhashfun (γs : GName × GName × GName) (val_size : ℕ) (f : val) : IProp GF
  hashkey (γs : GName × GName × GName) (k : ℕ) (v : Option ℕ) : IProp GF
  -- * General properties of the predicates
  hashkey_timeless (γs : GName × GName × GName) (k : ℕ) (v : Option ℕ) :
    Timeless (hashkey γs k v)
  conhashfun_persistent (γs : GName × GName × GName) (vs : ℕ) (f : val) :
    Persistent (conhashfun γs vs f)
  hashkey_Some_persistent (γs : GName × GName × GName) (k v : ℕ) :
    Persistent (hashkey γs k (some v))
  hashkey_presample (k : ℕ) (bad : Finset ℕ) (ε εI εO : ℝ≥0∞) (γs : GName × GName × GName)
    (val_size : ℕ) (f : val) :
    (∀ x, x ∈ bad → x < val_size + 1) →
    εI * bad.card + εO * ((val_size : ℝ≥0∞) + 1 - bad.card) ≤ ε * ((val_size : ℝ≥0∞) + 1) →
    ⊢ conhashfun γs val_size f -∗
      hashkey γs k none -∗
      ↯ ε -∗
      state_update ⊤ ⊤ iprop(∃ n : Fin (val_size + 1),
        ((⌜(n : ℕ) ∉ bad⌝ ∗ ↯ εO) ∨ (⌜(n : ℕ) ∈ bad⌝ ∗ ↯ εI)) ∗
        hashkey γs k (some (n : ℕ)))
  conhash_init (val_size max : ℕ) :
    {{ True }} cpl(&init_con_hash #val_size #max)
    {{ γs conhash, RET conhash;
        conhashfun γs val_size conhash ∗
        [∗list] k ∈ List.range (max + 1), hashkey γs k none }}
  wp_conhashfun_prev (f : val) (k n : ℕ) (γs : GName × GName × GName) (val_size : ℕ) :
    {{ conhashfun γs val_size f ∗ hashkey γs k (some n) }} cpl(&f #k)
    {{ RET LitV (LitInt (n : ℤ)); True }}

section instances

variable {GF : BundledGFunctors} [conerisGS GF] [c : con_hash4 GF]

instance con_hash4_hashkey_timeless (γs : GName × GName × GName) (k : ℕ) (v : Option ℕ) :
    Timeless (c.hashkey γs k v) := c.hashkey_timeless γs k v
instance con_hash4_conhashfun_persistent (γs : GName × GName × GName) (vs : ℕ) (f : val) :
    Persistent (c.conhashfun γs vs f) := c.conhashfun_persistent γs vs f
instance con_hash4_hashkey_Some_persistent (γs : GName × GName × GName) (k v : ℕ) :
    Persistent (c.hashkey γs k (some v)) := c.hashkey_Some_persistent γs k v

end instances

section derived_lemmas

variable {GF : BundledGFunctors} [conerisGS GF] [c : con_hash4 GF]

/-- Rocq: `wp_hash_lookup_safe`. -/
theorem wp_hash_lookup_safe (k : ℕ) (f : val) (γs : GName × GName × GName) (val_size : ℕ) :
    {{ c.hashkey γs k none ∗ c.conhashfun γs val_size f }} cpl(&f #k)
    {{ (v : ℕ), RET LitV (LitInt (v : ℤ)); ⌜v ≤ val_size⌝ ∗ c.hashkey γs k (some v) }} := by
  iintro %Φ ⟨HNone, #Hinv⟩ HΦ
  imod ErrorCredit.zero (GF := GF) with Herr
  iapply state_update_pgl_wp
  imod c.hashkey_presample k ∅ 0 0 0 γs val_size f (by simp) (by simp) $$ Hinv HNone Herr
    with ⟨%v, -, #Hkey⟩
  imodintro
  wp_apply c.wp_conhashfun_prev f k v γs val_size $$ [] with -
  · iframe Hinv Hkey
  iapply HΦ
  iframe Hkey
  ipureintro
  exact Nat.le_of_lt_succ v.isLt

/-- Rocq: `wp_hash_lookup_avoid_set`. -/
theorem wp_hash_lookup_avoid_set (k : ℕ) (f : val) (γs : GName × GName × GName)
    (bad : Finset ℕ) (ε εI εO : ℝ≥0∞) (val_size : ℕ)
    (Hbad : ∀ x : ℕ, x ∈ bad → x < val_size + 1)
    (Hdistr : εI * bad.card + εO * ((val_size : ℝ≥0∞) + 1 - bad.card) ≤
      ε * ((val_size : ℝ≥0∞) + 1)) :
    {{ ↯ ε ∗ c.hashkey γs k none ∗ c.conhashfun γs val_size f }} cpl(&f #k)
    {{ (v : ℕ), RET LitV (LitInt (v : ℤ));
        ⌜v ≤ val_size⌝ ∗
        ((⌜v ∈ bad⌝ ∗ ↯ εI) ∨ (⌜v ∉ bad⌝ ∗ ↯ εO)) ∗
        c.hashkey γs k (some v) }} := by
  iintro %Φ ⟨Herr, Hnone, #Hinv⟩ HΦ
  iapply state_update_pgl_wp
  imod c.hashkey_presample k bad ε εI εO γs val_size f Hbad Hdistr $$ Hinv Hnone Herr
    with ⟨%v, Hv, #Hhauth⟩
  imodintro
  wp_apply c.wp_conhashfun_prev f k v γs val_size $$ [] with -
  · iframe Hinv Hhauth
  iapply HΦ
  iframe Hhauth
  isplitr
  · ipureintro
    exact Nat.le_of_lt_succ v.isLt
  icases Hv with (⟨%H, Herr⟩ | ⟨%H, Herr⟩)
  · iright
    iframe Herr
    ipureintro
    exact H
  · ileft
    iframe Herr
    ipureintro
    exact H

end derived_lemmas

end Coneris.Examples.HashDir.ConHashInterface4
