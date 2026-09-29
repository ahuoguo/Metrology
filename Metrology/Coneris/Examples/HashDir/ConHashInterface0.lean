module

public import Metrology.Coneris.Examples.HashDir.HashViewInterface
public import Metrology.Coneris.ErrorRules
public import Iris.Instances.Lib.Invariants

/-!
# A concurrent hash interface (version 0)

Ported from clutch/theories/coneris/examples/hash/con_hash_interface0.v

## Rocq → Lean mapping
* `Class con_hash0 `{!conerisGS Σ} (val_size:nat) := Con_Hash0 {...}` is the Lean
  `class con_hash0 GF [conerisGS GF] (val_size : ℕ)` with the same field names:
  `init_hash0`, `allocate_tape0`, `compute_hash0`, `hash_tape_gname`, `hash_lock_gname`,
  `con_hash_inv0`, `hash_tape0`, `hash_tape_timeless`, `con_hash_inv_persistent`,
  `hash_tape_valid`, `hash_tape_exclusive`, `hash_tape_presample`, `con_hash_init0`,
  `con_hash_alloc_tape0`, `con_hash_spec0`.
  - The instance argument `{HR : ∀ m, Timeless (R m)}` is an instance-implicit argument
    `[HR : ∀ m, Timeless (R m)]`.
  - The `#[global] ... ::` instance fields are re-exported as the global instances
    `con_hash0_hash_tape_timeless`, `con_hash0_con_hash_inv_persistent`.
  - `P -∗ Q` fields are stated as `⊢ P -∗ Q`; `namespace` is iris-lean's `Namespace`,
    `↑N ⊆ E` is `↑N ⊆ E`.
  - `Forall (λ x, x <= val_size) ns` is `∀ x ∈ ns, x ≤ val_size`.
  - Errors are `ℝ≥0∞`: the hypothesis `∀ x, 0 <= ε2 x` of `hash_tape_presample` is dropped
    (automatic), `SeriesC (λ n, 1 / S val_size * ε2 n) <= ε` is
    `∑' n, 1 / ((val_size : ℝ≥0∞) + 1) * ε2 n ≤ ε` (as in `Coneris.Lib.HocapRand`);
    `fin (S val_size)` is `Fin (val_size + 1)`, `fin_to_nat n` is `(n : ℕ)`.
  - `gmap nat nat` is `hmap`, `m !! v` is `m[v]?`, `<[v:=n]> m` is `m.insert v n`.
  - Texan triples `{{{ P }}} e {{{ x, RET v; Q }}}` are iris-lean's `{{ P }} e {{ x, RET v; Q }}`
    (mask `⊤`); `f #v α` (`v : nat`, `α : val`) is `cpl(&f #v &α)`; `RET (#res)` is
    `RET LitV (LitInt (res : ℤ))`.

## Omitted
Nothing.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)

namespace Coneris.Examples.HashDir.ConHashInterface0

/-- Rocq: `con_hash0`. -/
class con_hash0 (GF : BundledGFunctors) [conerisGS GF] (val_size : ℕ) where
  -- * Operations
  init_hash0 : val
  allocate_tape0 : val
  compute_hash0 : val
  -- * Ghost state
  hash_tape_gname : Type
  hash_lock_gname : Type
  -- * Predicates
  con_hash_inv0 (N : Namespace) (f l hm : val) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)]
    (γ : hash_tape_gname) (γ_lock : hash_lock_gname) : IProp GF
  hash_tape0 (α : val) (ns : List ℕ) (γ : hash_tape_gname) : IProp GF
  -- * General properties of the predicates
  hash_tape_timeless (α : val) (ns : List ℕ) (γ : hash_tape_gname) : Timeless (hash_tape0 α ns γ)
  con_hash_inv_persistent (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : hash_tape_gname) (γ_lock : hash_lock_gname) :
    Persistent (con_hash_inv0 N f l hm R γ_tape γ_lock)
  hash_tape_valid (α : val) (ns : List ℕ) (γ : hash_tape_gname) :
    ⊢ hash_tape0 α ns γ -∗ ⌜∀ x ∈ ns, x ≤ val_size⌝
  hash_tape_exclusive (α : val) (ns ns' : List ℕ) (γ : hash_tape_gname) :
    ⊢ hash_tape0 α ns γ -∗ hash_tape0 α ns' γ -∗ False
  hash_tape_presample (N : Namespace) (γ : hash_tape_gname) (γ_lock : hash_lock_gname)
    (f l hm : val) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] (α : val) (ns : List ℕ)
    (ε : ℝ≥0∞) (ε2 : Fin (val_size + 1) → ℝ≥0∞) (E : CoPset) :
    ↑N ⊆ E →
    ∑' n : Fin (val_size + 1), 1 / ((val_size : ℝ≥0∞) + 1) * ε2 n ≤ ε →
    ⊢ con_hash_inv0 N f l hm R γ γ_lock -∗
      hash_tape0 α ns γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        ↯ (ε2 n) ∗ hash_tape0 α (ns ++ [(n : ℕ)]) γ)
  con_hash_init0 (N : Namespace) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] :
    {{ R ∅ }} cpl(&init_hash0 #())
    {{ (f : val), RET f; ∃ l hm γ_tape γ_lock, con_hash_inv0 N f l hm R γ_tape γ_lock }}
  con_hash_alloc_tape0 (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : hash_tape_gname) (γ_lock : hash_lock_gname) :
    {{ con_hash_inv0 N f l hm R γ_tape γ_lock }} cpl(&allocate_tape0 #())
    {{ (α : val), RET α; hash_tape0 α [] γ_tape }}
  con_hash_spec0 (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : hash_tape_gname) (γ_lock : hash_lock_gname)
    (Q1 : ℕ → IProp GF) (Q2 : ℕ → List ℕ → IProp GF) (α : val) (v : ℕ) :
    {{ con_hash_inv0 N f l hm R γ_tape γ_lock ∗
        (∀ m, R m -∗ state_update ⊤ ⊤
          (match m[v]? with
           | some res => iprop(R m ∗ Q1 res)
           | none => iprop(∃ n ns, hash_tape0 α (n :: ns) γ_tape ∗
                (hash_tape0 α ns γ_tape ={⊤}=∗ R (m.insert v n) ∗ Q2 n ns)))) }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); Q1 res ∨ ∃ ns, Q2 res ns }}

section instances

variable {GF : BundledGFunctors} [conerisGS GF] {val_size : ℕ} [c : con_hash0 GF val_size]

/-- Rocq: the instance field `hash_tape_timeless`. -/
instance con_hash0_hash_tape_timeless (α : val) (ns : List ℕ) (γ : c.hash_tape_gname) :
    Timeless (c.hash_tape0 α ns γ) := c.hash_tape_timeless α ns γ

/-- Rocq: the instance field `con_hash_inv_persistent`. -/
instance con_hash0_con_hash_inv_persistent (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_tape : c.hash_tape_gname) (γ_lock : c.hash_lock_gname) :
    Persistent (c.con_hash_inv0 N f l hm R γ_tape γ_lock) :=
  c.con_hash_inv_persistent N f l hm R γ_tape γ_lock

end instances

end Coneris.Examples.HashDir.ConHashInterface0
