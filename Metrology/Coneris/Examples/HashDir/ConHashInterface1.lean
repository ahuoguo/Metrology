module

public import Metrology.Coneris.Examples.HashDir.HashViewInterface
public import Metrology.Coneris.ErrorRules
public import Iris.Instances.Lib.Invariants

/-!
# A concurrent hash interface (version 1)

Ported from clutch/theories/coneris/examples/hash/con_hash_interface1.v

## Rocq → Lean mapping
* `Class con_hash1 `{!conerisGS Σ} (val_size:nat) := Con_Hash1 {...}` is the Lean
  `class con_hash1 GF [conerisGS GF] (val_size : ℕ)` with the same field names:
  `init_hash1`, `allocate_tape1`, `compute_hash1`, `hash_view_gname`, `hash_set_gname`,
  `hash_tape_gname`, `hash_lock_gname`, `con_hash_inv1`, `hash_tape1`, `hash_auth1`,
  `hash_frag1`, `hash_set1`, `hash_set_frag1`, the `#[global]` instance fields
  `hash_tape_timeless`, `hash_auth_timeless`, `hash_frag_timeless`, `hash_set_timeless`,
  `hash_set_frag_timeless`, `con_hash_inv_persistent`, `hash_frag_persistent`,
  `hash_set_frag_persistent` (re-exported as global instances `con_hash1_*`), and
  `hash_auth_exclusive`, `hash_auth_frag_agree`, `hash_auth_duplicate`,
  `hash_frag_frag_agree`, `hash_frag_in_hash_set`, `hash_tape_in_hash_set`,
  `hash_set_duplicate`, `hash_set_frag_in_set`, `hash_auth_insert`, `hash_set_valid`,
  `hash_tape_valid`, `hash_tape_exclusive`, `hash_tape_presample`, `con_hash_init1`,
  `con_hash_alloc_tape1`, `con_hash_spec1`.
  - The instance argument `{HR : ∀ m, Timeless (R m)}` is `[HR : ∀ m, Timeless (R m)]`.
  - `P -∗ Q` fields are stated as `⊢ P -∗ Q` (or `⊢ P ==∗ Q`).
  - `gset nat` is `Finset ℕ`, `size bad` is `bad.card`, `s ∪ {[x]}` is `s ∪ {x}`.
  - `Forall (λ x, x <= val_size) ns` is `∀ x ∈ ns, x ≤ val_size`.
  - `hash_tape_presample`: `ε εI εO : nonnegreal` are `ℝ≥0∞`; the real subtraction
    `val_size + 1 - size bad` is the truncated `ℝ≥0∞` one, which does not truncate since
    every element of `bad` is `< val_size + 1` (so `bad.card ≤ val_size + 1`).
  - `gmap nat nat` is `hmap`, `m !! v` is `m[v]?`, `<[v:=n]> m` is `m.insert v n`.
  - Texan triples are iris-lean's (mask `⊤`); `f #v α` is `cpl(&f #v &α)`.
* Section `test`: `con_hash_spec_test1`, `con_hash_spec_hashed_before1` (same names), over
  `[c : con_hash1 GF val_size]`. Rocq's `iDestruct (lem with "[$]") as "#H"` for a persistent
  conclusion (which keeps the framed hypotheses) is `persistent_entails_left`.

## Omitted
* The commented-out `iDestruct` in `con_hash_spec_hashed_before1`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)

namespace Coneris.Examples.HashDir.ConHashInterface1

/-- Rocq: `con_hash1`. -/
class con_hash1 (GF : BundledGFunctors) [conerisGS GF] (val_size : ℕ) where
  -- * Operations
  init_hash1 : val
  allocate_tape1 : val
  compute_hash1 : val
  -- * Ghost state
  hash_view_gname : Type
  hash_set_gname : Type
  hash_tape_gname : Type
  hash_lock_gname : Type
  -- * Predicates
  con_hash_inv1 (N : Namespace) (f l hm : val) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)]
    (γ1 : hash_view_gname) (γ2 : hash_set_gname) (γ3 : hash_tape_gname)
    (γ_lock : hash_lock_gname) : IProp GF
  hash_tape1 (α : val) (ns : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) : IProp GF
  hash_auth1 (m : hmap) (γ : hash_view_gname) (γ2 : hash_set_gname) : IProp GF
  hash_frag1 (v res : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname) : IProp GF
  hash_set1 (s : Finset ℕ) (γ2 : hash_set_gname) : IProp GF
  hash_set_frag1 (n : ℕ) (γ2 : hash_set_gname) : IProp GF
  -- * General properties of the predicates
  hash_tape_timeless (α : val) (ns : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) :
    Timeless (hash_tape1 α ns γ2 γ3)
  hash_auth_timeless (m : hmap) (γ : hash_view_gname) (γ2 : hash_set_gname) :
    Timeless (hash_auth1 m γ γ2)
  hash_frag_timeless (v res : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname) :
    Timeless (hash_frag1 v res γ γ2)
  hash_set_timeless (s : Finset ℕ) (γ2 : hash_set_gname) : Timeless (hash_set1 s γ2)
  hash_set_frag_timeless (s : ℕ) (γ2 : hash_set_gname) : Timeless (hash_set_frag1 s γ2)
  con_hash_inv_persistent (N : Namespace) (f l hm : val) (γ1 : hash_view_gname)
    (γ2 : hash_set_gname) (γ3 : hash_tape_gname) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_lock : hash_lock_gname) :
    Persistent (con_hash_inv1 N f l hm R γ1 γ2 γ3 γ_lock)
  hash_frag_persistent (v res : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname) :
    Persistent (hash_frag1 v res γ γ2)
  hash_set_frag_persistent (s : ℕ) (γ2 : hash_set_gname) : Persistent (hash_set_frag1 s γ2)
  hash_auth_exclusive (m m' : hmap) (γ : hash_view_gname) (γ2 : hash_set_gname) :
    ⊢ hash_auth1 m γ γ2 -∗ hash_auth1 m' γ γ2 -∗ False
  hash_auth_frag_agree (m : hmap) (k v : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname) :
    ⊢ hash_auth1 m γ γ2 -∗ hash_frag1 k v γ γ2 -∗ ⌜m[k]? = some v⌝
  hash_auth_duplicate (m : hmap) (k v : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname) :
    m[k]? = some v → ⊢ hash_auth1 m γ γ2 -∗ hash_frag1 k v γ γ2
  hash_frag_frag_agree (k v1 v2 : ℕ) (γ : hash_view_gname) (γ2 : hash_set_gname) :
    ⊢ hash_frag1 k v1 γ γ2 -∗ hash_frag1 k v2 γ γ2 -∗ ⌜v1 = v2⌝
  hash_frag_in_hash_set (γ1 : hash_view_gname) (γ2 : hash_set_gname) (v res : ℕ) :
    ⊢ hash_frag1 v res γ1 γ2 -∗ hash_set_frag1 res γ2
  hash_tape_in_hash_set (α : val) (ns : List ℕ) (γ : hash_set_gname) (γ' : hash_tape_gname) :
    ⊢ hash_tape1 α ns γ γ' -∗ [∗list] n ∈ ns, hash_set_frag1 n γ
  hash_set_duplicate (x : ℕ) (s : Finset ℕ) (γ : hash_set_gname) :
    x ∈ s → ⊢ hash_set1 s γ -∗ hash_set_frag1 x γ
  hash_set_frag_in_set (s : Finset ℕ) (n : ℕ) (γ : hash_set_gname) :
    ⊢ hash_set1 s γ -∗ hash_set_frag1 n γ -∗ ⌜n ∈ s⌝
  hash_auth_insert (m : hmap) (k v : ℕ) (γ1 : hash_view_gname) (γ2 : hash_set_gname) :
    m[k]? = none → ⊢ hash_set_frag1 v γ2 -∗ hash_auth1 m γ1 γ2 ==∗ hash_auth1 (m.insert k v) γ1 γ2
  hash_set_valid (s : Finset ℕ) (γ : hash_set_gname) :
    ⊢ hash_set1 s γ -∗ ⌜∀ n, n ∈ s → n ≤ val_size⌝
  hash_tape_valid (α : val) (ns : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) :
    ⊢ hash_tape1 α ns γ2 γ3 -∗ ⌜∀ x ∈ ns, x ≤ val_size⌝
  hash_tape_exclusive (α : val) (ns ns' : List ℕ) (γ2 : hash_set_gname) (γ3 : hash_tape_gname) :
    ⊢ hash_tape1 α ns γ2 γ3 -∗ hash_tape1 α ns' γ2 γ3 -∗ False
  hash_tape_presample (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ_hv : hash_view_gname) (γ_set : hash_set_gname)
    (γ : hash_tape_gname) (γ_lock : hash_lock_gname) (α : val) (ns : List ℕ) (s bad : Finset ℕ)
    (ε εI εO : ℝ≥0∞) (E : CoPset) :
    ↑N ⊆ E →
    (∀ x : ℕ, x ∈ bad → x < val_size + 1) →
    εI * bad.card + εO * ((val_size : ℝ≥0∞) + 1 - bad.card) ≤ ε * ((val_size : ℝ≥0∞) + 1) →
    ⊢ con_hash_inv1 N f l hm R γ_hv γ_set γ γ_lock -∗
      hash_tape1 α ns γ_set γ -∗ ↯ ε -∗
      hash_set1 s γ_set -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        ((⌜(n : ℕ) ∈ bad⌝ ∗ ↯ εI) ∨ (⌜(n : ℕ) ∉ bad⌝ ∗ ↯ εO)) ∗
        hash_set1 (s ∪ {(n : ℕ)}) γ_set ∗
        hash_tape1 α (ns ++ [(n : ℕ)]) γ_set γ)
  con_hash_init1 (N : Namespace) (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] :
    {{ R ∅ }} cpl(&init_hash1 #())
    {{ (f : val), RET f; ∃ l hm γ1 γ2 γ3 γ_lock, con_hash_inv1 N f l hm R γ1 γ2 γ3 γ_lock ∗
        hash_set1 ∅ γ2 }}
  con_hash_alloc_tape1 (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash_view_gname) (γ2 : hash_set_gname)
    (γ3 : hash_tape_gname) (γ_lock : hash_lock_gname) :
    {{ con_hash_inv1 N f l hm R γ1 γ2 γ3 γ_lock }} cpl(&allocate_tape1 #())
    {{ (α : val), RET α; hash_tape1 α [] γ2 γ3 }}
  con_hash_spec1 (N : Namespace) (f l hm : val) (R : hmap → IProp GF)
    [HR : ∀ m, Timeless (R m)] (γ1 : hash_view_gname) (γ2 : hash_set_gname)
    (γ3 : hash_tape_gname) (γ_lock : hash_lock_gname)
    (Q1 : ℕ → IProp GF) (Q2 : ℕ → List ℕ → IProp GF) (α : val) (v : ℕ) :
    {{ con_hash_inv1 N f l hm R γ1 γ2 γ3 γ_lock ∗
        (∀ m, R m -∗ hash_auth1 m γ1 γ2 -∗ state_update ⊤ ⊤
          (match m[v]? with
           | some res => iprop(R m ∗ hash_auth1 m γ1 γ2 ∗ Q1 res)
           | none => iprop(∃ n ns, hash_tape1 α (n :: ns) γ2 γ3 ∗
                (hash_tape1 α ns γ2 γ3 ={⊤}=∗ R (m.insert v n) ∗
                  hash_auth1 (m.insert v n) γ1 γ2 ∗ Q2 n ns)))) }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); Q1 res ∨ ∃ ns, Q2 res ns }}

section instances

variable {GF : BundledGFunctors} [conerisGS GF] {val_size : ℕ} [c : con_hash1 GF val_size]

instance con_hash1_hash_tape_timeless (α : val) (ns : List ℕ) (γ2 : c.hash_set_gname)
    (γ3 : c.hash_tape_gname) : Timeless (c.hash_tape1 α ns γ2 γ3) :=
  c.hash_tape_timeless α ns γ2 γ3
instance con_hash1_hash_auth_timeless (m : hmap) (γ : c.hash_view_gname) (γ2 : c.hash_set_gname) :
    Timeless (c.hash_auth1 m γ γ2) := c.hash_auth_timeless m γ γ2
instance con_hash1_hash_frag_timeless (v res : ℕ) (γ : c.hash_view_gname)
    (γ2 : c.hash_set_gname) : Timeless (c.hash_frag1 v res γ γ2) := c.hash_frag_timeless v res γ γ2
instance con_hash1_hash_set_timeless (s : Finset ℕ) (γ2 : c.hash_set_gname) :
    Timeless (c.hash_set1 s γ2) := c.hash_set_timeless s γ2
instance con_hash1_hash_set_frag_timeless (s : ℕ) (γ2 : c.hash_set_gname) :
    Timeless (c.hash_set_frag1 s γ2) := c.hash_set_frag_timeless s γ2
instance con_hash1_con_hash_inv_persistent (N : Namespace) (f l hm : val)
    (γ1 : c.hash_view_gname) (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname)
    (R : hmap → IProp GF) [HR : ∀ m, Timeless (R m)] (γ_lock : c.hash_lock_gname) :
    Persistent (c.con_hash_inv1 N f l hm R γ1 γ2 γ3 γ_lock) :=
  c.con_hash_inv_persistent N f l hm γ1 γ2 γ3 R γ_lock
instance con_hash1_hash_frag_persistent (v res : ℕ) (γ : c.hash_view_gname)
    (γ2 : c.hash_set_gname) : Persistent (c.hash_frag1 v res γ γ2) :=
  c.hash_frag_persistent v res γ γ2
instance con_hash1_hash_set_frag_persistent (s : ℕ) (γ2 : c.hash_set_gname) :
    Persistent (c.hash_set_frag1 s γ2) := c.hash_set_frag_persistent s γ2

end instances

section test

variable {GF : BundledGFunctors} [conerisGS GF] {val_size : ℕ} [c : con_hash1 GF val_size]

/-- Rocq: `con_hash_spec_test1`. -/
theorem con_hash_spec_test1 (N : Namespace) (f l hm : val) (γ1 : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname) (γlock : c.hash_lock_gname) (α : val)
    (n : ℕ) (ns : List ℕ) (v : ℕ) :
    {{ c.con_hash_inv1 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γlock ∗
        c.hash_tape1 α (n :: ns) γ2 γ3 }}
      cpl(&f #v &α)
    {{ (res : ℕ), RET LitV (LitInt (res : ℤ)); c.hash_frag1 v res γ1 γ2 ∗
        ((c.hash_tape1 α ns γ2 γ3 ∗ ⌜res = n⌝) ∨ c.hash_tape1 α (n :: ns) γ2 γ3) }} := by
  iintro %Φ ⟨#Hinv, Ht⟩ HΦ
  ihave ⟨Ht, #Hfrag⟩ := persistent_entails_left
    (wand_entails (c.hash_tape_in_hash_set α (n :: ns) γ2 γ3)) $$ Ht
  iapply c.con_hash_spec1 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γlock
    (fun res => iprop(c.hash_frag1 v res γ1 γ2 ∗ c.hash_tape1 α (n :: ns) γ2 γ3))
    (fun n' ns' => iprop(⌜n = n'⌝ ∗ ⌜ns' = ns⌝ ∗ c.hash_frag1 v n γ1 γ2 ∗ c.hash_tape1 α ns γ2 γ3))
    α v $$ [Ht]
  · isplitr
    · iexact Hinv
    iintro %m - Hauth
    cases hm' : m[v]? with
    | some res =>
      ihave ⟨Hauth, #Hf⟩ := persistent_entails_left
        (wand_entails (c.hash_auth_duplicate m v res γ1 γ2 hm')) $$ Hauth
      dsimp only
      imodintro
      iframe Hauth Hf Ht
    | none =>
      dsimp only
      imodintro
      iexists n, ns
      iframe Ht
      iintro Ht
      ihave ⟨Hn, -⟩ := BigSepL.bigSepL_cons.1 $$ Hfrag
      imod c.hash_auth_insert m v n γ1 γ2 hm' $$ Hn Hauth with H
      ihave ⟨H, #Hf⟩ := persistent_entails_left
        (wand_entails (c.hash_auth_duplicate (m.insert v n) v n γ1 γ2 (by simp))) $$ H
      imodintro
      iframe H Hf Ht
      isplitr <;> ipureintro <;> rfl
  iintro !> %res H
  icases H with (⟨Hf, Ht⟩ | ⟨%ns', %Hn, %Hns, #Hf, Ht⟩)
  · iapply HΦ
    iframe Hf
    iright
    iexact Ht
  · subst Hn Hns
    iapply HΦ
    iframe Hf
    ileft
    iframe Ht
    ipureintro
    rfl

/-- Rocq: `con_hash_spec_hashed_before1`. -/
theorem con_hash_spec_hashed_before1 (N : Namespace) (f l hm : val) (γ1 : c.hash_view_gname)
    (γ2 : c.hash_set_gname) (γ3 : c.hash_tape_gname) (γlock : c.hash_lock_gname) (α : val)
    (res v : ℕ) :
    {{ c.con_hash_inv1 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γlock ∗ c.hash_frag1 v res γ1 γ2 }}
      cpl(&f #v &α)
    {{ RET LitV (LitInt (res : ℤ)); c.hash_frag1 v res γ1 γ2 }} := by
  iintro %Φ ⟨#Hinv, #Hf⟩ HΦ
  iapply c.con_hash_spec1 N f l hm (fun _ => iprop(True)) γ1 γ2 γ3 γlock
    (fun res' => iprop(⌜res = res'⌝ ∗ c.hash_frag1 v res γ1 γ2)) (fun _ _ => iprop(⌜False⌝))
    α v $$ []
  · isplitr
    · iexact Hinv
    iintro %m - Hauth
    ihave %Hlk := c.hash_auth_frag_agree m v res γ1 γ2 $$ Hauth Hf
    rw [Hlk]
    dsimp only
    imodintro
    iframe Hauth Hf
    ipureintro
    rfl
  iintro !> %res' H
  icases H with (⟨%Heq, -⟩ | ⟨%_, %Hfalse⟩)
  · subst Heq
    iapply HΦ
    iexact Hf
  · exact Hfalse.elim

end test

end Coneris.Examples.HashDir.ConHashInterface1
