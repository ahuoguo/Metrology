module

public import Metrology.Coneris.ErrorRules

/-!
# An interface for a lazily sampled random value

Ported from clutch/theories/coneris/examples/lazy_rand/lazy_rand_interface.v

## Rocq → Lean mapping
* `Class lazy_rand `{!conerisGS Σ} (val_size:nat) := Lazy_Rand {...}` is the Lean
  `class lazy_rand (val_size : ℕ) GF` (over `[conerisGS GF]`) with the same field names:
  `init_lazy_rand`, `allocate_tape`, `lazy_read_rand`, `rand_tape_gname`, `rand_view_gname`,
  `rand_lock_gname`, `rand_inv`, `rand_tape_frag`, `rand_auth`, `rand_frag`,
  `rand_tape_frag_timeless`, `rand_auth_timeless`, `rand_frag_timeless`,
  `rand_tape_frag_valid`, `rand_inv_persistent`, `rand_frag_persistent`,
  `rand_tape_frag_exclusive`, `rand_auth_exclusive`, `rand_auth_frag_agree`,
  `rand_auth_duplicate`, `rand_auth_valid`, `rand_frag_valid`, `rand_frag_frag_agree`,
  `rand_auth_update`, `rand_tape_presample`, `lazy_rand_init`, `lazy_rand_alloc_tape`,
  `lazy_rand_spec`.
  - `{HP: ∀ n, Timeless (P n)}` is the instance argument `[HP : ∀ n, Timeless (P n)]`.
  - The `#[global] ... ::` instance fields are fields, re-exported as the global instances
    `lazy_rand_rand_tape_frag_timeless`, `lazy_rand_rand_auth_timeless`,
    `lazy_rand_rand_frag_timeless`, `lazy_rand_rand_inv_persistent`,
    `lazy_rand_rand_frag_persistent`.
  - Errors are `ℝ≥0∞`: the hypothesis `∀ x, 0 <= ε2 x` of `rand_tape_presample` is dropped;
    `SeriesC (λ n : fin (S val_size), 1 / S val_size * ε2 n) <= ε` is
    `∑' n, 1 / ((val_size : ℝ≥0∞) + 1) * ε2 n ≤ ε`; `fin (S val_size)` is `Fin (val_size + 1)`
    and `fin_to_nat n` is `(n : ℕ)`.
  - `P -∗ Q` / `P ==∗ Q` fields are stated as `⊢ P -∗ Q` / `⊢ P ==∗ Q`.
  - Texan triples `{{{ P }}} e {{{ x, RET v; Q }}}` are iris-lean's
    `{{ P }} e {{ x, RET v; Q }}` (mask `⊤`); `#tid` (`tid : nat`) is `#tid`
    (`LitV (LitInt tid)`), `(#res', #tid')%V` is `cpl_val((#res', #tid'))`.

## Omitted
* The commented-out Rocq field `rand_tape_auth_alloc`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Examples.LazyRand.LazyRandInterface

/-- Rocq: `lazy_rand`. -/
class lazy_rand (val_size : ℕ) (GF : BundledGFunctors) [conerisGS GF] where
  -- * Operations
  init_lazy_rand : val
  allocate_tape : val
  lazy_read_rand : val
  -- * Ghost state
  rand_tape_gname : Type
  rand_view_gname : Type
  rand_lock_gname : Type
  -- * Predicates
  rand_inv (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ : rand_tape_gname) (γ' : rand_view_gname)
    (γ_lock : rand_lock_gname) : IProp GF
  rand_tape_frag (α : val) (n : Option ℕ) (γ : rand_tape_gname) : IProp GF
  rand_auth (m : Option (ℕ × ℕ)) (γ : rand_view_gname) : IProp GF
  rand_frag (res : ℕ) (tid : ℕ) (γ : rand_view_gname) : IProp GF
  -- * General properties of the predicates
  rand_tape_frag_timeless (α : val) (ns : Option ℕ) (γ : rand_tape_gname) :
    Timeless (rand_tape_frag α ns γ)
  rand_auth_timeless (n : Option (ℕ × ℕ)) (γ : rand_view_gname) : Timeless (rand_auth n γ)
  rand_frag_timeless (n tid : ℕ) (γ : rand_view_gname) : Timeless (rand_frag n tid γ)
  rand_tape_frag_valid (α : val) (ns : ℕ) (γ : rand_tape_gname) :
    ⊢ rand_tape_frag α (some ns) γ -∗ ⌜ns ≤ val_size⌝
  rand_inv_persistent (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ_tape : rand_tape_gname) (γ_view : rand_view_gname)
    (γ_lock : rand_lock_gname) : Persistent (rand_inv N c P γ_tape γ_view γ_lock)
  rand_frag_persistent (v res : ℕ) (γ : rand_view_gname) : Persistent (rand_frag v res γ)
  rand_tape_frag_exclusive (α : val) (ns ns' : Option ℕ) (γ : rand_tape_gname) :
    ⊢ rand_tape_frag α ns γ -∗ rand_tape_frag α ns' γ -∗ False
  rand_auth_exclusive (n n' : Option (ℕ × ℕ)) (γ : rand_view_gname) :
    ⊢ rand_auth n γ -∗ rand_auth n' γ -∗ False
  rand_auth_frag_agree (n : Option (ℕ × ℕ)) (n' tid : ℕ) (γ : rand_view_gname) :
    ⊢ rand_auth n γ -∗ rand_frag n' tid γ -∗ ⌜n = some (n', tid)⌝
  rand_auth_duplicate (n : ℕ × ℕ) (γ : rand_view_gname) :
    ⊢ rand_auth (some n) γ -∗ rand_frag n.1 n.2 γ
  rand_auth_valid (n tid : ℕ) (γ : rand_view_gname) :
    ⊢ rand_auth (some (n, tid)) γ -∗ ⌜n ≤ val_size⌝
  rand_frag_valid (n tid : ℕ) (γ : rand_view_gname) :
    ⊢ rand_frag n tid γ -∗ ⌜n ≤ val_size⌝
  rand_frag_frag_agree (v1 v2 tid1 tid2 : ℕ) (γ : rand_view_gname) :
    ⊢ rand_frag v1 tid1 γ -∗ rand_frag v2 tid2 γ -∗ ⌜v1 = v2 ∧ tid1 = tid2⌝
  rand_auth_update (n : ℕ × ℕ) (γ : rand_view_gname) :
    n.1 ≤ val_size → ⊢ rand_auth none γ ==∗ rand_auth (some n) γ
  rand_tape_presample (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ : rand_tape_gname) (γ_view : rand_view_gname)
    (γ_lock : rand_lock_gname) (E : CoPset) (α : val) (ε : ℝ≥0∞)
    (ε2 : Fin (val_size + 1) → ℝ≥0∞) :
    ↑N ⊆ E →
    ∑' n, 1 / ((val_size : ℝ≥0∞) + 1) * ε2 n ≤ ε →
    ⊢ rand_inv N c P γ γ_view γ_lock -∗
      rand_tape_frag α none γ -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        ↯ (ε2 n) ∗ rand_tape_frag α (some (n : ℕ)) γ)
  lazy_rand_init (N : Namespace) (P : Option (ℕ × ℕ) → IProp GF) [HP : ∀ n, Timeless (P n)] :
    {{ P none }} cpl(v(&init_lazy_rand) #())
    {{ c, RET c; ∃ γ γ_view γ_lock, rand_inv N c P γ γ_view γ_lock }}
  lazy_rand_alloc_tape (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ_tape : rand_tape_gname) (γ_view : rand_view_gname)
    (γ_lock : rand_lock_gname) :
    {{ rand_inv N c P γ_tape γ_view γ_lock }} cpl(v(&allocate_tape) #())
    {{ α, RET α; rand_tape_frag α none γ_tape }}
  lazy_rand_spec (N : Namespace) (c : val) (P : Option (ℕ × ℕ) → IProp GF)
    [HP : ∀ n, Timeless (P n)] (γ_tape : rand_tape_gname) (γ_view : rand_view_gname)
    (γ_lock : rand_lock_gname) (Q1 Q2 : ℕ → ℕ → IProp GF) (α : val) (tid : ℕ) :
    {{ rand_inv N c P γ_tape γ_view γ_lock ∗
        (∀ n, P n -∗ rand_auth n γ_view -∗ state_update ⊤ ⊤
          (match n with
           | some (res, tid') => iprop(P n ∗ rand_auth n γ_view ∗ Q1 res tid')
           | none => iprop(∃ n', rand_tape_frag α (some n') γ_tape ∗
                (rand_tape_frag α none γ_tape ={⊤}=∗
                  P (some (n', tid)) ∗ rand_auth (some (n', tid)) γ_view ∗ Q2 n' tid)))) }}
      cpl(v(&lazy_read_rand) v(&c) v(&α) #tid)
    {{ (res' tid' : ℕ), RET cpl_val((#res', #tid')); Q1 res' tid' ∨ Q2 res' tid' }}

section instances

variable {val_size : ℕ} {GF : BundledGFunctors} [conerisGS GF] [l : lazy_rand val_size GF]

/-- Rocq: `#[global] rand_tape_frag_timeless` (the instance). -/
instance lazy_rand_rand_tape_frag_timeless (α : val) (ns : Option ℕ) (γ : l.rand_tape_gname) :
    Timeless (l.rand_tape_frag α ns γ) := l.rand_tape_frag_timeless α ns γ

/-- Rocq: `#[global] rand_auth_timeless` (the instance). -/
instance lazy_rand_rand_auth_timeless (n : Option (ℕ × ℕ)) (γ : l.rand_view_gname) :
    Timeless (l.rand_auth n γ) := l.rand_auth_timeless n γ

/-- Rocq: `#[global] rand_frag_timeless` (the instance). -/
instance lazy_rand_rand_frag_timeless (n tid : ℕ) (γ : l.rand_view_gname) :
    Timeless (l.rand_frag n tid γ) := l.rand_frag_timeless n tid γ

/-- Rocq: `#[global] rand_inv_persistent` (the instance). -/
instance lazy_rand_rand_inv_persistent (N : Namespace) (c : val)
    (P : Option (ℕ × ℕ) → IProp GF) [HP : ∀ n, Timeless (P n)] (γ_tape : l.rand_tape_gname)
    (γ_view : l.rand_view_gname) (γ_lock : l.rand_lock_gname) :
    Persistent (l.rand_inv N c P γ_tape γ_view γ_lock) :=
  l.rand_inv_persistent N c P γ_tape γ_view γ_lock

/-- Rocq: `#[global] rand_frag_persistent` (the instance). -/
instance lazy_rand_rand_frag_persistent (v res : ℕ) (γ : l.rand_view_gname) :
    Persistent (l.rand_frag v res γ) := l.rand_frag_persistent v res γ

end instances

end Coneris.Examples.LazyRand.LazyRandInterface
