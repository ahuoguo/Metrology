module

public import Metrology.Coneris.Examples.Hash
public import Metrology.Coneris.Lib.SpinLock
public import Metrology.Coneris.Lib.Par
public import Metrology.Coneris.Lib.ListSpec

/-!
# A concurrent hash

Ported from clutch/theories/coneris/examples/concurrent_hash.v

This example uses the spec from `hash.v` (`Coneris.Examples.Hash`) to derive a concurrent hash
with a simple lock.

## Rocq → Lean map
* Namespace `Coneris.Examples.ConcurrentHash`; `err`, `hash_once_prog`,
  `hash_once_prog_specialized`, `multiple_parallel`, `concurrent_hash_prog`,
  `hash_once_prog_spec`, `multiple_parallel_spec`, `concurrent_hash_spec`: same names.
* The section variables `val_size`, `insert_num`, `max_hash_size` and the hypotheses
  `max_hash_size_pos` and `Hineq` are explicit arguments (only of the definitions/lemmas that use
  them, as Rocq's section mechanism does).
* `Local Existing Instance spin_lock` is `attribute [local instance] spin_lock`; the context
  `!lockG Σ` is an instance argument `[L : spin_lockG GF]` (= `lock.lockG GF` for `spin_lock`),
  passed explicitly to the generic lock interface (`Lock.lock.is_lock L ..`, see
  `Coneris.Lib.Lock`). `acquire`/`release`/`newlock` are the generic `Lock.lock.acquire` etc.
* `Local Opaque amortized_error`: not needed (`err` is never unfolded).
* The expression-scope `e1 ||| e2` in `multiple_parallel` is `par_E e1 e2` (see
  `Coneris.Lib.Par`); after the pure steps it becomes the value-scope `par_V e1 e2` of `wp_par`,
  as in Rocq.
* `let, ("hd", "tl") := e in e'` is `let (hd, tl) := e; e'`; `list_nil`/`list_cons` are
  `&list_nil`/`&list_cons`.
* `own γ (◯ n)` is `iOwn (F := constOF (Auth ℕ)) γ (◯ n)` (see `Coneris.Examples.Hash`).
* `↯ (INR insert_num * err)` is `↯ ((insert_num : ℝ≥0∞) * err)`; `ec_split` is
  `ErrorCredit.split`.
* `[∗ list] k ↦ P ∈ Ps, ...` (index unused) is `[∗list] P ∈ Ps, ...`; the nested Texan triples
  `{{{ P }}} f #() {{{ v, RET v; Q v }}}` are iris-lean's `iprop({{ P }} .. {{ v, RET v; Q v }})`
  (a persistent `□ ∀ Φ, ...`).
* `multiple_parallel_spec` is proved by induction on `Ps` (Rocq: `iLöb`, recursing on the
  length of `Ps`); the `iInduction` of `concurrent_hash_spec` is the Lean induction of the
  helper lemmas `hash_once_prog_spec_list` and `split_credits_tokens`.

## Added
* `split_credits_tokens` (the first `iInduction` of `concurrent_hash_spec`) and
  `hash_once_prog_spec_list` (the second one).

## Omitted
None.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Lock Coneris.Lib.SpinLock Coneris.Lib.Par Coneris.Lib.List
open Coneris.Lib.Spawn Coneris.Examples.Hash

namespace Coneris.Examples.ConcurrentHash

attribute [local instance] spin_lock

section concurrent_hash

variable (val_size : ℕ) (insert_num : ℕ) (max_hash_size : ℕ)

/-- Rocq: `err`. -/
def err (max_hash_size_pos : 0 < max_hash_size) : ℝ≥0∞ :=
  amortized_error val_size max_hash_size max_hash_size_pos

/-- Rocq: `hash_once_prog`. -/
def hash_once_prog : val :=
  cpl_val(λ h lock <>,
    &lock.acquire lock;
    let input := rand(#val_size) in
    let output := h input in
    &lock.release lock;
    (input, output))

/-- Rocq: `hash_once_prog_specialized`. -/
def hash_once_prog_specialized (h lk : val) : val :=
  cpl_val(λ <>,
    &lock.acquire &lk;
    let input := rand(#val_size) in
    let output := &h input in
    &lock.release &lk;
    (input, output))

/-- Rocq: `multiple_parallel`. -/
def multiple_parallel : val :=
  cpl_val(rec multiple_parallel num f :=
    if num ≤ #0 then &list_nil else
      let (hd, tl) := &(par_E cpl(f #()) cpl(multiple_parallel (num - #1) f));
      &list_cons hd tl)

/-- Rocq: `concurrent_hash_prog`. -/
def concurrent_hash_prog : expr :=
  cpl(let h := &(init_hash val_size) #() in
    let lock := &lock.newlock #() in
    (h, &multiple_parallel #insert_num (&(hash_once_prog val_size) h lock)))

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [L : spin_lockG GF]
  [amortized_hashG GF]

/-- Rocq: `hash_once_prog_spec`. -/
theorem hash_once_prog_spec (max_hash_size_pos : 0 < max_hash_size) (γlock : GName)
    (γ1 γ2 : GName) (l f : val) :
    {{ lock.is_lock L γlock l
          (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2) ∗
        ↯ (err val_size max_hash_size max_hash_size_pos) ∗
        iOwn (F := constOF (Auth ℕ)) γ1 (◯ 1) }}
      cpl(&(hash_once_prog_specialized val_size f l) #())
    {{ (k v : ℕ), RET PairV (LitV (LitInt (k : ℤ))) (LitV (LitInt (v : ℤ)));
        (hash_view_frag k v γ2 : IProp GF) }} := by
  iintro %Φ ⟨#H, Herr, Htok⟩ HΦ
  unfold hash_once_prog_specialized
  wp_pures
  wp_apply lock.acquire_spec L γlock l _ $$ H with ⟨Hl, %m, K⟩
  wp_pures
  wp_apply wp_rand val_size val_size (by simp) $$ [] with %x -
  · itrivial
  wp_pures
  wp_apply wp_insert_amortized val_size max_hash_size max_hash_size_pos ⊤ f m γ1 γ2 x
    $$ [K Herr Htok] with %v ⟨%m', H', %_, %_, %_, Hfrag⟩
  · iframe
    unfold err
    iexact Herr
  wp_pures
  wp_apply lock.release_spec L γlock l _ $$ [Hl H'] with -
  · iframe H Hl
    iexists m'
    iexact H'
  wp_pures
  iapply HΦ
  iexact Hfrag

/-- Rocq: `multiple_parallel_spec`. -/
theorem multiple_parallel_spec (Ps : List (IProp GF)) (num : ℕ) (f : val) (Q : val → IProp GF)
    (Hlen : Ps.length = num) :
    {{ ([∗list] P ∈ Ps, iprop({{ P }} cpl(&f #()) {{ v, RET v; Q v }})) ∗ [∗list] P ∈ Ps, P }}
      cpl(&multiple_parallel #num &f)
    {{ v, RET v; (∃ returnl : List val, ⌜returnl.length = num⌝ ∗ ⌜is_list returnl v⌝ ∗
        [∗list] x ∈ returnl, Q x : IProp GF) }} := by
  induction Ps generalizing num with
  | nil =>
    subst Hlen
    iintro %Φ ⟨-, -⟩ HΦ
    unfold multiple_parallel
    wp_pures'
    imodintro
    iapply HΦ
    iexists []
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons P Ps IH =>
    subst Hlen
    iintro %Φ ⟨H1, H2⟩ HΦ
    icases H1 with ⟨#H1, H1'⟩
    icases H2 with ⟨H2, H2'⟩
    wp_rec
    simp only [par_E]
    wp_pures'
    wp_bind (App (App (Val par) _) _)
    have hpar := wp_par (GF := GF) Q (fun v => iprop(∃ returnl : List val,
        ⌜returnl.length = Ps.length⌝ ∗ ⌜is_list returnl v⌝ ∗ [∗list] x ∈ returnl, Q x))
      cpl(&f #()) cpl(&multiple_parallel (#((P :: Ps).length) - #1) &f)
    unfold par_V at hpar
    iapply hpar $$ [H2] [H1' H2']
    · iapply H1 $$ H2
      iintro !> %v Hv
      iexact Hv
    · wp_pures'
      iapply IH Ps.length rfl $$ [H1' H2']
      · iframe
      iintro !> %v H
      iexact H
    iintro %v1 %v2 ⟨HQ, %returnl, %Hlen, %Hl, Hrest⟩
    inext
    wp_pures'
    wp_apply wp_list_cons (A := val) v1 returnl v2 $$ [] with %v %Hv
    · ipureintro
      exact Hl
    iapply HΦ
    iexists v1 :: returnl
    isplitr
    · ipureintro
      simp [Hlen]
    isplitr
    · ipureintro
      exact Hv
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- The first `iInduction` of Rocq's `concurrent_hash_spec`: splitting the error credits and the
tokens into one `↯ e ∗ own γ (◯ 1)` per thread. -/
theorem split_credits_tokens (n : ℕ) (e : ℝ≥0∞) (γ : GName) :
    ↯ ((n : ℝ≥0∞) * e) ∗ iOwn (F := constOF (Auth ℕ)) γ (◯ n) ⊢@{IProp GF}
      [∗list] P ∈ List.replicate n iprop(↯ e ∗ iOwn (F := constOF (Auth ℕ)) γ (◯ 1)), P := by
  induction n with
  | zero =>
    iintro -
    rw [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | succ n IH =>
    iintro ⟨Herr, Htoken⟩
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    have he : ((n + 1 : ℕ) : ℝ≥0∞) * e = e + (n : ℝ≥0∞) * e := by push_cast; ring
    ihave Herr := ErrorCredit.ext he $$ Herr
    icases ErrorCredit.split $$ Herr with ⟨Herr, Herr'⟩
    rw [Nat.add_comm n 1]
    icases (own_frag_add γ 1 n).1 $$ Htoken with ⟨Htoken, Htoken'⟩
    isplitl [Herr Htoken]
    · iframe
    iapply IH
    iframe

/-- Rocq: `hash_once_prog "h" "lock"` reduces to `hash_once_prog_specialized h lock` (the
`rewrite - /(hash_once_prog_specialized f lk)` step of `concurrent_hash_spec`). -/
theorem hash_once_prog_app (f lk : val) (Φ : val → IProp GF) :
    Φ (hash_once_prog_specialized val_size f lk) ⊢
      WP cpl(&(hash_once_prog val_size) &f &lk) {{ Φ }} := by
  iintro H
  unfold hash_once_prog
  wp_pures
  imodintro
  unfold hash_once_prog_specialized
  iexact H

/-- The second `iInduction` of Rocq's `concurrent_hash_spec`: one `hash_once_prog_spec` per
thread. -/
theorem hash_once_prog_spec_list (max_hash_size_pos : 0 < max_hash_size) (n : ℕ)
    (γlock γ1 γ2 : GName) (lk f : val) :
    lock.is_lock L γlock lk (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2)
      ⊢@{IProp GF}
      [∗list] P ∈ List.replicate n iprop(↯ (err val_size max_hash_size max_hash_size_pos) ∗
          iOwn (F := constOF (Auth ℕ)) γ1 (◯ 1)),
        iprop({{ P }} cpl(&(hash_once_prog_specialized val_size f lk) #())
          {{ v, RET v; ∃ k v' : ℕ,
            ⌜v = PairV (LitV (LitInt (k : ℤ))) (LitV (LitInt (v' : ℤ)))⌝ ∗
            hash_view_frag k v' γ2 }}) := by
  induction n with
  | zero =>
    iintro -
    rw [List.replicate_zero]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | succ n IH =>
    iintro #Hlock
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · imodintro
      iintro %Φ' ⟨H1, H2⟩ HΦ
      iapply hash_once_prog_spec val_size max_hash_size max_hash_size_pos γlock γ1 γ2 lk f
        $$ [H1 H2]
      · iframe Hlock H1 H2
      iintro !> %k %v H'
      iapply HΦ
      iexists k, v
      iframe
      ipureintro
      rfl
    iapply IH $$ Hlock

/-- Rocq: `concurrent_hash_spec`. -/
theorem concurrent_hash_spec (max_hash_size_pos : 0 < max_hash_size)
    (Hineq : insert_num ≤ max_hash_size) :
    {{ ↯ ((insert_num : ℝ≥0∞) * err val_size max_hash_size max_hash_size_pos) }}
      (concurrent_hash_prog val_size insert_num)
    {{ (f lv : val), RET PairV f lv; (∃ (γ1 γ2 γlock : GName) (l : val) (ls : List val),
        lock.is_lock L γlock l
          (∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2) ∗
        ⌜is_list ls lv⌝ ∗
        ⌜ls.length = insert_num⌝ ∗
        ([∗list] x ∈ ls, ∃ k v : ℕ,
          ⌜x = PairV (LitV (LitInt (k : ℤ))) (LitV (LitInt (v : ℤ)))⌝ ∗ hash_view_frag k v γ2) ∗
        iOwn (F := constOF (Auth ℕ)) γ1 (◯ (max_hash_size - insert_num)) : IProp GF) }} := by
  unfold concurrent_hash_prog
  iintro %Φ Herr HΦ
  wp_apply wp_init_hash_amortized val_size max_hash_size ⊤ $$ [] with %f Hf
  · itrivial
  imod Hf with ⟨%γ1, %γ2, Hf, Htoken⟩
  wp_pures
  wp_apply lock.newlock_spec L
    iprop(∃ m, coll_free_hashfun_amortized val_size max_hash_size f m γ1 γ2) $$ [Hf]
    with %lk %γlock #Hlock
  · iexists ∅
    iexact Hf
  wp_pures
  ihave Htoken := (show iOwn (GF := GF) (F := constOF (Auth ℕ)) γ1 (◯ max_hash_size) ⊢
      iOwn (F := constOF (Auth ℕ)) γ1 (◯ (insert_num + (max_hash_size - insert_num))) by
    rw [Nat.add_sub_cancel' Hineq]) $$ Htoken
  icases (own_frag_add γ1 _ _).1 $$ Htoken with ⟨Htoken, Htoken'⟩
  ihave HPs := split_credits_tokens insert_num (err val_size max_hash_size max_hash_size_pos) γ1
    $$ [Herr Htoken]
  · iframe
  wp_bind (App (App (Val (hash_once_prog val_size)) _) _)
  iapply hash_once_prog_app
  wp_apply multiple_parallel_spec
    (List.replicate insert_num iprop(↯ (err val_size max_hash_size max_hash_size_pos) ∗
      iOwn (F := constOF (Auth ℕ)) γ1 (◯ 1)))
    insert_num (hash_once_prog_specialized val_size f lk)
    (fun x => iprop(∃ k v : ℕ, ⌜x = PairV (LitV (LitInt (k : ℤ))) (LitV (LitInt (v : ℤ)))⌝ ∗
      hash_view_frag k v γ2)) (by simp) $$ [HPs] with %lv ⟨%ls, %Hlen, %Hls, Hrest⟩
  · isplitr [HPs]
    · iapply hash_once_prog_spec_list val_size max_hash_size max_hash_size_pos insert_num
        γlock γ1 γ2 lk f $$ Hlock
    · iexact HPs
  wp_pures
  imodintro
  iapply HΦ
  iexists γ1, γ2, γlock, lk, ls
  iframe
  isplitr
  · iexact Hlock
  ipureintro
  exact ⟨Hls, Hlen⟩

end concurrent_hash

end Coneris.Examples.ConcurrentHash
