module

public import Metrology.Coneris.ProofMode

/-!
# Array utilities for Coneris

Ported from clutch/theories/coneris/lib/array.v (itself adapted from iris.heap_lang).

Provides some array utilities:
* `array_copy_to`, a function which copies to an array in-place.
* Using `array_copy_to` we also implement `array_clone`, which allocates a fresh array and
  copies to it, and `array_resize`.
* `array_init`, to create and initialize an array with a given function. Specifically,
  `array_init n f` creates a new array of size `n` in which the `i`th element is initialized
  with `f #i`.

## Rocq → Lean mapping
* Programs are written with the `cpl_val(...)` notation; `rec: "f" "x" := e` is
  `rec f x := e`, `AllocN e1 e2` is `allocn(e1, e2)`, `e1 <- e2` is `e1 ← e2`, `e1 ;; e2` is
  `e1; e2`. Rocq's `if: _ then _ else e1 ;; e2` (the `else` branch extends to the end) is
  written `if _ then _ else (e1; e2)` (in the Lean notation `;` binds weaker than `if`).
* `{{{ P }}} e @ E {{{ x, RET v; Q }}}` is iris-lean's `{{ P }} (e) @ s; E {{ x, RET v; Q }}`,
  generalized over the stuckness `s` (as in `Metrology.Coneris.DerivedLaws`).
* `l ↦∗{dq} vs`, `l ↦∗ vs` are those of `Metrology.Coneris.DerivedLaws`.
* `seq 0 n` is `List.range n`, `seq i k` is `List.range' i k`, `replicate` is
  `List.replicate`, `g <$> xs` is `xs.map g`, `length` is `List.length`.
* Rocq `#(i : nat)` is `LitV (LitInt ((i : ℕ) : ℤ))` (written `#i` with `i : ℕ`).
* `pgl_wp_wand` is `Coneris.pgl_wp_wand`.
* Proofs by `iInduction` are Lean inductions on the (closed) Texan-triple statements.

## Deviations
* `array_init_loop` and `wp_array_init_loop` are `Local` in Rocq; here they are ordinary
  (public) declarations of the namespace `Coneris.Lib.Array`.
* The section variable `R` of Rocq's `array_init_fmap` section is unused there and omitted.
* `big_sepL_exists_eq` is `Local` in Rocq; here it is an ordinary lemma.

## Proof notes
* In `wp_array_copy_to`, `wp_array_init_loop` the store is done with
  `wp_apply wp_store $$ H` instead of the `wp_store` tactic: with array points-tos
  (`l ↦∗ vs`) in the context, the `wp_store` tactic times out while looking up the points-to
  (a unification of `l ↦ ?v` against the array hypotheses).

## Added
* Sanity-check `example`s checking the transcribed programs against their ASTs.
* Helpers `array_replicate_split`, `array_cons_shift`,
  `big_sepL_range'_succ`, `big_sepL_cons_shift` (small arithmetic/big-op facts that Rocq's
  proofs do inline by `rewrite`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris

namespace Coneris.Lib.Array

/-- Rocq: `array_copy_to`. -/
def array_copy_to : val :=
  cpl_val(rec array_copy_to dst src n :=
    if n ≤ #0 then #()
    else (dst ← !src;
          array_copy_to (dst +ₗ #1) (src +ₗ #1) (n - #1)))

/-- Rocq: `array_clone`. -/
def array_clone : val :=
  cpl_val(λ src n,
    let dst := allocn(n, #()) in
    &array_copy_to dst src n;
    dst)

/-- Rocq: `array_resize`. Not very efficient, but OK for the purpose of writing
specifications. -/
def array_resize : val :=
  cpl_val(λ src n m,
    let dst := allocn(n + m, #()) in
    &array_copy_to dst src n;
    dst)

/-- Rocq: `array_init_loop` (`Local` in Rocq). `array_init_loop src i n f` initializes
elements `i`, `i+1`, ..., `n` of the array `src` to `f #i`, `f #(i+1)`, ..., `f #n`. -/
def array_init_loop : val :=
  cpl_val(rec loop src i n f :=
    if i = n then #()
    else (src +ₗ i ← f i;
          loop src (i + #1) n f))

/-- Rocq: `array_init`. -/
def array_init : val :=
  cpl_val(λ n f,
    let src := allocn(n, #()) in
    &array_init_loop src #0 n f;
    src)

/-- Sanity check: the transcription of `array_copy_to` is the intended AST. -/
example : array_copy_to =
    val.RecV (.BNamed "array_copy_to") (.BNamed "dst") (expr.Rec .BAnon (.BNamed "src")
      (expr.Rec .BAnon (.BNamed "n")
        (expr.If (expr.BinOp .LeOp (expr.Var "n") (expr.Val (val.LitV (.LitInt 0))))
          (expr.Val (val.LitV .LitUnit))
          (Seq (expr.Store (expr.Var "dst") (expr.Load (expr.Var "src")))
            (expr.App (expr.App (expr.App (expr.Var "array_copy_to")
              (expr.BinOp .OffsetOp (expr.Var "dst") (expr.Val (val.LitV (.LitInt 1)))))
              (expr.BinOp .OffsetOp (expr.Var "src") (expr.Val (val.LitV (.LitInt 1)))))
              (expr.BinOp .MinusOp (expr.Var "n") (expr.Val (val.LitV (.LitInt 1))))))))) :=
  rfl

/-- Sanity check: the transcription of `array_init_loop` is the intended AST. -/
example : array_init_loop =
    val.RecV (.BNamed "loop") (.BNamed "src") (expr.Rec .BAnon (.BNamed "i")
      (expr.Rec .BAnon (.BNamed "n") (expr.Rec .BAnon (.BNamed "f")
        (expr.If (expr.BinOp .EqOp (expr.Var "i") (expr.Var "n"))
          (expr.Val (val.LitV .LitUnit))
          (Seq (expr.Store (expr.BinOp .OffsetOp (expr.Var "src") (expr.Var "i"))
                (expr.App (expr.Var "f") (expr.Var "i")))
            (expr.App (expr.App (expr.App (expr.App (expr.Var "loop") (expr.Var "src"))
              (expr.BinOp .PlusOp (expr.Var "i") (expr.Val (val.LitV (.LitInt 1)))))
              (expr.Var "n")) (expr.Var "f"))))))) :=
  rfl

/-- Sanity check: the transcription of `array_resize` is the intended AST. -/
example : array_resize =
    val.RecV .BAnon (.BNamed "src") (expr.Rec .BAnon (.BNamed "n") (expr.Rec .BAnon (.BNamed "m")
      (Let (.BNamed "dst")
        (expr.AllocN (expr.BinOp .PlusOp (expr.Var "n") (expr.Var "m")) (expr.Val (val.LitV .LitUnit)))
        (Seq (expr.App (expr.App (expr.App (expr.Val array_copy_to) (expr.Var "dst"))
            (expr.Var "src")) (expr.Var "n"))
          (expr.Var "dst"))))) :=
  rfl

/-- Sanity check: the transcription of `array_init` is the intended AST. -/
example : array_init =
    val.RecV .BAnon (.BNamed "n") (expr.Rec .BAnon (.BNamed "f")
      (Let (.BNamed "src") (expr.AllocN (expr.Var "n") (expr.Val (val.LitV .LitUnit)))
        (Seq (expr.App (expr.App (expr.App (expr.App (expr.Val array_init_loop)
            (expr.Var "src")) (expr.Val (val.LitV (.LitInt 0)))) (expr.Var "n")) (expr.Var "f"))
          (expr.Var "src")))) :=
  rfl

section proof

variable {GF : BundledGFunctors} [conerisGS GF]
variable {s : Stuckness} {E : CoPset}

/-- Rocq: `wp_array_copy_to`. -/
theorem wp_array_copy_to (dst src : Loc) (vdst vsrc : List val) (dq : DFrac) (n : ℤ)
    (Hvdst : (vdst.length : ℤ) = n) (Hvsrc : (vsrc.length : ℤ) = n) :
    {{ dst ↦∗ vdst ∗ src ↦∗{dq} vsrc }} (cpl(&array_copy_to #dst #src #n)) @ s; E
    {{ RET LitV LitUnit; (dst ↦∗ vsrc ∗ src ↦∗{dq} vsrc : IProp GF) }} := by
  induction vdst generalizing n dst src vsrc with
  | nil =>
    cases vsrc with
    | cons => simp at Hvdst Hvsrc; omega
    | nil =>
      simp at Hvdst; subst Hvdst
      iintro %Φ ⟨Hdst, Hsrc⟩ HΦ
      wp_rec
      wp_pures
      iapply HΦ
      iframe
  | cons v1 vdst IH =>
    cases vsrc with
    | nil => simp at Hvdst Hvsrc; omega
    | cons v2 vsrc =>
      iintro %Φ ⟨Hdst, Hsrc⟩ HΦ
      simp only [List.length_cons] at Hvdst Hvsrc
      wp_rec
      wp_pures
      rw [decide_eq_false (by omega)]
      wp_pures
      icases (array_cons dst _ v1 vdst).1 $$ Hdst with ⟨Hv1, Hdst⟩
      icases (array_cons src _ v2 vsrc).1 $$ Hsrc with ⟨Hv2, Hsrc⟩
      wp_load
      -- `wp_store` times out here (see the module docstring), so we apply `wp_store` directly.
      wp_apply wp_store $$ Hv1 with Hv1
      wp_smart_apply IH (dst +ₗ 1) (src +ₗ 1) vsrc (n - 1) (by omega) (by omega) $$ [Hdst Hsrc] with ⟨Hdst, Hsrc⟩
      · iframe
      iapply HΦ
      iframe

/-- Rocq: `wp_array_clone`. -/
theorem wp_array_clone (l : Loc) (dq : DFrac) (vl : List val) (n : ℤ)
    (Hvl : (vl.length : ℤ) = n) (Hn : 0 < n) :
    {{ l ↦∗{dq} vl }} (cpl(&array_clone #l #n)) @ s; E
    {{ l', RET LitV (LitLoc l'); (l' ↦∗ vl ∗ l ↦∗{dq} vl : IProp GF) }} := by
  iintro %Φ Hvl HΦ
  wp_lam
  wp_pures
  wp_alloc dst as Hdst
  wp_pures
  wp_smart_apply wp_array_copy_to dst l (List.replicate n.toNat (LitV LitUnit)) vl dq n
    (by simp; omega) Hvl $$ [Hdst Hvl] with ⟨Hdst, Hl⟩
  · iframe
  wp_pures
  iapply HΦ
  iframe

/-- Helper (not in Rocq): splitting the array allocated by `array_resize` (Rocq: inline
`rewrite Z2Nat.inj_add Nat2Z.id replicate_add; iPoseProof (array_app ...)`). -/
theorem array_replicate_split (l : Loc) (n m : ℕ) (v : val) :
    (l ↦∗ List.replicate ((n : ℤ) + (m : ℤ)).toNat v : IProp GF) ⊢
      l ↦∗ List.replicate n v ∗ (l +ₗ (n : ℤ)) ↦∗ List.replicate m v := by
  rw [show ((n : ℤ) + (m : ℤ)).toNat = n + m by omega, List.replicate_add]
  refine (array_app l _ _ _).1.trans ?_
  rw [List.length_replicate]

/-- Rocq: `wp_array_resize`. -/
theorem wp_array_resize (l : Loc) (dq : DFrac) (vl : List val) (n m : ℕ)
    (Hvl : (vl.length : ℤ) = (n : ℤ)) (Hn : 0 < n) (Hm : 0 < m) :
    {{ l ↦∗{dq} vl }} (cpl(&array_resize #l #n #m)) @ s; E
    {{ l', RET LitV (LitLoc l');
      (l' ↦∗ (vl ++ List.replicate m (LitV LitUnit)) ∗ l ↦∗{dq} vl : IProp GF) }} := by
  obtain rfl : vl.length = n := by omega
  iintro %Φ Hvl HΦ
  wp_lam
  wp_pures
  wp_alloc dst as Hdst
  icases array_replicate_split dst vl.length m _ $$ Hdst with ⟨Hdst1, Hdst2⟩
  wp_pures
  wp_smart_apply wp_array_copy_to dst l (List.replicate vl.length (LitV LitUnit)) vl dq
    vl.length (by simp) rfl $$ [Hdst1 Hvl] with ⟨Hdst, Hl⟩
  · iframe
  wp_pures
  iapply HΦ
  iframe
  iapply (array_app dst _ vl _).2
  iframe

/-! ### `array_init` -/

section array_init

variable (Q : ℕ → val → IProp GF)

omit [conerisGS GF] in
/-- Helper (not in Rocq): `seq i (S k) = i :: seq (S i) k` under a big separating
conjunction. -/
theorem big_sepL_range'_succ (Φ : ℕ → IProp GF) (i k : ℕ) :
    ([∗list] j ∈ List.range' i (k + 1), Φ j) ⊣⊢ Φ i ∗ [∗list] j ∈ List.range' (i + 1) k, Φ j := by
  rw [List.range'_succ]
  exact BigSepL.bigSepL_cons

/-- Helper (not in Rocq): `array_cons` at an offset `l +ₗ i` (Rocq: inline
`rewrite loc_add_assoc Z.add_1_r -Nat2Z.inj_succ`). -/
theorem array_cons_shift (l : Loc) (dq : DFrac) (i : ℕ) (v : val) (vs : List val) :
    ((l +ₗ (i : ℤ)) ↦∗{dq} (v :: vs) : IProp GF) ⊣⊢
      (l +ₗ (i : ℤ)) ↦{dq} v ∗ (l +ₗ ((i + 1 : ℕ) : ℤ)) ↦∗{dq} vs := by
  refine (array_cons _ dq v vs).trans ?_
  rw [loc_add_assoc]
  push_cast
  exact .rfl

omit [conerisGS GF] in
/-- Helper (not in Rocq): re-indexing the big separating conjunction of the postcondition of
`wp_array_init_loop` (Rocq: inline `rewrite /= Nat.add_0_r; setoid_rewrite Nat.add_succ_r`). -/
theorem big_sepL_cons_shift (i : ℕ) (v : val) (vs : List val) :
    Q i v ∗ ([∗list] j ↦ w ∈ vs, Q (i + 1 + j) w) ⊢ [∗list] j ↦ w ∈ v :: vs, Q (i + j) w := by
  refine .trans ?_ BigSepL.bigSepL_cons.2
  rw [BigSepL.bigSepL_eq_of_forall_eq (Ψ := fun j w => Q (i + (j + 1)) w)
    (@fun j w => by rw [Nat.add_right_comm, Nat.add_assoc])]
  exact .rfl

/-- Rocq: `wp_array_init_loop` (`Local` in Rocq). -/
theorem wp_array_init_loop (l : Loc) (i : ℕ) (n : ℤ) (k : ℕ) (f : val)
    (Hn : n = ((i + k : ℕ) : ℤ)) :
    {{ (l +ₗ (i : ℤ)) ↦∗ List.replicate k (LitV LitUnit) ∗
        [∗list] j ∈ List.range' i k, WP (cpl(&f #(j : ℕ))) @ s; E {{ Q j }} }}
      (cpl(&array_init_loop #l #i #n &f)) @ s; E
    {{ vs, RET LitV LitUnit;
      ⌜vs.length = k⌝ ∗ (l +ₗ (i : ℤ)) ↦∗ vs ∗ [∗list] j ↦ v ∈ vs, Q (i + j) v }} := by
  induction k generalizing i with
  | zero =>
    subst Hn
    simp only [List.replicate_zero, List.range'_zero]
    iintro %Φ ⟨Hl, Hf⟩ HΦ
    wp_rec
    wp_pures
    imodintro
    iapply HΦ $$ %([] : List val)
    isplitr
    · ipureintro; rfl
    isplitl [Hl]
    · iexact Hl
    iclear Hf
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | succ k IH =>
    subst Hn
    rw [List.replicate_succ]
    iintro %Φ ⟨Hl, Hf⟩ HΦ
    wp_rec
    wp_pures
    rw [decide_eq_false (by omega)]
    wp_pures
    icases (array_cons_shift l _ i _ _).1 $$ Hl with ⟨Hl, HSl⟩
    icases (big_sepL_range'_succ _ i k).1 $$ Hf with ⟨Hf, HSf⟩
    wp_bind (App (Val f) _)
    iapply pgl_wp_wand $$ Hf
    iintro %v Hv
    wp_pures
    wp_apply wp_store $$ Hl with Hl
    wp_pures
    rw [show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; rfl]
    iapply IH (i + 1) (by omega) $$ [HSl HSf]
    · iframe
    inext
    iintro %vs ⟨%Hlen, HSl, Hvs⟩
    iapply HΦ $$ %(v :: vs)
    isplitr
    · ipureintro; simp [Hlen]
    isplitl [Hl HSl]
    · iapply (array_cons_shift l _ i v vs).2
      iframe
    iapply big_sepL_cons_shift
    iframe

/-- Rocq: `wp_array_init`. -/
theorem wp_array_init (n : ℤ) (f : val) (Hn : 0 < n) :
    {{ [∗list] i ∈ List.range n.toNat, WP (cpl(&f #(i : ℕ))) @ s; E {{ Q i }} }}
      (cpl(&array_init #n &f)) @ s; E
    {{ l vs, RET LitV (LitLoc l);
      ⌜(vs.length : ℤ) = n⌝ ∗ l ↦∗ vs ∗ [∗list] k ↦ v ∈ vs, Q k v }} := by
  rw [List.range_eq_range']
  iintro %Φ Hf HΦ
  wp_lam
  wp_pures
  wp_alloc l as Hl
  have H := wp_array_init_loop (s := s) (E := E) Q l 0 n n.toNat f (by omega)
  simp only [Nat.cast_zero, loc_add_0, Nat.zero_add] at H
  wp_pures
  wp_smart_apply H $$ [Hl Hf] with %vs ⟨%Hlen, Hl, Hvs⟩
  · iframe
  wp_pures
  iapply HΦ $$ %l %vs
  iframe
  ipureintro
  omega

end array_init

/-! ### `array_init_fmap` -/

section array_init_fmap

variable {A : Type} (g : A → val) (Q : ℕ → A → IProp GF)

omit [conerisGS GF] in
/-- Rocq: `big_sepL_exists_eq` (`Local` in Rocq). -/
theorem big_sepL_exists_eq (vs : List val) :
    ([∗list] k ↦ v ∈ vs, ∃ x, ⌜v = g x⌝ ∗ Q k x) ⊢
      ∃ xs, ⌜vs = xs.map g⌝ ∗ [∗list] k ↦ x ∈ xs, Q k x := by
  induction vs generalizing Q with
  | nil =>
    iintro -
    iexists []
    isplitr
    · ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons v vs IH =>
    iintro ⟨⟨%x, %Hx, Hv⟩, Hvs⟩
    icases IH (fun k => Q (k + 1)) $$ Hvs with ⟨%xs, %Hxs, Hxs⟩
    iexists x :: xs
    isplitr
    · ipureintro; simp [Hx, Hxs]
    iframe

/-- Rocq: `wp_array_init_fmap`. -/
theorem wp_array_init_fmap (n : ℤ) (f : val) (Hn : 0 < n) :
    {{ [∗list] i ∈ List.range n.toNat,
        WP (cpl(&f #(i : ℕ))) @ s; E {{ v, ∃ x, ⌜v = g x⌝ ∗ Q i x }} }}
      (cpl(&array_init #n &f)) @ s; E
    {{ l xs, RET LitV (LitLoc l);
      ⌜(xs.length : ℤ) = n⌝ ∗ l ↦∗ (xs.map g) ∗ [∗list] k ↦ x ∈ xs, Q k x }} := by
  iintro %Φ Hf HΦ
  iapply wp_array_init (fun i v => iprop(∃ x, ⌜v = g x⌝ ∗ Q i x)) n f Hn $$ Hf
  inext
  iintro %l %vs ⟨%Hlen, Hl, Hvs⟩
  icases big_sepL_exists_eq g Q vs $$ Hvs with ⟨%xs, %Hxs, Hxs⟩
  subst Hxs
  iapply HΦ $$ %l %xs
  iframe
  ipureintro
  simpa using Hlen

end array_init_fmap

/-! ### `array_zip` -/

section array_zip

variable {A B : Type} (R : ℕ → A → B → IProp GF)

omit [conerisGS GF] in
/-- Rocq: `big_sepL_exists`. -/
theorem big_sepL_exists (vs : List B) :
    ([∗list] k ↦ v ∈ vs, ∃ x, R k x v) ⊢ ∃ xs, [∗list] k ↦ v;x ∈ vs;xs, R k x v := by
  induction vs generalizing R with
  | nil =>
    iintro -
    iexists []
    iapply BigSepL2.bigSepL2_nil.2
    itrivial
  | cons v vs IH =>
    iintro ⟨⟨%x, Hv⟩, Hvs⟩
    icases IH (fun k => R (k + 1)) $$ Hvs with ⟨%xs, Hxs⟩
    iexists x :: xs
    iframe

end array_zip

end proof

end Coneris.Lib.Array
