module

public import Metrology.Foxtrot.Examples.VonNeumann

/-!
# The von Neumann trick: the second refinement step

Ported from clutch/theories/foxtrot/examples/von_neumann.v (part 2:
`wp_von_neumann_prog'_rand_prog`).

## Rocq → Lean map
* `wp_von_neumann_prog'_rand_prog`: same name.
* The local `pose`s `small`, `large`, `l1`, `l2` of the Rocq proof are the definitions
  `vn_small`, `vn_large`, `vn_l1`, `vn_l2` (with `x = Z.to_nat (n `min` N)` a parameter `m`);
  Rocq's `seq a k` is `List.range' a k` and `l ≫= (λ x, (λ y, (x, y)) <$> l')` is
  `l.flatMap (fun x => l'.map (fun y => (x, y)))` (definitionally `List.product l l'`).
* The inline side conditions of `pupd_couple_von_neumann_1` (proved in Rocq with
  `list_elem_of_bind`, `NoDup_bind`, `length_bind`, `length_seq`, and an induction for the bound
  `2 * ((x+1) * (S N' - x)) <= S (S N') * S (S N')`) are the lemmas `mem_vn_l1`, `mem_vn_l2`,
  `vn_l1_bound`, `vn_l2_bound`, `vn_nodup`, `vn_len`, `vn_len_pos`, `vn_len_bound`.

## Deviations
* `x := (n `min` N)%Z` is the natural number `min n N` (`n` is a natural number, from
  `lrel_nat`); the `ℤ` minimum returned by `wp_min_prog` is rewritten into it (`Nat.cast_min`).
* The bound `2 * ((x+1) * (S N - x)) ≤ S (S N) * S (S N)` is proved directly (it is
  `2ab ≤ (a + b)²` with `a + b = N + 2`) instead of by Rocq's induction.
* The invariant for the unary `lrel_ref` gets the namespace `UnaryRel.logN.@ l` explicitly
  (Rocq: `inv_alloc _ _ _` with a shelved namespace and proposition).
* The spec thread is bound to the `rand #1` of `flip` (`tp_bind`) before the Löb induction, so
  that the rejected case can apply the induction hypothesis directly.

## Added
* `vn_small`, `vn_large`, `vn_l1`, `vn_l2` and their lemmas (see above).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot Foxtrot.BinaryRel Foxtrot.Lib.Spawn Foxtrot.Lib.Par Foxtrot.Lib.Min
open Foxtrot.Lib.Conversion

namespace Foxtrot.Examples.VonNeumann

/-! ## The lists of `pupd_couple_von_neumann_1` -/

section lists

variable (N m : ℕ)

/-- Rocq: `small` (local `pose`), with `m = Z.to_nat x`. -/
def vn_small : List ℕ := List.range' 0 (m + 1)

/-- Rocq: `large` (local `pose`). -/
def vn_large : List ℕ := List.range' (m + 1) (N + 1 - m)

/-- Rocq: `l1` (local `pose`). -/
def vn_l1 : List (ℕ × ℕ) := (vn_small m).flatMap (fun x => (vn_large N m).map (fun y => (x, y)))

/-- Rocq: `l2` (local `pose`). -/
def vn_l2 : List (ℕ × ℕ) := (vn_large N m).flatMap (fun x => (vn_small m).map (fun y => (x, y)))

variable {N m}

theorem mem_vn_l1 (hm : m ≤ N) (a b : ℕ) :
    (a, b) ∈ vn_l1 N m ↔ a ≤ m ∧ m + 1 ≤ b ∧ b ≤ N + 1 := by
  simp only [vn_l1, vn_small, vn_large, List.mem_flatMap, List.mem_map, List.mem_range',
    Prod.mk.injEq]
  constructor
  · rintro ⟨a', ⟨i, hi, rfl⟩, b', ⟨k, hk, rfl⟩, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨a, ⟨a, by omega, by simp⟩, b, ⟨b - (m + 1), by omega, by omega⟩, rfl, rfl⟩

theorem mem_vn_l2 (hm : m ≤ N) (a b : ℕ) :
    (a, b) ∈ vn_l2 N m ↔ m + 1 ≤ a ∧ a ≤ N + 1 ∧ b ≤ m := by
  simp only [vn_l2, vn_small, vn_large, List.mem_flatMap, List.mem_map, List.mem_range',
    Prod.mk.injEq]
  constructor
  · rintro ⟨a', ⟨i, hi, rfl⟩, b', ⟨k, hk, rfl⟩, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨a, ⟨a - (m + 1), by omega, by omega⟩, b, ⟨b, by omega, by simp⟩, rfl, rfl⟩

theorem vn_l1_bound (hm : m ≤ N) : ∀ x ∈ vn_l1 N m, x.1 ≤ N + 1 ∧ x.2 ≤ N + 1 := by
  rintro ⟨a, b⟩ h
  rw [mem_vn_l1 hm] at h
  simp only
  omega

theorem vn_l2_bound (hm : m ≤ N) : ∀ x ∈ vn_l2 N m, x.1 ≤ N + 1 ∧ x.2 ≤ N + 1 := by
  rintro ⟨a, b⟩ h
  rw [mem_vn_l2 hm] at h
  simp only
  omega

theorem vn_nodup (hm : m ≤ N) : (vn_l1 N m ++ vn_l2 N m).Nodup := by
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · show (List.product (vn_small m) (vn_large N m)).Nodup
    exact List.Nodup.product (List.nodup_range' ..) (List.nodup_range' ..)
  · show (List.product (vn_large N m) (vn_small m)).Nodup
    exact List.Nodup.product (List.nodup_range' ..) (List.nodup_range' ..)
  · rintro ⟨a, b⟩ h1 ⟨a', b'⟩ h2 heq
    rw [mem_vn_l1 hm] at h1
    rw [mem_vn_l2 hm] at h2
    simp only [Prod.mk.injEq] at heq
    omega

theorem vn_len : (vn_l1 N m).length = (vn_l2 N m).length := by
  simp only [vn_l1, vn_l2, length_bind]
  exact Nat.mul_comm _ _

theorem vn_len_eq : (vn_l1 N m).length = (m + 1) * (N + 1 - m) := by
  simp only [vn_l1, length_bind, vn_small, vn_large, List.length_range']

theorem vn_len_pos (hm : m ≤ N) : 0 < (vn_l1 N m).length := by
  rw [vn_len_eq]
  exact Nat.mul_pos (by omega) (by omega)

theorem vn_len_bound (hm : m ≤ N) : 2 * (vn_l1 N m).length ≤ (N + 1 + 1) * (N + 1 + 1) := by
  rw [vn_len_eq]
  obtain ⟨b, hb⟩ : ∃ b, N + 1 - m = b := ⟨_, rfl⟩
  have hN : N + 1 + 1 = (m + 1) + b := by omega
  rw [hb, hN]
  nlinarith

end lists

section proof

variable (N : ℕ) (ad : val)
variable {GF : BundledGFunctors} [foxtrotRGS GF]

/-- Rocq: `wp_von_neumann_prog'_rand_prog`. -/
theorem wp_von_neumann_prog'_rand_prog (Ht : Htyped ad) (K : List ectx_item) (j : ℕ) :
    ⊢ j ⤇ fill K cpl(&rand_prog &ad) -∗
      WP cpl(&(von_neumann_prog' N) &ad)
        {{ v, ∃ v' : val, j ⤇ fill K (Val v') ∗
          (lrel_arr lrel_unit lrel_bool : lrel GF) v v' }} := by
  iintro Hspec
  unfold von_neumann_prog' rand_prog flip flipL
  wp_pures
  tp_pures j
  wp_alloc l as Hl
  wp_pures
  imod inv_alloc (UnaryRel.logN.@ l) ⊤
      iprop(∃ v1 : val, l ↦ v1 ∗ (UnaryRel.lrel_nat : UnaryRel.lrel GF) v1) $$ [Hl]
    with #Hinv
  · inext
    iexists _
    iframe Hl
    dsimp only [UnaryRel.lrel_nat]
    iexists 0
    ipureintro
    rfl
  wp_apply wp_fork $$ []
  · ihave H' := UnaryRel.typed_safe (GF := GF) _ [] _ Ht
    wp_bind (Val ad)
    iapply wp_wand $$ H'
    iintro %v #H
    dsimp only [UnaryRel.interp, UnaryRel.lrel_arr, UnaryRel.lrel_ref, UnaryRel.lrel_unit]
    ihave H2 := H $$ %_ []
    · iexists l
      isplit
      · ipureintro; rfl
      iexact Hinv
    unfold UnaryRel.refines UnaryRel.refines_def
    iapply wp_wand $$ H2
    iintro %_ -
    itrivial
  wp_pures
  iexists _
  iframe Hspec
  imodintro
  dsimp only [lrel_arr, lrel_unit]
  imodintro
  iintro %v1 %v2 %⟨h1, h2⟩
  subst h1 h2
  unfold BinaryRel.refines BinaryRel.refines_def
  iintro %K' %j' Hspec
  tp_pures j'
  tp_bind j' (Rand _ _)
  iloeb as IH generalizing Hspec
  wp_pures
  wp_bind (Load _)
  dsimp only [UnaryRel.lrel_nat]
  iinv Hinv with ⟨%v0, >Hl, >⟨%n, %h1⟩⟩ Hclose
  subst h1
  wp_load
  imod Hclose $$ [Hl]
  · inext
    iexists _
    iframe Hl
    iexists n
    ipureintro
    rfl
  imodintro
  wp_apply wp_min_prog (n : ℤ) (N : ℤ) ⊤ $$ [] with %z %Hz
  · itrivial
  subst Hz
  wp_pures
  wp_alloctape α as Hα
  wp_pures
  wp_alloctape β as Hβ
  wp_pures
  rw [← Nat.cast_min, Nat.cast_one]
  have hm : min n N ≤ N := min_le_right _ _
  imod pupd_couple_von_neumann_1 (N := N + 1) (vn_l1 N (min n N)) (vn_l2 N (min n N)) α β [] []
      j' _ ⊤ (vn_l1_bound hm) (vn_l2_bound hm) (vn_nodup hm) vn_len (vn_len_pos hm)
      (vn_len_bound hm) $$ [Hα] [Hβ] Hspec with ⟨%x, %y, %Hx, %Hy, Hα, Hβ, Hspec⟩
  · inext
    iexact Hα
  · inext
    iexact Hβ
  simp only [List.nil_append]
  obtain ⟨m, hmeq⟩ : ∃ m, min n N = m := ⟨_, rfl⟩
  rw [hmeq] at hm
  rw [hmeq]
  by_cases K1 : (x, y) ∈ vn_l1 N m
  · simp only [K1, ↓reduceIte]
    rw [mem_vn_l1 hm] at K1
    rw [fill_app_rctx _ _ (Val (LitV (LitInt 1)))]
    imod spec_int_to_bool ⊤ j' K' 1 $$ Hspec with Hspec
    rw [Z_to_bool_neq_0 1 (by decide)]
    wp_randtape
    wp_pures
    rw [decide_eq_true K1.1]
    wp_randtape
    wp_pures
    rw [decide_eq_false (by omega : ¬ y ≤ m)]
    wp_pures
    imodintro
    iexists _
    iframe Hspec
    dsimp only [lrel_bool]
    iexists true
    ipureintro
    exact ⟨rfl, rfl⟩
  by_cases K2 : (x, y) ∈ vn_l2 N m
  · simp only [K1, K2, ↓reduceIte]
    rw [mem_vn_l2 hm] at K2
    rw [fill_app_rctx _ _ (Val (LitV (LitInt 0)))]
    imod spec_int_to_bool ⊤ j' K' 0 $$ Hspec with Hspec
    rw [Z_to_bool_eq_0]
    wp_randtape
    wp_pures
    rw [decide_eq_false (by omega : ¬ x ≤ m)]
    wp_randtape
    wp_pures
    rw [decide_eq_false (by omega : ¬ m < y)]
    wp_pures
    imodintro
    iexists _
    iframe Hspec
    dsimp only [lrel_bool]
    iexists false
    ipureintro
    exact ⟨rfl, rfl⟩
  simp only [K1, K2, ↓reduceIte]
  rw [mem_vn_l1 hm] at K1
  rw [mem_vn_l2 hm] at K2
  wp_randtape
  wp_pures
  wp_randtape
  by_cases hx : x ≤ m
  · rw [decide_eq_true hx]
    wp_pure
    rw [decide_eq_true (by omega : y ≤ m)]
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    iapply IH $$ Hspec
  · rw [decide_eq_false hx]
    wp_pure
    rw [decide_eq_false (by omega : ¬ y ≤ m)]
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    iapply IH $$ Hspec

end proof

end Foxtrot.Examples.VonNeumann
