module

public import Metrology.Coneris.Examples.HashDir.ConHashImpl4Part2
public import Metrology.Coneris.ErrorRules

/-!
# A concurrent hash with per-key presampling tapes (part 3: `wp_hashfun_prev`, presampling)

Ported from clutch/theories/coneris/examples/hash/con_hash_impl4.v (`wp_hashfun_prev` and
`hashkey_presample`; see `ConHashImpl4` and `ConHashImpl4Part2` for the general mapping).

## Rocq → Lean mapping
* `wp_hashfun_prev`, `hashkey_presample`: same names; `f #k @ E` is `cpl(&f #k) @ E`,
  `RET #n` is `RET LitV (LitInt (n : ℤ))`.
* `hashkey_presample`: `bad : gset nat` is `bad : Finset ℕ`, `size bad` is `bad.card`,
  `ε εI εO : nonnegreal` are `ℝ≥0∞`, and the real inequality
  `εI * size bad + εO * (val_size + 1 - size bad) <= ε * (val_size + 1)` uses the truncated
  `ℝ≥0∞` subtraction, which does not truncate since every element of `bad` is `< S val_size`
  (so `bad.card ≤ val_size + 1`). This is the side condition of `state_step_err_set_in_out`
  (the `cond_nonneg` side conditions vanish). `fin (S val_size)` is `Fin (val_size + 1)`.

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

namespace Coneris.Examples.HashDir.ConHashImpl4

section con_hash_impl

variable {GF : BundledGFunctors} [conerisGS GF] [H : con_hashG GF]

/-- Rocq: `wp_hashfun_prev`. -/
theorem wp_hashfun_prev (N : Namespace) (E : CoPset) (f : val) (val_size max k n : ℕ)
    (γs : GName × GName × GName) (HE : ↑N ⊆ E) :
    {{ hashfunInv N γs val_size ∗ hashfun γs val_size max f ∗ hashkey γs k (some n) }}
      cpl(&f #k) @ E
    {{ RET LitV (LitInt (n : ℤ)); (hashfun γs val_size max f : IProp GF) }} := by
  unfold hashkey
  iintro %Φ ⟨#HI, Hhash, %α, #Hα, #Hkey⟩ HΦ
  unfold hashfun
  icases Hhash with ⟨%lvm, %ltm, %vm, %tm, %Hdom, %Hf, Hvm, Htm, HtmA, HvmA, #HkeysV⟩
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get lvm _ k $$ Hvm with %vret ⟨Hhash, %Hv⟩
  subst Hv
  rw [Std.ExtTreeMap.getElem?_map]
  cases Hvmk : vm[k]? with
  | some n' =>
    simp only [Option.map_some, opt_to_val]
    wp_pures
    ihave Hk := (BigSepM.bigSepM_lookup (M := nat_map) (i := k) (x := n') Hvmk) $$ HkeysV
    ihave %Heq := ghost_map_elem_agree (GF := GF) (H := nat_map) γs.1 k _ _ (some n') (some n)
      $$ [Hk Hkey]
    · iframe Hk Hkey
    obtain rfl : n' = n := Option.some.inj Heq
    imodintro
    iapply HΦ
    iexists lvm, ltm, vm, tm
    iframe
    isplitr
    · ipureintro
      exact Hdom
    isplitr
    · ipureintro
      rfl
    iexact HkeysV
  | none =>
    simp only [Option.map_none, opt_to_val]
    wp_pures
    wp_apply wp_get ltm _ k $$ Htm with %α' ⟨Htm, %Hα'⟩
    subst Hα'
    ihave %Hlk := ghost_map_lookup $$ HtmA Hα
    have Hlk' : tm[k]? = some α := Hlk
    rw [Std.ExtTreeMap.getElem?_map, Hlk']
    simp only [Option.map_some, opt_to_val]
    wp_pures
    wp_bind (Rand _ _)
    unfold hashfunInv hashfunI
    iinv HI with ⟨%m, >Hm, >Hkeys⟩ Hclose
    ihave %Hmk := ghost_map_lookup $$ Hm Hkey
    icases (BigSepM.bigSepM_lookup_acc (M := nat_map) (i := k) (x := some n) Hmk).1 $$ Hkeys
      with ⟨⟨%α'', #Hα'', Hk⟩, Hkeys⟩
    ihave %Heqα := ghost_map_elem_agree (GF := GF) (H := nat_map) γs.2.1 k _ _ α α''
      $$ [Hα Hα'']
    · iframe Hα Hα''
    subst Heqα
    imod ghost_map_insert (H := nat_map) k n Hvmk $$ HvmA with ⟨HvmA, HkV⟩
    unfold hashfunI_tape
    icases Hk with (Htape | #HkV')
    · wp_apply wp_rand_tape val_size α n [] (val_size : ℤ) (by simp) $$ Htape with ⟨-, %_⟩
      imod ghost_map_elem_persist $$ HkV with #HkV
      imod Hclose $$ [Hkeys Hm] with -
      · inext
        iexists m
        iframe Hm
        iapply Hkeys
        iexists α
        iframe Hα
        dsimp only
        iright
        iexact HkV
      imodintro
      wp_pures
      wp_apply wp_set lvm _ k (LitV (LitInt (n : ℤ))) $$ Hhash with Hhash
      wp_pures
      imodintro
      have hb := (BigSepM.bigSepM_insert (M := nat_map) (PROP := IProp GF)
        (Φ := fun k n => iprop(γs.1 ↪◯MAP[k]{.discard} (some n : Option ℕ))) (x := n) Hvmk)
      rw [nat_map_insert_eq] at hb ⊢
      iapply HΦ
      iexists lvm, ltm, vm.insert k n, tm
      rw [nat_map_map_insert]
      iframe
      isplitr
      · ipureintro
        exact Hdom
      isplitr
      · ipureintro
        rfl
      iapply hb.2
      iframe Hkey HkeysV
    · ihave %Hv := ghost_map_elem_valid_2 (GF := GF) (H := nat_map) γs.2.2 k _ _ n n
        $$ [HkV HkV']
      · iframe HkV HkV'
      exact absurd (DFrac.valid_own_op Hv.1) (by have : (1 : Qp).val = 1 := rfl; grind)

/-- Rocq: `hashkey_presample`. Presampling of hash key. -/
theorem hashkey_presample (N : Namespace) (E : CoPset) (val_size k : ℕ) (bad : Finset ℕ)
    (ε εI εO : ℝ≥0∞) (γs : GName × GName × GName) (HE : ↑N ⊆ E)
    (Hsize : ∀ x, x ∈ bad → x < val_size + 1)
    (Heps : εI * bad.card + εO * ((val_size : ℝ≥0∞) + 1 - bad.card) ≤
      ε * ((val_size : ℝ≥0∞) + 1)) :
    ⊢ hashfunInv N γs val_size -∗ hashkey γs k none -∗ ↯ ε -∗
      state_update E E iprop(∃ n : Fin (val_size + 1),
        ((⌜(n : ℕ) ∉ bad⌝ ∗ ↯ εO) ∨ (⌜(n : ℕ) ∈ bad⌝ ∗ ↯ εI)) ∗
          (hashkey γs k (some (n : ℕ)) : IProp GF)) := by
  unfold hashfunInv hashkey
  iintro #HI Hkey Herr
  imod inv_acc HE $$ HI with ⟨HI, Hclose⟩
  unfold hashfunI
  imod HI with ⟨%m, Hm, Hkeys⟩
  ihave %Hkm := ghost_map_lookup $$ Hm Hkey
  icases (BigSepM.bigSepM_delete (M := nat_map) (i := k) (x := none) Hkm).1 $$ Hkeys
    with ⟨⟨%α, #Hk, Hα⟩, Hkeys⟩
  unfold hashfunI_tape
  imod state_step_err_set_in_out val_size bad ε εI εO (E \ ↑N) α [] Hsize Heps $$ Hα Herr
    with ⟨%n, Herr, Htape⟩
  simp only [List.nil_append]
  imod ghost_map_update (some (n : ℕ)) $$ Hm Hkey with ⟨Hm, Hkey⟩
  imod ghost_map_elem_persist $$ Hkey with #Hkey
  imod Hclose $$ [Hkeys Htape Hm] with -
  · inext
    iexists (Iris.Std.insert m k (some (n : ℕ)))
    iframe Hm
    iapply (BigSepM.bigSepM_insert_delete (M := nat_map)).2
    iframe Hkeys
    iexists α
    iframe Hk
    dsimp only
    ileft
    iexact Htape
  imodintro
  iexists n
  iframe Herr
  iexists α
  iframe Hk Hkey

end con_hash_impl

end Coneris.Examples.HashDir.ConHashImpl4
