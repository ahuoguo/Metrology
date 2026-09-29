module

public import Metrology.Coneris.Examples.HashDir.SeqHashImplPart2

/-!
# A sequential hash implementation against the collision-free hash view interface
(part 3: hashing a fresh key)

Ported from clutch/theories/coneris/examples/hash/seq_hash_impl.v (`wp_insert_no_coll` and the
class `seq_hashG_impl`).

## Rocq → Lean mapping
* `wp_insert_no_coll` (same name): `f #n α` (with `α : val`) is `cpl(&f #n &α)`.
* `Class seq_hashG_impl `{conerisGS Σ, rand_spec} := { seq_hashG_impl_rand : randG Σ;
  seq_hashG_impl_abstract_tapesGS : abstract_tapesGS Σ }` is the Lean class `seq_hashG_impl`
  over `[conerisGS GF] [r : rand_spec GF]` with the same fields (the second one is an instance).
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Map Coneris.Lib.HocapRand Coneris.Lib.AbstractTape
open Coneris.Examples.HashDir.CollFreeHashViewInterface
open Coneris.Examples.HashDir.SeqHashInterface
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map nat_map_insert_eq)

namespace Coneris.Examples.HashDir.SeqHashImpl

section seq_hash_impl

variable {GF : BundledGFunctors} [conerisGS GF] [r1 : rand_spec GF] (L : r1.randG GF)
variable [hv1 : hash_view GF] (L' : hv1.hvG GF) [HinG' : abstract_tapesGS GF]
variable (val_size : ℕ)

/-- Rocq: `wp_insert_no_coll`. -/
theorem wp_insert_no_coll (E : CoPset) (f : val) (m : hmap) (n : ℕ) (tape_m : val_map (List ℕ))
    (x : ℕ) (xs : List ℕ) (γ1 : GName) (γ2 : hv1.hv_name) (α : val) (Hlookup : m[n]? = none) :
    {{ coll_free_hashfun L L' val_size f m tape_m γ1 γ2 ∗ hash_tape val_size α (x :: xs) γ1 }}
      cpl(&f #n &α) @ E
    {{ RET LitV (LitInt (x : ℤ));
        coll_free_hashfun L L' val_size f (m.insert n x) (tape_m.insert α xs) γ1 γ2 ∗
        hv1.hv_frag L' n x γ2 ∗
        hash_tape val_size α xs γ1 }} := by
  unfold coll_free_hashfun hashfun hash_tape
  iintro %Φ ⟨⟨⟨%h, %Hf, Hmap, %Hbound, Hauth, Htapes⟩, Hview, %Hnodup⟩, Htape⟩ HΦ
  subst Hf
  unfold compute_hash_specialized
  wp_pures
  wp_apply wp_get h _ n $$ Hmap with %vret ⟨Hhash, %Hv⟩
  subst Hv
  ihave %H := abstract_tapes_agree _ _ _ _ _ $$ Hauth Htape
  have Hlk := tapes_lookup_of_map tape_m α val_size val_size (x :: xs) H
  rw [Std.ExtTreeMap.getElem?_map, Hlookup]
  simp only [Option.map_none, opt_to_val]
  wp_pures
  ihave ⟨Htapes1, Htapes2⟩ := (BigSepM.bigSepM_insert_acc (M := val_map)
    (Φ := fun α t => r1.rand_tapes L α (val_size, t)) Hlk) $$ Htapes
  ihave %H' := r1.rand_tapes_valid L α val_size (x :: xs) $$ Htapes1
  wp_apply r1.rand_tape_spec_some L E α val_size x xs $$ Htapes1 with Htapes1
  wp_pures
  wp_apply wp_set h _ n _ $$ Hhash with Hlist
  wp_pures
  have Hperm := tape_m_elements_lookup tape_m α (x :: xs) Hlk
  have Hx : ∀ y ∈ m.toList.map (fun p => p.2), x ≠ y := by
    intro y hy hxy
    subst hxy
    have hx : x ∈ tape_m_elements tape_m := Hperm.mem_iff.mpr (by simp)
    exact List.disjoint_of_nodup_append Hnodup hx hy
  imod hv1.hv_auth_insert L' m n x γ2 Hlookup Hx $$ Hview with ⟨Hview, Hfrag⟩
  imod abstract_tapes_pop γ1 _ α val_size xs x $$ Hauth Htape with ⟨Hauth, Htape⟩
  ihave Htapes := Htapes2 $$ %xs Htapes1
  imodintro
  iapply HΦ
  iframe Hview Hfrag Htape
  simp only [val_map_insert_eq]
  rw [tapes_map_insert, hmap_map_insert]
  isplitl
  · iexists h
    iframe Hlist Hauth Htapes
    ipureintro
    refine ⟨rfl, ?_⟩
    intro ind i hi
    rw [Std.ExtTreeMap.getElem?_insert] at hi
    split at hi
    · cases hi; exact ⟨Nat.zero_le _, H' x List.mem_cons_self⟩
    · exact Hbound ind i hi
  ipureintro
  -- `NoDup` of the new used values
  have h1 := tape_m_elements_insert tape_m α xs
  have h2 := ((toList_insert_perm_nat m n x Hlookup).map (fun p => p.2))
  refine (List.Perm.nodup_iff ?_).mpr Hnodup
  refine (List.Perm.append h1 h2).trans ?_
  refine List.perm_middle.trans ?_
  refine List.Perm.trans ?_ (Hperm.append_right _).symm
  simp

end seq_hash_impl

/-- Rocq: `seq_hashG_impl`. -/
class seq_hashG_impl (GF : BundledGFunctors) [conerisGS GF] [r : rand_spec GF] where
  seq_hashG_impl_rand : r.randG GF
  seq_hashG_impl_abstract_tapesGS : abstract_tapesGS GF

attribute [reducible, instance] seq_hashG_impl.seq_hashG_impl_abstract_tapesGS

end Coneris.Examples.HashDir.SeqHashImpl
