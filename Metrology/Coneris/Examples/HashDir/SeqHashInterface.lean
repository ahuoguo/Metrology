module

public import Metrology.Coneris.Examples.HashDir.CollFreeHashViewInterface
public import Metrology.Coneris.Lib.AbstractTape
public import Metrology.Coneris.ErrorRules

/-!
# Seq hash interface

Ported from clutch/theories/coneris/examples/hash/seq_hash_interface.v

(Rocq: "Not completed. To be deleted".)

## Rocq → Lean mapping
* `tape_m_elements` (same name): `gmap val (list nat)` is `val_map (List ℕ)` (from
  `Coneris.Lib.AbstractTape`, keyed by the scoped order on values); `concat (map_to_list m).*2`
  is `(m.toList.map (fun p => p.2)).flatten`.
* `Class seq_hash `{!conerisGS Σ} {h:hash_view} `{!hvG Σ} (val_size:nat)` is the Lean
  `class seq_hash GF [conerisGS GF] [h : hash_view GF] (L' : h.hvG GF) (val_size : ℕ)`, where
  `hash_view` is the collision-free hash view `CollFreeHashViewInterface.hash_view` (the one
  Rocq imports). The instance argument `!hvG Σ` is the explicit class parameter `L'`.
  Fields (same names): `init_hash`, `allocate_tape`, `compute_hash`, `seq_hashG`,
  `seq_hash_tape_gname`, `abstract_seq_hash`, `seq_hash_tape`, `seq_hash_tape_timeless`,
  `abstract_seq_hash_coll_free`, `seq_hash_presample`.
  - The implicit `{L : seq_hashG Σ}` is an explicit argument `(L : seq_hashG GF)`.
  - The instance field `seq_hash_tape_timeless ::` is re-exported as the global instance
    `seq_hash_seq_hash_tape_timeless`.
  - Errors are `ℝ≥0∞`: `nnreal_div (nnreal_nat a) (nnreal_nat b)` is
    `(a : ℝ≥0∞) / (b : ℝ≥0∞)`. The natural subtraction `S val_size - k` is kept. When it is `0`,
    Rocq's `nnreal_div _ 0` is `0` whereas the Lean `_ / 0` is `∞`; this case is irrelevant since
    then `k ≥ val_size + 1` and the premise `↯ (k / (val_size + 1))` is contradictory (`≥ 1`).
  - `length (map_to_list m)` is `m.toList.length`.
  - As in Rocq, the presample conclusion leaves the tape `ns` unchanged (the interface is
    unfinished upstream); it is transcribed literally.

## Omitted
* The commented-out Rocq fields (`incr_counter`, `tape_name`, `concrete_seq_hash`,
  `concrete_seq_hash_timeless`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.AbstractTape Coneris.Examples.HashDir.CollFreeHashViewInterface
open Coneris.Examples.HashDir.HashViewInterface (hmap nat_map)

namespace Coneris.Examples.HashDir.SeqHashInterface

/-- Rocq: `tape_m_elements`. -/
def tape_m_elements (tape_m : val_map (List ℕ)) : List ℕ :=
  (tape_m.toList.map (fun p => p.2)).flatten

/-- Rocq: `seq_hash`. -/
class seq_hash (GF : BundledGFunctors) [conerisGS GF] [h : hash_view GF] (L' : h.hvG GF)
    (val_size : ℕ) where
  -- * Operations
  init_hash : val
  allocate_tape : val
  compute_hash : val
  -- * Ghost state
  /-- The assumptions about `Σ`. -/
  seq_hashG : BundledGFunctors → Type
  seq_hash_tape_gname : Type
  -- * Predicates
  abstract_seq_hash (L : seq_hashG GF) (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (γ1 : seq_hash_tape_gname) (γ2 : h.hv_name) : IProp GF
  seq_hash_tape (L : seq_hashG GF) (α : val) (ns : List ℕ) (γ : seq_hash_tape_gname) : IProp GF
  -- * General properties of the predicates
  seq_hash_tape_timeless (L : seq_hashG GF) (α : val) (ns : List ℕ) (γ : seq_hash_tape_gname) :
    Timeless (seq_hash_tape L α ns γ)
  abstract_seq_hash_coll_free (L : seq_hashG GF) (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (γ1 : seq_hash_tape_gname) (γ2 : h.hv_name) :
    ⊢ abstract_seq_hash L f m tape_m γ1 γ2 -∗ ⌜coll_free m⌝
  seq_hash_presample (L : seq_hashG GF) (f : val) (m : hmap) (tape_m : val_map (List ℕ))
    (γ1 : seq_hash_tape_gname) (γ2 : h.hv_name) (α : val) (E : CoPset) (ε : ℝ≥0∞)
    (ns : List ℕ) :
    ⊢ abstract_seq_hash L f m tape_m γ1 γ2 -∗
      seq_hash_tape L α ns γ1 -∗
      ↯ (((m.toList.length + (tape_m_elements tape_m).length : ℕ) : ℝ≥0∞) /
          ((val_size + 1 : ℕ) : ℝ≥0∞)) -∗
      ↯ ε -∗
      state_update E E iprop(∃ (_n : ℕ),
        ↯ ((((val_size + 1 : ℕ) : ℝ≥0∞) /
            ((val_size + 1 - (m.toList.length + (tape_m_elements tape_m).length) : ℕ) : ℝ≥0∞)) *
            ε) ∗
        seq_hash_tape L α ns γ1 ∗
        abstract_seq_hash L f m tape_m γ1 γ2)

/-- Rocq: the instance field `seq_hash_tape_timeless`. -/
instance seq_hash_seq_hash_tape_timeless {GF : BundledGFunctors} [conerisGS GF]
    [h : hash_view GF] {L' : h.hvG GF} {val_size : ℕ} [s : seq_hash GF L' val_size]
    (L : s.seq_hashG GF) (α : val) (ns : List ℕ) (γ : s.seq_hash_tape_gname) :
    Timeless (s.seq_hash_tape L α ns γ) :=
  s.seq_hash_tape_timeless L α ns γ

end Coneris.Examples.HashDir.SeqHashInterface
