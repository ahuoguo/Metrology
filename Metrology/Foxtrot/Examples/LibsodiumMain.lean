module

public import Metrology.Foxtrot.Examples.LibsodiumFork
public import Metrology.Foxtrot.Examples.LibsodiumRem
public import Metrology.Foxtrot.Examples.LibsodiumLoop
public import Metrology.Foxtrot.Examples.LibsodiumTapes
public import Metrology.Foxtrot.Examples.LibsodiumLoopRev

/-!
# `randombytes_uniform` from libsodium: the main results

Ported from clutch/theories/foxtrot/examples/libsodium.v (part 3: main lemmas)

`randombytes_uniform MAX` (rejection sampling) is contextually equivalent to
`ideal_uniform MAX` (a single uniform sample).

## Rocq → Lean map
* `randombytes_uniform_refines_ideal`, `ideal_refines_randombytes_uniform`,
  `randombytes_uniform_equivalent_ideal`: same names. As in Rocq, the first two are proved by
  chains of `ctx_refines_transitive` through the intermediate programs of
  `Metrology.Foxtrot.Examples.Libsodium`; each link is a separate lemma:
  - `randombytes_uniform ≤ rbu_rem ≤ rbu_fork ≤ ideal_uniform`
    (`randombytes_uniform_refines_rem`, `rbu_rem_refines_fork`, `rbu_fork_refines_ideal`);
  - `ideal_uniform ≤ rbu_tapes ≤ rbu_rem ≤ rbu_rem_tape ≤ randombytes_uniform`
    (`ideal_refines_tapes`, `tapes_refines_rem`, `rem_refines_rem_tape`,
    `rem_tape_refines_randombytes_uniform`).
* The contextual refinements are between `Val (randombytes_uniform MAX)` etc. (Rocq: the
  coercion `of_val`), at the type `TArrow TNat TNat` (Rocq: `TNat → TNat`).

## Omitted
None.
-/

@[expose] public section

noncomputable section

open ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Examples.Libsodium

variable (MAX : ℕ)

/-- Rocq: `randombytes_uniform_refines_ideal`. -/
theorem randombytes_uniform_refines_ideal :
    (∅ : varmap type) ⊨ Val (randombytes_uniform MAX) ≤ctx≤ Val (ideal_uniform MAX) :
      TArrow TNat TNat :=
  ctx_refines_transitive _ _ _ _ _
    (ctx_refines_transitive _ _ _ _ _ (randombytes_uniform_refines_rem MAX)
      (rbu_rem_refines_fork MAX))
    (rbu_fork_refines_ideal MAX)

/-- Rocq: `ideal_refines_randombytes_uniform`. -/
theorem ideal_refines_randombytes_uniform :
    (∅ : varmap type) ⊨ Val (ideal_uniform MAX) ≤ctx≤ Val (randombytes_uniform MAX) :
      TArrow TNat TNat :=
  ctx_refines_transitive _ _ _ _ _ (ideal_refines_tapes MAX)
    (ctx_refines_transitive _ _ _ _ _ (tapes_refines_rem MAX)
      (ctx_refines_transitive _ _ _ _ _ (rem_refines_rem_tape MAX)
        (rem_tape_refines_randombytes_uniform MAX)))

/-- Rocq: `randombytes_uniform_equivalent_ideal`. -/
theorem randombytes_uniform_equivalent_ideal :
    (∅ : varmap type) ⊨ Val (randombytes_uniform MAX) =ctx= Val (ideal_uniform MAX) :
      TArrow TNat TNat :=
  ⟨randombytes_uniform_refines_ideal MAX, ideal_refines_randombytes_uniform MAX⟩

end Foxtrot.Examples.Libsodium
