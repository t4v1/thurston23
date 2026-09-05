# Prove2Me mission — state

* Proposal id: `789a22d6-71bf-4e66-8b88-482190e9905f`
* Status: **LIVE (Private)** since 2026-09-05 22:56 UTC
* Mission id: `bdb8a0d7-b122-4208-9150-92d71bea7f8f`
* Former status: Draft, visibility **private** (no moderator step; it goes live at
  the captain's confirmation, and can be made public later — permanently)
* Environment: `777aaa6` (Lean v4.29.0-rc3), the platform environment closest to
  the local Mathlib checkout the bundle was verified against
* Fields: Differential Geometry, Geometry & Topology, Number Theory
* Type: OpenProblem

## Items (in order)

| kind | name | role |
|---|---|---|
| definition | `Thurston23.bundle` | ℍ³, `hvol`, `hdist`, `IsKleinian`, `hyperbolicVolumes` |
| theorem | `Thurston23.volume_of_finite_index` | Milestone 1 |
| theorem | `Thurston23.hyperbolicVolumes_nonempty` | Milestone 2 |
| theorem | `Thurston23.thurston_question_23` | **goal** |
| theorem | `Thurston23.thurston_question_23_strong` | stronger form |

Each item carries a read-back: the testimony of an independent auditor that was
given only the Lean code, with all prose stripped, and asked what it says.

## What remains, and it is the captain's alone

The platform does not allow an agent to submit. Open the proposal review page,
confirm each of the five items after comparing its read-back against the source,
then click **Submit Proposal**. On a private mission that publishes it directly,
with no moderator review; making it public later is permanent.

## Launch log — what the platform actually required

Four submit attempts failed; each error was a platform convention not documented
in the captain guide, and each was resolved by reading a working mission
(the symplectic one) rather than by guessing.

1. `definition_name` may not contain a dot — it must be a plain Lean identifier.
   `Thurston23.bundle` was rejected as "Compile failed"; renamed
   `Thurston23_bundle`.
2. Definition items take no `preamble` field, and the platform supplies none:
   the imports must be inside the definition body itself. Without them `ℝ`,
   `Set`, `Measure` were all unknown. Fixed by starting the bundle with
   `import Mathlib`.
3. Theorem items are not given the mission's definitions automatically. A
   published definition becomes the module `Definitions.Def_<definition_name>`,
   and each theorem's preamble must import it. `import Mathlib` alone left
   `H3`, `hvol`, `IsKleinian` unknown.
4. Editing an item resets its confirmation, so every edit costs a re-audit.

Also fixed before launch: the goal was initially attached to the wrong item —
the server appears to take the goal from the last entry of `item_order`, not
from the `main_item_id` sent with it.
