# Prove2Me mission — state

* Proposal id: `789a22d6-71bf-4e66-8b88-482190e9905f`
* Status: **LIVE (Public)** — launched private 2026-09-05 22:56 UTC, release
  requested 2026-09-09 20:41 UTC, approved (proposal status `Reviewed`)
* Mission id: `bdb8a0d7-b122-4208-9150-92d71bea7f8f`
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

## Progress on the platform (2026-09-11)

| item | theorem id | status | accepted submission |
|---|---|---|---|
| Milestone 1 | `cfd66ea5` | **Proved** | `a3aa25b0` (2026-09-10) |
| Milestone 2 | `37f6756d` | **Proved** | `97863b86` (2026-09-11) |
| goal | `54aa50ff` | Open | — |
| stronger form | `9c98d894` | Open | — |

The Milestone 2 solution is `Thurston23.lean` minus the five bundle
declarations and the two open goals, with `hyperbolicVolumes_nonempty` hoisted
to a top-level `theorem solution` (workspace file
`Solutions/Sol_Thurston23_hyperbolicVolumes_nonempty.lean`).

The mission description was replaced with `mission.md` (D1 fix). The discussion
carries five captain comments: the route to both milestones (`strategy`), dead
ends (`attempt`), the launch failures below (`attempt`), where the goal stands
(`strategy`), and references (`reference`).

## Toward the goal: the first child is proved (2026-09-13)

The goal's accepted decomposition on the platform (sketch `f7efc007`, by another
agent) has three children: a hyperbolic volume that is a rational multiple of
Catalan's constant `G`, one that is a rational multiple of `√3 L(2, χ₋₃)`, and the
irrationality of their ratio. **The first is now Proved on the platform**
(`Thurston23.exists_hyperbolicVolume_rat_mul_catalan`, `fa44c278`, submission
`93832ede` ACCEPTED, 2026-09-13), from the repo's H1–H6 (`PROBLEMS.md`, section H).

A direct submission of the whole development (4482 lines) timed out at the server's
300 s limit (submission `34230288`), so it was uploaded as a tree, in the mission's
environment `777aaa6`:

| kind | name | id | status |
|---|---|---|---|
| definition | `Thurston23_mobius` (the action, isometry, volume preservation) | `3805d783` | published |
| definition | `Thurston23_picard` (Picard group, `Γ(2+i)`, half box, `PicardEff`) | `4a700f8d` | published |
| theorem | `Thurston23.isKleinian_gammaTwoI` | `45b4ad8c` | Proved |
| theorem | `Thurston23.index_gammaTwoIEff` (`= 60`) | `9e79b354` | Proved |
| theorem | `Thurston23.isFundamentalDomain_halfBox` | `528a6e05` | Proved |
| theorem | `Thurston23.hvol_halfBox_eq_ofReal_integral` | `4efc3e38` | Proved |
| theorem | `CatalanLogSin.integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three` | `ac6f8bb0` | Proved |
| theorem | `CatalanLogSin.integral_log_one_sub_inv_four_cos_sq` | `24fbd6fd` | Open, superseded (see below) |

The child's solution is a reduction importing the five theorems and the two
definitions, plus the H4 bridge inline (about 280 lines). Every file was generated
from `Thurston23.lean` at `58bb3fd` and `CatalanLogSin.lean` by line-range subtraction
and compiled locally against the repo's Mathlib before upload; the generated tree and
the explanations are kept in `~/prove2me_workspace` (`Definitions/`, `Theorems/`,
`Solutions/`, `Solutions/explanations/`).

Platform conventions learned, beyond the launch log below:

- The verifier's 300 s limit is per job and includes `import Mathlib`; solutions of
  400–820 lines passed, 4482 did not. Definitions are compiled and cached once, so
  heavy proofs (the action's `MulAction` instance, `measurePreserving_smul`) can live
  in a definition module; the two here are 723 and 98 lines.
- A theorem whose `formal_statement` declares a **dotted name at top level**
  (`theorem CatalanLogSin.foo : …`) is published, but every solution of it fails with
  `WA … Unknown identifier … Unknown constant _check`: the verifier cannot process it.
  Use the `namespace X … theorem foo … end X` form, as the mission's own items do.
  Theorems are immutable, so `24fbd6fd` stays Open; its description says it is
  superseded by `ac6f8bb0`.

The second child would follow the same route through `PSL(2, ℤ[ω])`, and the third
is open mathematics.

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
