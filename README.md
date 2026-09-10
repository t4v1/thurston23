# Thurston's Question 23 — formalization bundle

A Lean 4 / Mathlib definition bundle and statement of the twenty-third of the
twenty-four questions in Thurston, *Three-dimensional manifolds, Kleinian groups
and hyperbolic geometry*, Bull. Amer. Math. Soc. **6** (1982), 357–381, prepared
as a [Prove2Me](https://prove2.me) mission.

* `Thurston23.lean` — the bundle: hyperbolic `3`-space, its volume and distance,
  Kleinian actions, fundamental domains, the set of volumes; two milestones and
  the goal.
* `mission.md` — the mission description as submitted to the platform.

**The question.** Thurston asked whether the volumes of hyperbolic
`3`-manifolds are rationally independent. Literally the answer is no: a degree
`n` cover has `n` times the volume. The open question is whether every rational
relation between volumes arises from commensurability — equivalently, whether
some two hyperbolic `3`-manifolds have irrational volume ratio. No such pair is
known.

**Milestones.**

1. `volume_of_finite_index` — a subgroup of index `n` has a fundamental domain
   of `n` times the volume. This is the source of all known relations. **Proved**,
   via a general lemma on fundamental domains of a finite-index subgroup
   (`measure_eq_index_smul`) that Mathlib does not have, together with the
   countability of a Kleinian group, which follows from proper discontinuity
   (`countable_of_properlyDiscontinuous`) rather than being assumed.
2. `hyperbolicVolumes_nonempty` — at least one finite-volume hyperbolic
   `3`-manifold exists, so the goal is not vacuous.

**Sanity check.** `hvol_cusp_box` — the unit cusp box `[0,1]² × [1,∞)` has
hyperbolic volume `1/2`, so `hvol`, which is built with `Measure.comap`, is not
the zero measure (`hvol_ne_zero`). Nothing else in the bundle evaluates `hvol`
on a concrete set.

**Commensurability.** `hvol_ratio_rational_of_commensurable` — subgroups of one
Kleinian group with a common finite-index subgroup have quotients of rationally
related volume: Milestone 1 applied twice to one fundamental domain for the
intersection. This is the source of every known rational relation in
`hyperbolicVolumes`; the question is whether it is the only one. The general
form, `relIndex_smul_measure_eq`, holds for any countable group acting on any
measure space with an invariant measure.

**Toward Milestone 2.** `instMulActionSL2C` — `SL(2, ℂ)` acts on `ℍ³` by Möbius
transformations, through the quaternion model `(x, y, t) ↦ x + y i + t j`. The
action stays in the half-space precisely because `det = 1`; it is by
isometries of `hdist` (`hdist_smul`) and preserves `hvol`
(`measurePreserving_smul`, via the Bruhat factorisation into translations,
dilations and the inversion, each a change of variables). The Picard lattice
and its fundamental domain are the remaining steps (see `PROBLEMS.md`).

**Goal.** `thurston_question_23` — the volumes are not all rationally related.
The stronger form, that their `ℚ`-span is infinite dimensional, is stated as
`thurston_question_23_strong`.

## Building

The package requires a Mathlib checkout at `../mathlib4-thurston`, pinned to
commit `120ef86bf4` on Lean `v4.29.0-rc2` — the closest match to the platform
environment `777aaa6` (Lean v4.29.0-rc3) — with this package's `.lake/packages`
symlinked into it. A dedicated worktree rather than a shared clone, because a
shared clone follows Mathlib master and its toolchain moves under the build.
One-time setup from an existing clone, then nothing is rebuilt:

```
git -C ../mathlib4 worktree add --detach ../mathlib4-thurston 120ef86bf4
(cd ../mathlib4-thurston && lake exe cache get)
mkdir -p .lake && ln -s "$PWD/../mathlib4-thurston/.lake/packages" .lake/packages
lake env lean Thurston23.lean
```

Only the `sorry` warnings on the three open targets should appear:
`hyperbolicVolumes_nonempty`, `thurston_question_23` and
`thurston_question_23_strong`.
