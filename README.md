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

**Goal.** `thurston_question_23` — the volumes are not all rationally related.
The stronger form, that their `ℚ`-span is infinite dimensional, is stated as
`thurston_question_23_strong`.

## Building

The package requires a local Mathlib checkout at `../mathlib4`, as in the
GillesCourtois collection; nothing is downloaded or rebuilt:

```
lake env lean Thurston23.lean
```

Only the `sorry` warnings on the three open targets should appear:
`hyperbolicVolumes_nonempty`, `thurston_question_23` and
`thurston_question_23_strong`.
