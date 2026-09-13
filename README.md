# Thurston's Question 23 — formalization bundle

A Lean 4 / Mathlib definition bundle and statement of the twenty-third of the
twenty-four questions in Thurston, *Three-dimensional manifolds, Kleinian groups
and hyperbolic geometry*, Bull. Amer. Math. Soc. **6** (1982), 357–381, prepared
as a [Prove2Me](https://prove2.me) mission.

* `Thurston23.lean` — the bundle: hyperbolic `3`-space, its volume and distance,
  Kleinian actions, fundamental domains, the set of volumes; two milestones and
  the goal.
* `CatalanLogSin.lean` — the analytic core of the covolume: the log-sine integrals
  at `π/4` and `3π/4` are `-G/2` and `G/2`, `G` Catalan's constant, and
  `∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ = -G/3`. Depends on Mathlib only; imported by
  the bundle.
* `mission.md` — the mission description as submitted to the platform.
* `PROBLEMS.md` — the tracker: what is proved, what is open, and why.

**The question.** In Thurston's words (1982, p. 380): "Show that volumes of
hyperbolic 3-manifolds are not all rationally related." Some rational relations
are forced — a degree `n` cover has `n` times the volume — so the question is
whether every rational relation arises from commensurability; equivalently,
whether some two hyperbolic `3`-manifolds have irrational volume ratio. No such
pair is known. (The paraphrase "are the volumes rationally independent?",
common in secondary sources, is not Thurston's, and read literally is false.)

**Milestones.**

1. `volume_of_finite_index` — a subgroup of index `n` has a fundamental domain
   of `n` times the volume. This is the source of all known relations. **Proved**,
   via a general lemma on fundamental domains of a finite-index subgroup
   (`measure_eq_index_smul`) that Mathlib does not have, together with the
   countability of a Kleinian group, which follows from proper discontinuity
   (`countable_of_properlyDiscontinuous`) rather than being assumed.
2. `hyperbolicVolumes_nonempty` — at least one finite-volume hyperbolic
   `3`-manifold exists, so the goal is not vacuous. **Proved**, with the
   congruence subgroup `Γ(2 + i)` of the Picard group; see below.

**Sanity check.** `hvol_cusp_box` — the unit cusp box `[0,1]² × [1,∞)` has
hyperbolic volume `1/2`, so `hvol`, which is built with `Measure.comap`, is not
the zero measure (`hvol_ne_zero`). Nothing else in the bundle evaluates `hvol`
on a concrete set. `hvol` is moreover an `IsOpenPosMeasure`: every nonempty
open set has positive volume (`hvol_pos_of_isOpen`). `hdist_ofUpperHalfPlane` — on the vertical slice `y = 0`,
`hdist` is Mathlib's `UpperHalfPlane.dist`, so the hand-written metric agrees
with a reviewed one.

**Explicit Kleinian groups.** `isKleinian_translations` — the translations
`(x, y, t) ↦ (x + n, y, t)` are Kleinian, with the slab `0 ≤ x < 1` as a
fundamental domain of infinite volume; `isKleinian_bot` — so is the trivial
group, with all of `ℍ³`. Neither is collected by `hyperbolicVolumes`, which
asks for a finite positive volume, so Milestone 2's finiteness is not
decoration.

**Commensurability.** `hvol_ratio_rational_of_commensurable` — subgroups of one
Kleinian group with a common finite-index subgroup have quotients of rationally
related volume: Milestone 1 applied twice to one fundamental domain for the
intersection. This is the source of every known rational relation in
`hyperbolicVolumes`; the question is whether it is the only one. The general
form, `relIndex_smul_measure_eq`, holds for any countable group acting on any
measure space with an invariant measure.

**Milestone 2.** `instMulActionSL2C` — `SL(2, ℂ)` acts on `ℍ³` by Möbius
transformations, through the quaternion model `(x, y, t) ↦ x + y i + t j`. The
action stays in the half-space precisely because `det = 1`; it is by
isometries of `hdist` (`hdist_smul`) and preserves `hvol`
(`measurePreserving_smul`, via the Bruhat factorisation into translations,
dilations and the inversion, each a change of variables). The Picard group
`picard = SL(2, ℤ[i])` and every subgroup of it act properly discontinuously
(`properlyDiscontinuous_of_le_picard`): a compact set lies in a box, and an
element moving a point of the box into the box has all four entries bounded.
The congruence subgroup `gammaTwoI = Γ(2 + i)` has finite index in it
(`relIndex_gammaTwoI_picard`) and acts freely (`gammaTwoI_free`): a fixed
point forces the trace to be real of absolute value at most `2`, and the only
such Gaussian integer congruent to `2` modulo `2 + i` is `2`, which forces
`g = 1`. So `isKleinian_gammaTwoI` — the first inhabitant of `IsKleinian`.
Its fundamental domain is not written down: a free, properly discontinuous
action by homeomorphisms has a measurable one (`exists_isFundamentalDomain`,
Mathlib does not have it), of volume at most that of any set meeting every
orbit. Reduction theory for the Picard group (`exists_smul_mem_picardBox`:
maximise the height on the orbit, translate into `|x|, |y| ≤ ½`, and `|q| ≥ 1`
or else the inversion would raise the height) gives such a set: one translate
of the box per coset of `Γ(2 + i)`, finitely many. The box lies above height
`½`, so its volume is finite; `hvol ≠ 0` makes the domain's volume positive
(`exists_fundamentalDomain_gammaTwoI`).

**The Picard fundamental domain.** `isFundamentalDomain_halfBox` — the closed half
box `|x| ≤ ½`, `0 ≤ y ≤ ½`, `|q| ≥ 1` is a fundamental domain for the Picard group
modulo the elements acting trivially. Covering is the reduction theory above, folded
by `z ↦ -z`; uniqueness on the open box is the three-dimensional analogue of
`Mathlib/NumberTheory/Modular.lean`; and the boundary, four coordinate planes and the
unit sphere, is null. This is what pins the covolume to a number: the volume of the
box is `G/3`, `G` Catalan's constant, by Humbert's formula, and
`exists_fundamentalDomain_gammaTwoI_eq_nsmul` makes the covolume of `Γ(2 + i)` a
positive integer multiple of it.

**Catalan's constant.** `hvol_halfBox_eq_catalan` — the volume of the box is
`G/3`, so the covolume of `Γ(2 + i)` is a positive integer multiple of `G/3`
(`exists_fundamentalDomain_gammaTwoI_eq_catalan`) and some hyperbolic volume is a
rational multiple of Catalan's constant (`exists_hyperbolicVolume_rat_mul_catalan`).
The three-dimensional integral reduces to a plane integral by Tonelli, the plane
integral goes to polar coordinates, where the angle folds onto `[0, π/4]`, and the
result is `-∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ`. The analytic side is
`CatalanLogSin.lean`: `integral_log_two_sin`, `∫₀^{π/4} log (2 sin θ) dθ = -G/2`,
by running the Taylor series of `log (1 - z)` along a circle of radius `r < 1`,
integrating term by term, and taking `r → 1` (Abel's limit theorem on the series
side, dominated convergence on the integral side); Mathlib has the log-sine value
at `π/2` but not at `π/4`, and no Catalan constant. The identity
`sin 3θ = sin θ (4 cos²θ - 1)` then turns the box integrand into three log-sine
integrals. See `PROBLEMS.md`, section H.

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
mkdir -p .lake/build/lib/lean
lake env lean -o .lake/build/lib/lean/CatalanLogSin.olean CatalanLogSin.lean
lake env lean Thurston23.lean
```

The second command compiles `CatalanLogSin.lean`, which the bundle imports, to
where `lake env` looks for it. Only the `sorry` warnings on the two open targets
should appear: `thurston_question_23` and `thurston_question_23_strong`.

## Licence

Apache License 2.0, the licence Mathlib uses, so that anything here can be
upstreamed or reused without friction. See `LICENSE`.
