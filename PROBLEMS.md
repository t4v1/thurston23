# Problems

The formalization tracker for Thurston's Question 23. One entry per theorem
or task; status is **proved** (in `Thurston23.lean`, axiom-clean at Mathlib
`120ef86bf4`), **open**, or **blocked** (needs infrastructure listed under
*depends on*). Effort is a working estimate, not a promise. The Mathlib side
of the plan, with rationale, is on the plan page linked at the bottom.

Legend: `M` mission targets · `S` sanity and support theorems on the bundle ·
`L` Mathlib PR ladder · `D` documentation.

---

## M — Mission targets (Prove2Me `bdb8a0d7`)

### M1 · Milestone 1 — a subgroup of index `n` has `n` times the volume — **proved**
`volume_of_finite_index`. Proved via the general `measure_eq_index_smul`
together with `countable_of_properlyDiscontinuous`; no hypothesis was added
to the published statement. Commit `cd0f0c4`.

### M2 · Milestone 2 — the set of volumes is nonempty — **in progress (M2.1–M2.5 done)**
`hyperbolicVolumes_nonempty`. Needs a genuine lattice: `hyperbolicVolumes`
demands finite *and* positive volume, so the trivial group (infinite
volume) does not qualify. Chosen route: the Picard group `SL(2, ℤ[i])`, whose
reduction theory is the Euclidean algorithm in `ℤ[i]` — the 3-dimensional
analogue of `Mathlib/NumberTheory/Modular.lean`. Everything is done inside
the bundle's own `H3`; the Mathlib ladder (L5–L8) is not a prerequisite.
Effort: months. Sub-problems, in order:

- **M2.1 · Möbius action of `SL(2, ℂ)` on `H3`** — **proved** (`instMulActionSL2C`).
  Model `H3` inside the quaternions as `{q | q.imK = 0 ∧ 0 < q.imJ}` via
  `Quaternion.ofComplex`; `g • q := (a q + b)(c q + d)⁻¹`. To prove: the
  denominator is nonzero on the half-space; the image has `imK = 0` and
  `imJ = t / D`, `D = |cz+d|² + |c|²t²` — this is where `det = 1` is used;
  `MulAction` laws by division-ring algebra (the complex entries sit to the
  left of `q` and commute among themselves). Transport to `H3 ≃ UHS`.
- **M2.2 · Isometry** — **proved** (`hdist_smul`). Via the two-sided
  factorisation `(p c + d)(g p − g q)(c q + d) = p − q` in the quaternions
  (`mobius_sub_factor`), which needs only that the entries commute and
  `ad − bc = 1`; taking `normSq` gives `|gp − gq|² = |p − q|² / (D_p D_q)`
  (`normSq_mobius_sub`), and the `cosh` argument is invariant.
- **M2.3 · Measure preservation** — **proved** (`measurePreserving_smul`).
  Reduced to three generator families via the Bruhat factorisation
  `g = T(a/c) · S · D(c) · T(d/c)` (`sl2_eq_of_ne_zero`); translations,
  the linear maps `D a` (`det = |a|⁶`) and the inversion `S` (Jacobian
  `invJac`, `det = |x|⁻⁶`, verified by `det_fin_three`) each go through one
  change-of-variables lemma `hvol_image_smul`, with preimages under `g`
  taken as images under `g⁻¹` (`measurePreserving_smul_of_image`) so no
  preimage is ever computed. Two Mathlib wrinkles recorded in the source:
  `ContinuousLinearMap.proj` must have its ring and family pinned or
  elaboration times out, and `HasFDerivAt.inv` does not exist (use
  `hasFDerivAt_inv` with `comp`).
- **M2.4 · The Picard group and proper discontinuity** — **proved**
  (`properlyDiscontinuous_of_le_picard`, `picard_properlyDiscontinuous`).
  `picard` is the range of `SpecialLinearGroup.map GaussianInt.toComplex`, so
  it is a subgroup for free and `SL(2, ℤ[i]) → picard` is available for
  M2.5; `mem_picard_iff` says it is exactly the matrices with Gaussian integer
  entries. A compact `K` lies in a box (`exists_box_of_isCompact`: heights in
  `[t₀, T]`, `|q|² ≤ R`); if `g` moves a point of the box into it, the heights
  give `|c q + d|² ≤ T/t₀`, and `|c q + d|² ≥ |c|² t²` bounds `c`, then `d`
  (`bottom_row_bound`); the same for `g⁻¹ = !![d, -b; -c, a]` bounds `a`, and
  `b = (g q)(c q + d) − a q` needs no case split on `c` (`entries_bound`).
  All bounds go through `|x + y|² ≤ 2(|x|² + |y|²)`, so no square root is
  taken. Stated for every subgroup of `picard`, which is the form M2.7 needs.
  ~200 lines.
- **M2.5 · A torsion-free finite-index subgroup** — **proved**
  (`relIndex_gammaTwoI_picard`, `gammaTwoI_free`, and with M2.2–M2.4
  `isKleinian_gammaTwoI`, the first inhabitant of `IsKleinian`).
  `gammaTwoIZ` is the kernel of reduction mod `(2+i)` in `SL(2, ℤ[i])` and
  `gammaTwoI` its image in `SL(2, ℂ)`. Finite index: `ℤ[i]/(2+i)` is covered
  by the residues `0, …, 4` (`i ≡ −2`, `5 = (2+i)(2−i)`; `omega` does the
  arithmetic), so `SL(2, ℤ[i]/(2+i))` is finite and the kernel has finite
  index; `relIndex_map_map_of_injective` carries it into `picard`. Freeness:
  at a fixed point the four components of `q (c q + d) = a q + b` and
  `|c q + d|² = 1` are pure real algebra (`fixed_point_real`), giving
  `tr g` real in `[−2, 2]`, and `tr g = 2 ⇒ g = 1` directly — no `±` case
  split: `tr − 2 ≡ 0 (mod 2+i)` with `tr − 2 ∈ [−4, 0]` already excludes
  `−I` (`eq_two_of_sub_two_mem`). ~250 lines.
- **M2.6 · A fundamental domain of finite positive volume** — open; the long
  pole. Big group: `PSL(2, ℤ[i]) := SL(2, ℤ[i]) ⧸ {±I}`, acting through
  `Quotient.lift` since `−I` acts trivially (the L4 trap). Domain: the
  folded box `B⁺ = {0 ≤ Re z ≤ ½, |Im z| ≤ ½, |z|² + t² ≥ 1}`; the fold by
  `z ↦ −z` is the element `diag(i, −i)`, which is why the unfolded box is
  *not* a fundamental domain for the Picard group. Sub-steps:
  (i) discreteness — `(c, d) ↦ |c z + d|² + |c|² t²` tends to `∞` on
  `ℤ[i]²`, so the orbit has a point of maximal height (Modular.lean's
  `exists_max_im`); (ii) covering — translate `z` into the box, fold, and
  if `|q| < 1` apply `S`, which raises the height, contradicting maximality;
  (iii) uniqueness on the interior — if `q, g q ∈ B⁺°` then `g = 1`: WLOG
  `|c q + d| ≤ 1`, and `t² > 1 − |z|² > ½` forces `|c|² < 2`; `c = 0` gives
  a translation or `z ↦ −z + b`, neither of which meets the open half-box;
  `c` a unit gives `|z − w|² < |z|²` for a Gaussian integer `w ≠ 0`, impossible
  for `0 < Re z < ½`, `|Im z| < ½`; (iv) the boundary is `hvol`-null — planes
  and a sphere, `hvol ≪ volume`; (v) `hvol B⁺ ≤ ∫₀^{½}∫_{−½}^{½}∫_{1/√2}^∞ t⁻³ < ∞`
  and `> 0`; (vi) transport: `Γ(2+i)` injects into `PSL` (its only element
  acting trivially is `1`, by `gammaTwoI_free`), its image has
  finite index (`relIndex_gammaTwoI_picard`), `isFundamentalDomain_iUnion_out`
  gives the domain, and `measure_eq_index_smul` its volume
  `index × hvol B⁺`, finite and positive. ~800 lines.
- **M2.7 · Assemble** `hyperbolicVolumes_nonempty` from `isKleinian_gammaTwoI`
  and M2.6's fundamental domain for `gammaTwoI`. ~20 lines.

### M3 · Goal — some two volumes have irrational ratio — **open mathematics**
`thurston_question_23`, `thurston_question_23_strong`. Not a formalization
task. Reduces, via Humbert, to irrationality of a ratio of `ζ_K(2)` values;
Thurston's own pointer `[Mil 2]` is to Milnor's Lobachevsky-function
independence conjecture (now Chowla–Milnor), which is open.

---

## S — Sanity and support theorems on the bundle

### S1 · `hvol` is not the zero measure — **proved**
`hvol_cusp_box : hvol (cuspBox) = 2⁻¹`, `hvol_ne_zero`. Closes the risk that
`Measure.comap` silently returned `0`. Commit `c23e0f4`.

### S2 · Commensurable subgroups have rationally related volumes — **proved**
`relIndex_smul_measure_eq` (general), `exists_rat_measure_eq`,
`IsKleinian.subgroup`, `mem_hyperbolicVolumes_of_subgroup`,
`hvol_ratio_rational_of_commensurable`. The positive half of Thurston's
framing. Converse is false (Ruberman). Commit `2a25c3f`.

### S3 · `hdist` agrees with Mathlib's `UpperHalfPlane.dist` on the `y = 0` slice — **open**
Statement: for `z w : ℍ`, `hdist ⟨![z.re, 0, z.im], _⟩ ⟨![w.re, 0, w.im], _⟩ = dist z w`.
Mathlib's distance is `2 · arsinh(|z−w| / 2√(Im z · Im w))`; the bundle's is
`arcosh` of `1 + |p−q|²/(2 p₃ q₃)` written as a logarithm. Bridge:
`cosh d = 1 + 2 sinh²(d/2)`. The only available certification of the
bundle's metric against a reviewed definition. Effort: an afternoon of real
analysis.

### S4 · Two explicit Kleinian groups — **open**
(i) `isKleinian_unit : IsKleinian Unit` — minutes.
(ii) ℤ acting by `(x, y, t) ↦ (x + n, y, t)`, with fundamental domain
`[0,1) × ℝ × ℝ₊` of *infinite* volume — shows the definitions have nontrivial
instances and that M2's finiteness demand is doing real work. Needs: the
action as a `MulAction (Multiplicative ℤ) H3`, isometry of `hdist` under
x-translation (the formula is translation-invariant termwise), measure
preservation (translation invariance of Lebesgue measure through `comap`),
freeness, proper discontinuity (bounded `x`-coordinate on a compact set).
Effort: an hour or two. Less urgent since M2.5: `isKleinian_gammaTwoI` is a
nontrivial inhabitant of `IsKleinian`, and `IsKleinian.subgroup` gives the
Kleinian half of (ii) for any translation subgroup of `Γ(2+i)`; only the
infinite-volume fundamental domain would remain.

### S5 · `hvol.IsOpenPosMeasure` — **open**
Every nonempty open set has positive volume. Not given by S1. Small; useful
for S4(ii) and for any future positivity argument.

---

## L — Mathlib PR ladder (dependency order)

### L1 · Covolume of a finite-index subgroup — **proved, not yet submitted**
`isFundamentalDomain_iUnion_out`, `measure_eq_index_smul`, plus S2's
`relIndex_smul_measure_eq` and the two `Subgroup` instances. Target file:
extend `MeasureTheory/Group/FundamentalDomain.lean`. Open work: state via
`covolume`, add `@[to_additive]`, check the additive form recovers
`ZLattice.covolume_div_covolume_eq_relIndex`, rename to Mathlib conventions.
Upstream API note: newer Mathlib makes `Commensurable` a pair of
`IsFiniteRelIndex` classes (`h.1.relIndex_ne_zero`, not `h.1`).

### L2 · Countability from proper discontinuity — **proved, not yet submitted**
`countable_of_properlyDiscontinuous`. Target:
`Topology/Algebra/ProperAction/ProperlyDiscontinuous.lean`. Open work:
restate against Mathlib's two-compact `ProperlyDiscontinuousSMul` class
(equivalent: apply the one-compact form to `K ∪ L`).

### L3 · Hyperbolic measure on ℍ² — **open**
`UpperHalfPlane.volume := dx dy / y²` and `SMulInvariantMeasure SL(2,ℝ) ℍ`.
No hyperbolic measure exists in Mathlib in any dimension. Independent
motivation: the Petersson inner product cannot currently be stated. Proof
route: `lintegral_image_eq_lintegral_abs_det_fderiv_mul`; the Möbius Jacobian
`1/|cz+d|⁴` cancels the density's `|cz+d|⁴`. This is the template L6 copies.

### L4 · `ModularGroup.fd` is a fundamental domain; covolume `π/3` — **blocked on L3 + PSL action**
Must be stated for PSL(2,ℤ): `−I` acts trivially, so `𝒟` is *not* a
fundamental domain for SL(2,ℤ) in Mathlib's sense. Mathlib has no
`MulAction PSL(2,ℤ) ℍ`; descend `SLAction` through the center first. Same
trap recurs for every lattice with torsion.

### L5 · Hyperbolic n-space, upper half-space model — **open, design decision first**
Three candidate models: general ℍⁿ over `EuclideanSpace ℝ (Fin n)`; ℍ³ inside
the quaternions; ℍ³ as `ℂ × ℝ₊` with the PSL(2,ℂ) action as two explicit
formulas. The third needs nothing from the quaternion library and makes L6's
invariance a copy of L3's. Take to Zulip (`#mathlib4`, "Hyperbolic space"
thread) before writing code. Precedent: mathlib4 PR #7861 proposed
`Geometry/Hyperbolic/` in 2023 and never merged.

### L6 · PSL(2,ℂ) acting on ℍ³ by isometries — **blocked on L5**
Under the `ℂ × ℝ₊` model the Jacobian is `1/D³` against a density that
transforms by `D³`, `D = |cz+d|² + |c|²t²`. Reference: Elstrodt–Grunewald–
Mennicke ch. 1.

### L7 · Kleinian groups and hyperbolic volume upstream — **blocked on L1, L2, L5, L6**
Where the bundle's definitions would land. `IsKleinian.properly_discontinuous`
should extend `ProperlyDiscontinuousSMul` rather than restate it. Do not edit
the live Prove2Me definition for this; it belongs in the upstream version.

### L8 · Bianchi groups, Humbert's formula, a torsion-free subgroup — **blocked on L5–L7**
Bianchi groups have torsion (PSL(2,ℤ) ⊂ each), so the manifold is a
finite-index torsion-free subgroup away; volume = index × Humbert via L1 in
its general form. Needs `ζ_K(2)` special values, which Mathlib lacks.
Multi-year.

---

## D — Documentation

### D1 · The docstring misquotes Thurston — **fixed in the repo** (`7b077a1`); platform copy still pending
Module docstring, `README.md`, and `mission.md` say Thurston asked whether
volumes are "rationally independent" and then correct that reading. His
actual wording (BAMS 1982, p. 380, `refs/`) is *"not all rationally
related"* — the paraphrase is Wikipedia's. The Lean statements are faithful.
Fixed in the module docstring, the goal docstring, the README and
`mission.md`. The copy of `mission.md` on Prove2Me still carries the old
wording; editing the published item resets its confirmation, so that waits
for the next forced re-audit.

---

Plan page with rationale and sources:
https://claude.ai/code/artifact/3b88aaf6-5a20-4784-be6a-f926bc90a326
