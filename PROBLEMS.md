# Problems

The formalization tracker for Thurston's Question 23. One entry per theorem
or task; status is **proved** (in `Thurston23.lean` or `CatalanLogSin.lean`,
axiom-clean at Mathlib `120ef86bf4`), **open**, or **blocked** (needs
infrastructure listed under *depends on*). The two files are the package's
`lean_lib` targets, both default, so `lake build` compiles `CatalanLogSin` and then
the bundle, which imports it (commit `20339b7`; see the README's build section). Effort is a working estimate, not a promise. The Mathlib side
of the plan, with rationale, is on the plan page linked at the bottom.

Legend: `M` mission targets · `S` sanity and support theorems on the bundle ·
`L` Mathlib PR ladder · `D` documentation.

---

## M — Mission targets (Prove2Me `bdb8a0d7`)

### M1 · Milestone 1 — a subgroup of index `n` has `n` times the volume — **proved**
`volume_of_finite_index`. Proved via the general `measure_eq_index_smul`
together with `countable_of_properlyDiscontinuous`; no hypothesis was added
to the published statement. Commit `cd0f0c4`.

### M2 · Milestone 2 — the set of volumes is nonempty — **proved**
`hyperbolicVolumes_nonempty`, axiom-clean, with no change to the published
statement. Accepted on Prove2Me 2026-09-11 (submission `97863b86`). Needs a genuine lattice: `hyperbolicVolumes`
demands finite *and* positive volume, so the trivial group (infinite
volume) does not qualify. Route taken: the congruence subgroup `Γ(2+i)` of the
Picard group `SL(2, ℤ[i])`, whose reduction theory is the Euclidean algorithm
in `ℤ[i]` — the 3-dimensional analogue of `Mathlib/NumberTheory/Modular.lean`.
Everything is done inside the bundle's own `H3`; the Mathlib ladder (L5–L8)
was not a prerequisite. Sub-problems, in order (about 900 lines in all):

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
- **M2.6 · A fundamental domain of finite positive volume** — **proved**
  (`exists_fundamentalDomain_gammaTwoI`), ~330 lines, by a shorter route than
  planned: no explicit domain, no `PSL(2, ℤ[i])`, no uniqueness geometry, no
  null boundary. The planned route (the folded box `B⁺` as a strict
  fundamental domain for `PSL`, then transport) stays recorded in git history;
  only its covering half was needed.
  (i) *Existence* (`exists_isFundamentalDomain`, general): a free, properly
  discontinuous action by homeomorphisms of a second countable, locally
  compact Hausdorff space has a measurable fundamental domain. Each point has
  a neighbourhood no `g ≠ 1` maps into itself (`exists_nhds_smul_notMem`:
  a compact neighbourhood meets only finitely many of its translates, and
  Hausdorff separation handles those); countably many such open sets `U n`
  cover; keep a point of `U n` when its orbit misses every `U m`, `m < n`.
  (ii) *Upper bound* (`measure_le_of_forall_exists_smul_mem`): a fundamental
  domain has at most the measure of any set meeting every orbit, via
  Mathlib's `measure_eq_tsum`.
  (iii) *Reduction* (`exists_smul_mem_picardBox`): heights on a Picard orbit
  that are at least the starting one are `t / |c q + d|²` with finitely many
  Gaussian `(c, d)` (`finite_heights`), so a maximal one exists; translate it
  into `|x|, |y| ≤ ½`; then `|q| ≥ 1`, else `S` raises the height.
  (iv) *Finite volume*: the box lies above height `½` (`picardBox_subset`) and
  `[-½, ½]² × [½, ∞)` has finite `hvol` (`hvol_tallBox_lt_top`, the
  cusp-box computation without evaluating the integral); one translate per
  coset of `Γ(2+i)` in `picard` meets every `Γ(2+i)`-orbit, and there are
  finitely many cosets (`relIndex_gammaTwoI_picard`).
  (v) *Positive volume*: Mathlib's `IsFundamentalDomain.measure_ne_zero` with
  `hvol_ne_zero`.
- **M2.7 · Assemble** — **proved**: `hyperbolicVolumes_nonempty` from
  `isKleinian_gammaTwoI` and M2.6, with `v = (hvol F).toReal`.

### M3 · Goal — some two volumes have irrational ratio — **open mathematics**
`thurston_question_23`, `thurston_question_23_strong`. Not a formalization
task. Reduces, via Humbert, to irrationality of a ratio of `ζ_K(2)` values;
Thurston's own pointer `[Mil 2]` is to Milnor's Lobachevsky-function
independence conjecture (now Chowla–Milnor), which is open.

The platform decomposition's third child, `catalan_ne_rat_mul_sqrt_three_LChiMinusThree`
(`7a432ef7`: `G ≠ q √3 L(2, χ₋₃)` for every `q : ℚ`), is exactly this open core. Numerically
`G / (√3 L(2, χ₋₃)) = 0.6768608078…` (the platform description's `0.6768661…` is off in the
sixth digit), with continued fraction `[0; 1, 2, 10, 1, 1, 3, 3, 1, 1, 2, 17, …]`.

- **M3.1 · Finite shadow: no rational of denominator below `1733`** — **proved**:
  `catalan_ne_rat_mul_sqrt_three_LChiMinusThree_of_den_lt`, in `CatalanEisensteinRatio.lean`
  (Mathlib only), is the third child's statement under the extra hypothesis `q.den < 1733`.
  Tails of `∑ 1/(mk+c)²` are bracketed by telescoping sums, `[1/(my) - (m/12)/y³, 1/(my)]` with
  `y = c - m/2` (`tsum_le`, `le_tsum`); forty terms give `G ∈ [0.91596551, 0.91596568]` and
  `L(2, χ₋₃) ∈ [0.78130225, 0.78130260]` (`catalan_bounds`, `lchi3_bounds`), so the ratio lies
  strictly between the Farey neighbours `664/981` and `509/752` (`ratio_mem`), and a fraction
  strictly between Farey neighbours `a/b < c/d` has denominator at least `b + d`
  (`add_le_den_of_farey`). More terms push the bound up (sixty terms: `2714`), but no finite
  computation reaches the statement itself.

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

### S3 · `hdist` agrees with Mathlib's `UpperHalfPlane.dist` on the `y = 0` slice — **proved**
`hdist_ofUpperHalfPlane`: for `z w : UpperHalfPlane`,
`hdist (ofUpperHalfPlane z) (ofUpperHalfPlane w) = dist z w`, where
`ofUpperHalfPlane z = ⟨![z.re, 0, z.im], _⟩`. The only available
certification of the bundle's metric against a reviewed definition. No real
analysis was needed: Mathlib already has
`UpperHalfPlane.cosh_dist : cosh (dist z w) = 1 + |z − w|² / (2 Im z Im w)`,
which is exactly the bundle's `cosh` argument on the slice, and the logarithm
in `hdist` is by definition `Real.arcosh`, so `Real.arcosh_cosh` finishes.
About 20 lines.

### S4 · Two explicit Kleinian groups — **proved**
(i) `isKleinian_bot : IsKleinian (⊥ : Subgroup SL(2, ℂ))`, with `hvol_univ`:
all of `H3` has infinite volume. The trivial group taken as `⊥` rather than
`Unit`, so that no new `MulAction` instance on `H3` is needed.
(ii) `translations = zpowers (T 1)`, acting by `(x, y, t) ↦ (x + n, y, t)`:
`isKleinian_translations`, with the slab `0 ≤ x < 1` as a fundamental domain
(`isFundamentalDomain_xSlab`) of *infinite* volume (`hvol_xSlab`), collected in
`exists_isKleinian_fundamentalDomain_infinite_volume`. So M2's finiteness
demand is doing real work: this group is Kleinian but contributes nothing to
`hyperbolicVolumes`.

No new action was needed: the translations sit inside `SL(2, ℂ)`, so isometry,
measure preservation and proper discontinuity come from M2.1–M2.4
(`hdist_smul`, `measurePreserving_smul`, `properlyDiscontinuous_of_le_picard`),
and freeness is `x + n ≠ x`. The fundamental domain is `IsFundamentalDomain.mk'`
with `n = -⌊x⌋`. Infinite volume is where S5 pays off: the slab is the disjoint
union of the `ℤ`-many `y`-translates of its unit cell, each of the same volume
by invariance, and that volume is positive because the cell contains a nonempty
open set. About 190 lines.

### S5 · `hvol.IsOpenPosMeasure` — **proved**
Every nonempty open set has positive volume (the instance, and
`hvol_pos_of_isOpen`). Not given by S1, which only rules out the zero measure.
Two Mathlib lemmas and no computation: Lebesgue measure restricted to the open
half-space is open-positive (`IsOpenPosMeasure.comap` along
`isOpenEmbedding_subtypeVal`), and since the density `t⁻³` vanishes nowhere,
Lebesgue measure is absolutely continuous with respect to `hvol`
(`withDensity_absolutelyContinuous'`), which transfers the property
(`AbsolutelyContinuous.isOpenPosMeasure`). About 12 lines. Useful for S4(ii)
and for any future positivity argument.

---

## H — Humbert for `ℚ(i)`: the covolume as a multiple of Catalan's constant

The goal's accepted decomposition on the platform (sketch `f7efc007`, by another
agent) has three open children: a hyperbolic volume that is a rational multiple
of Catalan's constant `G = L(2, χ₋₄)`, one that is a rational multiple of
`√3 L(2, χ₋₃)`, and the irrationality of their ratio. The third is open
mathematics. The first is what this ladder proves, from the Picard machinery here:
`covol(PSL(2, ℤ[i])) = G/3` (`hvol_halfBox_eq_catalan`), hence `covol(Γ(2+i)) = 60 · G/3 = 20 G`
(`index_gammaTwoIEff`, `exists_fundamentalDomain_gammaTwoI_eq_twenty_catalan`), so
`20 G ∈ hyperbolicVolumes` and `exists_hyperbolicVolume_rat_mul_catalan`. The value `G/3`
was checked numerically to seven decimals before starting.

### H1 · Uniqueness on the open half box — **proved**
`eq_of_smul_mem_halfBoxOpen`: an element of the Picard group carrying a point of
`|x| < ½`, `0 < y < ½`, `|q| > 1` into that same set fixes it. With
`exists_smul_mem_picardBox` (the covering half, already proved) this is the
statement that the closed half box is a fundamental domain modulo `±1`. The
three-dimensional analogue of `Mathlib/NumberTheory/Modular.lean`, about 250
lines; see the section docstring for the argument.

### H2 · Covering for the *half* box — **proved**
`exists_smul_mem_halfBox`: `exists_smul_mem_picardBox` lands in the full box;
`R = diag(i, -i) ∈ picard` acts as `z ↦ -z` and folds `y < 0` back. 30 lines.

### H3 · The effective action and the fundamental domain — **proved**
`isFundamentalDomain_halfBox : IsFundamentalDomain PicardEff halfBox hvol`.
Three pieces:

- *The acting group.* `IsFundamentalDomain` needs a.e. disjoint translates and
  `-1` acts trivially, so the group is `PicardEff = picard ⧸ picardKer`, the
  quotient by the kernel of the action. Taking the kernel rather than `{±1}`
  costs nothing (normality is free, and `⟦g⟧ = 1` is exactly "g acts trivially"),
  and avoids having to prove that the kernel *is* `{±1}`.
- *Null boundary* (`hvol_halfBox_sdiff_halfBoxOpen`). The boundary lies in four
  coordinate planes and the unit sphere. Planes: `Measure.pi_hyperplane`. Sphere:
  transport to `EuclideanSpace ℝ (Fin 3)` along `PiLp.volume_preserving_toLp` and
  use `Measure.addHaar_sphere`. Then `hvol_preimage_eq_zero` carries a Lebesgue
  null set of `ℝ³` to an `hvol` null set of `H3`, through `hvol_apply`.
- *Assembly* via `IsFundamentalDomain.mk''`: covering is H2; for `⟦g⟧ ≠ 1` the
  intersection `⟦g⟧ • halfBox ∩ halfBox` lies in the boundary union its translate,
  because a point with both it and its `g⁻¹`-image in the *open* box makes `g` act
  trivially by H1, i.e. `⟦g⟧ = 1`.

H1's conclusion was strengthened for this from `g • p = p` to `∀ q, g • q = q`:
the proof already produced `g = ±1`, only the statement was throwing it away.

### H4 · The covolume of `Γ(2+i)` as a multiple of the box — **proved**
`exists_fundamentalDomain_gammaTwoI_eq_nsmul`: there are `n > 0` and a
fundamental domain `F` for `Γ(2+i)` with `hvol F = n • hvol halfBox`, together
with `hvol_halfBox_pos` and `hvol_halfBox_lt_top`.

The exact value `n = 60` is *not needed* for the platform child, which asks for a
**rational** multiple of Catalan's constant, so any finite index does; that
realization shrank this step a lot. Naming the constant, `covol(Γ(2+i)) = 20 G`, is
H6 below.

What is needed is the bridge: `n` is the index of `gammaTwoIEff`, the image of
`Γ(2+i)` in `PicardEff`, nonzero by `Subgroup.index_map_dvd` from
`relIndex_gammaTwoI_picard`; `isFundamentalDomain_iUnion_out` builds `F` from the
box; `measure_eq_index_smul` (M1) gives the volume; and
`isFundamentalDomain_of_eff` carries the domain back from the image to `Γ(2+i)`
itself, which is legitimate because `Γ(2+i) → PicardEff` is injective: an element
of `Γ(2+i)` acting trivially fixes a point, so it is the identity by freeness.

### H5 · `vol(half box) = G/3` — **proved**
`hvol_halfBox_eq_catalan : hvol halfBox = ENNReal.ofReal (catalan / 3)`, and with H4
`exists_fundamentalDomain_gammaTwoI_eq_catalan`: the covolume of `Γ(2+i)` is
`n · G/3` for a positive integer `n`. Hence
`exists_hyperbolicVolume_rat_mul_catalan : ∃ v ∈ hyperbolicVolumes, ∃ q : ℚ, v = q · G`,
the first of the three children of the goal in the platform's accepted decomposition.
A by-product is `catalan_pos`, positivity of Catalan's constant read off from the
positivity of the volume. `Thurston23.lean` now imports `CatalanLogSin.lean`; to make
the import resolvable both files became `lean_lib` targets in `lakefile.toml`, built by
`lake build` (Lake checks Mathlib's traces without rebuilding it, and deletes any olean
it did not write itself, so the earlier hand-compiled olean is no longer an option).

The analytic core is `CatalanLogSin.lean` (Mathlib only, no dependency on the bundle):

```lean
integral_log_two_sin : ∫ θ in (0:ℝ)..(π/4), log (2 * sin θ) = -(catalan / 2)
integral_log_one_sub_inv_four_cos_sq :
  ∫ θ in (0:ℝ)..π/4, log (1 - 1 / (4 * cos θ ^ 2)) = -(catalan / 3)
```

where `catalan = ∑ (-1)ⁿ/(2n+1)²` is defined there. Mathlib has the log-sine value at
`π/2` (`integral_log_sin_zero_pi_div_two`) but nothing at `π/4`, no Catalan constant,
Clausen or Lobachevsky function.

The proof of the value at `π/4`, in four steps:

1. `hasSum_neg_log_norm_circle`: the real part of the Taylor series of `-log (1 - z)`
   on the circle of radius `r < 1`, `-log ‖1 - r e^{iφ}‖ = ∑ rⁿ cos(nφ)/n`.
2. `integral_arc`: term-by-term integration over `θ ∈ [0, π/4]`, giving
   `∑ rⁿ sin(nπ/2)/(2n²)` for `|r| < 1`. The exchange is `integral_tsum` against a
   geometric bound.
3. `hasSum_boundary`: at `r = 1` the series is `G/2` (reindex to odd `n`, where
   `sin(nπ/2) = (-1)ᵐ`). Abel's limit theorem (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`)
   carries this to the limit `r → 1⁻` on the series side.
4. The integral side converges to `∫ log (2 sin θ)` by dominated convergence, with
   bound `log 2 + |log (sin 2θ)|` from `‖1 - r e^{iφ}‖² - sin²φ = (r - cos φ)²`
   (`abs_log_norm_le`), integrable by `intervalIntegrable_log_sin`. Uniqueness of
   limits closes it; `norm_one_sub_exp` is the boundary value `‖1 - e^{2iθ}‖ = 2 sin θ`.

The geometric half, in `Thurston23.lean`, three steps:

1. *3D → 2D.* `hvol_above_graph`: the volume of `{(x, y, t) : (x,y) ∈ D, g(x,y) ≤ t}`
   is `∫_D 1/(2 g²)`, by Tonelli with the height innermost (`splitEquiv`, the
   measure-preserving `ℝ³ ≃ ℝ × ℝ²`) and `lintegral_Ici_inv_cube : ∫_{t ≥ a} t⁻³ = 1/(2a²)`.
   Specialized: `hvol_halfBox_eq_plane_integral`, the volume is
   `∫_{boxBase} dx dy / (2(1 - x² - y²))` over `boxBase = [-½, ½] × [0, ½]`.
2. *Polar coordinates* (`lintegral_boxBase_eq`). The base is not a polar rectangle: a ray at
   angle `θ ∈ [0, π)` leaves it at `radialBound θ = 1/(2 max(|cos θ|, sin θ))`
   (`polarCoord_symm_mem_boxBase_iff`). Mathlib's `lintegral_comp_polarCoord_symm` and
   Tonelli give the iterated integral (`lintegral_boxBase_polar`); the inner one is
   `integral_radial : ∫₀^R r dr/(2(1 - r²)) = -¼ log (1 - R²)`, where the logarithm first
   appears. The angular integral over `[0, π]` then folds twice, by `θ ↦ π - θ` and
   `θ ↦ π/2 - θ`, onto `[0, π/4]`, where the bound is `1/(2 cos θ)` (`integral_g_fold`):
   `hvol halfBox = -∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ` (`hvol_halfBox_eq_ofReal_integral`).
   Folding the angle rather than the base means no Cartesian symmetry maps and no null
   boundaries: the only measure theory is Tonelli.
3. *Trigonometry* (`CatalanLogSin.integral_log_one_sub_inv_four_cos_sq`). The identity
   `sin 3θ = sin θ (4 cos²θ - 1)` writes `1 - 1/(4 cos²θ)` as
   `2 sin 3θ / (2 sin 2θ · 2 cos θ)`, so on `(0, π/4]` the integrand is
   `log (2 sin 3θ) - log (2 sin 2θ) - log (2 cos θ)`. Substituting, the three integrals are
   `⅓ ∫₀^{3π/4}`, `½ ∫₀^{π/2}` and `∫_{π/4}^{π/2}` of `log (2 sin u)`, worth `G/6`, `0`,
   `G/2`: the value at `π/2` is Mathlib's, the value at `π/4` is step 4 above, and the
   value at `3π/4` (`integral_log_two_sin_three_pi_div_four`) is `∫_{π/2}^{3π/4} =
   ∫_{π/4}^{π/2}` by `u ↦ π - u`. Total `-G/3`.

### H6 · The index is `60`: `covol(Γ(2+i)) = 20 G` — **proved**
`index_gammaTwoIEff : gammaTwoIEff.index = 60`, hence
`exists_fundamentalDomain_gammaTwoI_eq_twenty_catalan` (a fundamental domain of volume
`20 G`) and `twenty_catalan_mem_hyperbolicVolumes`. Three pieces, about 400 lines:

- *Reduction modulo `2 + i` is onto `SL(2, 𝔽₅)`* (`reduction_surjective`, section
  `IndexOfGamma`). Mathlib has no surjectivity of `SL(2, R) → SL(2, R/I)` in any form, so
  it is proved by lifting through `SL(2, ℤ)`: every class mod `2 + i` is the class of an
  integer (`exists_int_rep`), and the integers in `(2 + i)` are the multiples of `5`
  (`intCast_mem_idealTwoI_iff`), so a matrix over `ℤ[i]/(2+i)` of determinant one is a
  matrix of integers with `ad - bc ≡ 1 (mod 5)`. `exists_sl2Z_lift` lifts it: a first row
  with coprime integer lifts (if `5 ∤ b` take `a' = a + 5u(1 - a)` with `5u + bv = 1`, which
  is `≡ 1 (mod b)`; if `5 ∣ b` take `(a, 5)`), Bézout coefficients `u a' + v b' = 1` for
  the second row `(-v, u)`, and a lower unipotent correction `[[1,0],[t,1]]` whose residue
  `t` exists by `decide` over all residues (`exists_t_zmod`, `5⁶ · 5` cases).
- *`|SL(2, 𝔽₅)| = 120`* (`card_sl2_quot`). `ℤ[i]/(2+i)` has characteristic `5`
  (`charP_quotTwoI`), so `ZMod.castHom` is a ring isomorphism `𝔽₅ ≅ ℤ[i]/(2+i)`
  (`zmodFiveEquiv`), which transports `SL(2, ·)`; `SL(2, 𝔽₅)` is the quadruples with
  `ad - bc = 1` (`sl2Quad`), counted by `decide` (`card_quad`). Then
  `index_gammaTwoIZ : gammaTwoIZ.index = 120` by `Subgroup.index_ker`.
- *The kernel is `{±1}`* (section `KernelPmOne`). An element fixing every point is `±1`
  (`coe_eq_pm_one_of_forall_smul_eq`): the fixed-point equations at `(0,0,1)` and
  `(0,0,2)` force `b = c = 0`, at `(1,0,1)` they make the diagonal real, and the
  determinant makes it `±1`; the equations are those of `fixed_point_real`, extracted
  by `fixed_point_components`. So `picardKer = zpowers (-1)` and `Nat.card picardKer = 2`.
  And `-1 ∉ Γ(2+i)` because `-2 ∉ (2+i)` (`neg_one_notMem_gammaTwoI`).
- *Assembly* (section `IndexSixty`). `SL(2, ℤ[i]) ≃* picard` (`picardEquiv`, from
  injectivity) identifies `Γ(2+i).subgroupOf picard` with the image of the kernel
  `gammaTwoIZ`, so it is normal and of index `120` (`index_gammaTwoI_subgroupOf`);
  `Subgroup.index_map` makes the index of `gammaTwoIEff` that of `Γ ⊔ picardKer`, and
  `relIndex_sup_right` with `Γ ⊓ picardKer = ⊥` gives `[Γ ⊔ picardKer : Γ] = 2`.

### H7 · The second child: a volume that is a rational multiple of `√3 L(2, χ₋₃)` — **proved**
`exists_hyperbolicVolume_rat_mul_LChiMinusThree`, in `Thurston23Eisenstein.lean`: the covolume of
the congruence subgroup `Γ(3 + ω)` of the Bianchi group `SL(2, ℤ[ω])`, `ω = e^{2πi/3}`, is
`n · √3 L(2, χ₋₃)/8` for a positive integer `n` (`exists_fundamentalDomain_gammaSeven_eq_lchi3`),
where `L(2, χ₋₃) = ∑ (1/(3n+1)² - 1/(3n+2)²)`. The route is H1–H5 for `ℤ[ω]`; what changed:

- *The ring.* Mathlib has no Eisenstein integers, so `EisInt` is the structure `a + bω` with the
  multiplication `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω`, and its `CommRing` instance is
  pulled back along the injective embedding in `ℂ` (`Function.Injective.commRing`). Norm
  `a² - ab + b²` (`normSq_toC`).
- *Proper discontinuity* is now stated once for any subgroup of `SL(2, ℂ)` with finitely many
  elements whose entries lie in a disc (`properlyDiscontinuous_of_finite_entries`); the Bianchi group
  qualifies since `2(a² - ab + b²) ≥ a², b²`.
- *The torsion-free subgroup* has level `3 + ω`, a prime of norm `7`: `a + bω ∈ (3 + ω)` iff
  `7 ∣ 2a + b` (`mem_idealP_iff`), so a trace `≡ 2` in `[-2, 2]` is `2`. Levels of norm `2`, `3`, `4`
  would not do: they leave `-1` or elements of order `3` in the subgroup.
- *The fundamental domain* is the box over the rhombus `0 ≤ x ≤ ½`, `0 ≤ x + √3 y ≤ 1`, a third of
  the hexagonal Voronoi cell of `ℤ[ω]` (`isFundamentalDomain_eisBox`). The Voronoi property on the
  rhombus is an affine function of `(x, x + √3 y)` whose corner values are nonnegative integer
  combinations of `n(n - 1)` (`cell_of_eisBase`, `cell_strict_of_eisBaseOpen`). Covering takes the
  nearest lattice point (`exists_nearest_eis`) and a rotation by `ω` or `ω²`, realised by
  `D(ω²)`, `D(ω)`. Uniqueness: `t² > ⅔` on the open box rules out `|c|² ≥ 2`, the Voronoi property
  rules out `|c| = 1`, and of the six units only `±1` square to a rotation that keeps the open
  rhombus (`eis_unit_cases`, `not_eisBaseOpen_rot`). The boundary lies in two coordinate planes, two
  planes `x + √3 y = c` (null as preimages of coordinate planes under a shear of determinant `1`,
  `volume_plane_sqrt3`), and the unit sphere.
- *The volume.* In polar coordinates the rhombus is `θ ∈ [-π/6, π/2]`,
  `r ≤ 1/(2 max(cos θ, cos(θ - π/3)))`; the angle folds by `θ ↦ θ - π/3` and `θ ↦ -θ` onto `[0, π/6]`:
  `hvol eisBox = -∫₀^{π/6} log (1 - 1/(4 cos²θ)) dθ` (`hvol_eisBox_eq_ofReal_integral`).
- *The analytic core*, `EisensteinLogSin.lean` (Mathlib and `CatalanLogSin.lean` only): the log-sine
  argument of H5 for a general endpoint `0 ≤ a < π/2`, `∫₀^a log (2 sin θ) = -∑ sin(2na)/(2n²)`
  (`integral_log_two_sin_eq_tsum`); at `a = π/3` the series is `(√3/4) L(2, χ₋₃)` by the residues of
  `n` mod `3` (`hasSum_sin_two_pi_div_three`); and the identity `sin 3θ = sin θ (4 cos²θ - 1)` gives
  `∫₀^{π/6} log (1 - 1/(4 cos²θ)) dθ = -√3 L(2, χ₋₃)/8`. So `hvol eisBox = √3 L(2, χ₋₃)/8`
  (`hvol_eisBox_eq`), Humbert's formula for `ℚ(√-3)`.

Not computed, and not needed: the index `n`. It should be `|PSL(2, 𝔽₇)| = 168`, by the argument of
H6 with `𝔽₇` in place of `𝔽₅`.

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

The same PR can carry `exists_isFundamentalDomain` (with
`exists_nhds_smul_notMem`) — a free, properly discontinuous action by
homeomorphisms of a second countable, locally compact Hausdorff space has a
measurable fundamental domain — and `measure_le_of_forall_exists_smul_mem`
(a fundamental domain has at most the measure of any set meeting every
orbit), both proved in M2.6. Mathlib has neither; with
`ProperlyDiscontinuousSMul` and `ContinuousConstSMul` in place of the explicit
hypotheses they are general-purpose.

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

### D1 · The docstring misquotes Thurston — **fixed** (repo `7b077a1`, platform 2026-09-11)
Module docstring, `README.md`, and `mission.md` said Thurston asked whether
volumes are "rationally independent" and then corrected that reading. His
actual wording (BAMS 1982, p. 380, `refs/`) is *"not all rationally
related"* — the paraphrase is Wikipedia's. The Lean statements are faithful.
Fixed in the module docstring, the goal docstring, the README and
`mission.md`; the live mission description was replaced with `mission.md`
through `PATCH /missions/:id`, which touches no published item. The same edit
narrowed an overstatement in *Significance*: sharing an invariant trace field
forces rationally related volumes only when that field has a single complex
place.

The published goal's docstring and natural-language statement (immutable)
already open with "not all rationally related"; they mention "rationally
independent" only as the literal reading that is false, not as Thurston's
words, so they need no change.

---

Plan page with rationale and sources:
https://claude.ai/code/artifact/3b88aaf6-5a20-4784-be6a-f926bc90a326
