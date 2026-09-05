/-
# Thurston's Question 23: rational relations among hyperbolic volumes

Definition bundle and statements for a Prove2Me mission.

Thurston's twenty-third question, from *Three-dimensional manifolds, Kleinian
groups and hyperbolic geometry*, Bull. Amer. Math. Soc. **6** (1982), 357--381,
asks whether the volumes of hyperbolic `3`-manifolds are rationally
independent. Read literally the answer is no: a degree `n` cover has `n` times
the volume, so commensurable manifolds always have rationally related volumes.
The question as it is understood, and as it remains open, is whether the
volumes are *not all* rationally related, that is whether some two of them have
irrational ratio.

The bundle below fixes the meaning of every word in that sentence. Hyperbolic
`3`-space is the upper half-space; its volume is Lebesgue measure with density
`z⁻³`, which is the Riemannian volume of the hyperbolic metric written out, so
no Riemannian machinery is needed; the hyperbolic distance is given by its
closed formula; a Kleinian action is a free, properly discontinuous action by
hyperbolic isometries; and the volume of the quotient is the measure of a
fundamental domain in the sense of `MeasureTheory.IsFundamentalDomain`.

Isometries are not required to preserve orientation, so the set of volumes
below contains the volumes of non-orientable quotients as well; this enlarges
the set but not its `ℚ`-span, and both goals below are unaffected. That
isometries preserve the hyperbolic volume is a field of the structure rather
than a derived fact: deriving it amounts to classifying the isometry group of
`ℍ³`, which is not the subject of this mission.

Two milestones are stated: that passing to a subgroup of index `n` multiplies
the volume by `n`, which is the source of every known rational relation between
volumes, and that the set of volumes is nonempty, without which the goal would
be vacuous. Nothing here is proved: this is a statement bundle.
-/
import Mathlib

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

/-! ## Hyperbolic `3`-space -/

/-- The upper half-space model of hyperbolic `3`-space. -/
def H3 : Type := {p : Fin 3 → ℝ // 0 < p 2}

instance : MeasurableSpace H3 := Subtype.instMeasurableSpace
instance : TopologicalSpace H3 := instTopologicalSpaceSubtype

/-- The hyperbolic volume: Lebesgue measure with density `z⁻³`. This is the
Riemannian volume of the metric `(dx² + dy² + dz²)/z²` written out. -/
noncomputable def hvol : Measure H3 :=
  ((volume : Measure (Fin 3 → ℝ)).comap Subtype.val).withDensity
    fun p => ENNReal.ofReal ((p.1 2) ^ (3 : ℕ))⁻¹

/-- The hyperbolic distance, through the closed formula
`cosh d(p,q) = 1 + |p - q|² / (2 p₃ q₃)`, written with the logarithmic form of
`arcosh`. -/
noncomputable def hdist (p q : H3) : ℝ :=
  let c : ℝ := 1 + (∑ i, (p.1 i - q.1 i) ^ 2) / (2 * p.1 2 * q.1 2)
  Real.log (c + Real.sqrt (c ^ 2 - 1))

/-! ## Kleinian groups and the volumes of their quotients -/

/-- A Kleinian action: a group acting on hyperbolic `3`-space by hyperbolic
isometries, freely and properly discontinuously. The quotient by such an action
is a complete hyperbolic `3`-manifold; discreteness and torsion freeness are
consequences of the conditions below rather than extra hypotheses. Preservation
of `hvol` is stated as a field: it is true of every hyperbolic isometry, but
deriving it from `isometry` means classifying `Isom(ℍ³)`, which is not the
subject of this mission. -/
structure IsKleinian (G : Type) [Group G] [MulAction G H3] : Prop where
  /-- each element acts by a hyperbolic isometry -/
  isometry : ∀ (g : G) (p q : H3), hdist (g • p) (g • q) = hdist p q
  /-- each element preserves the hyperbolic volume -/
  measure_preserving : ∀ g : G, MeasurePreserving (fun p : H3 => g • p) hvol hvol
  /-- the action is free: no element except the identity fixes a point -/
  free : ∀ g : G, g ≠ 1 → ∀ p : H3, g • p ≠ p
  /-- the action is properly discontinuous -/
  properly_discontinuous :
    ∀ K : Set H3, IsCompact K → {g : G | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite

/-- The set of volumes of finite-volume hyperbolic `3`-manifolds: the measures
of fundamental domains of Kleinian actions. -/
def hyperbolicVolumes : Set ℝ :=
  {v | ∃ (G : Type) (_ : Group G) (_ : MulAction G H3), IsKleinian G ∧
      ∃ F : Set H3, MeasureTheory.IsFundamentalDomain G F hvol ∧
        hvol F = ENNReal.ofReal v ∧ 0 < v}

/-! ## Milestones -/

/-- **Milestone 1.** Passing to a subgroup of index `n` multiplies the volume
by `n`: a fundamental domain for `H` is the union of `n` translates of a
fundamental domain for `G`. This is the source of every known rational relation
between the volumes of hyperbolic `3`-manifolds — commensurable manifolds, that
is manifolds with a common finite cover, have rationally related volumes — and
it is what makes the literal reading of Question 23 false. Stated in `ℝ≥0∞` so
that no degenerate case is hidden by `ENNReal.ofReal`. -/
theorem volume_of_finite_index {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) (H : Subgroup G) (hH : 0 < H.index)
    (F FH : Set H3) (hF : MeasureTheory.IsFundamentalDomain G F hvol)
    (hFH : MeasureTheory.IsFundamentalDomain H FH hvol) :
    hvol FH = H.index • hvol F := by
  sorry

/-- **Milestone 2.** There is at least one finite-volume hyperbolic
`3`-manifold, so the set of volumes is nonempty. Without this the goal below
would be vacuously false rather than open. This is not a warm-up: it asks for a
concrete cofinite-volume Kleinian group together with a fundamental domain of
finite positive measure, and Mathlib has no `ℍ³`, no `Isom(ℍ³)` and no action of
`PSL(2,ℂ)` on the upper half-space. -/
theorem hyperbolicVolumes_nonempty : hyperbolicVolumes.Nonempty := by
  sorry

/-! ## The goal -/

/-- **Thurston's Question 23.** The volumes of hyperbolic `3`-manifolds are not
all rationally related: some two of them have irrational ratio.

Read literally, "the volumes are rationally independent" is false, since a
degree `n` cover has `n` times the volume (Milestone 1); the open question is
whether every rational relation arises that way. It is not known how to exhibit
a single pair of hyperbolic `3`-manifolds whose volumes have irrational ratio.
For arithmetic examples Humbert's formula expresses the volume of the Bianchi
quotient of an imaginary quadratic field `F` as `|δ_F|^{3/2} ζ_F(2) / 4π²`, so
the question reduces to the irrationality of a ratio of Dedekind zeta values at
`2`, a transcendence statement of the same difficulty as the irrationality of
`ζ(5)`. -/
theorem thurston_question_23 :
    ∃ v ∈ hyperbolicVolumes, ∃ w ∈ hyperbolicVolumes,
      ∀ q : ℚ, v ≠ (q : ℝ) * w := by
  sorry

/-- The stronger form in which the question is sometimes stated: the `ℚ`-span
of the set of volumes is infinite dimensional. -/
theorem thurston_question_23_strong :
    ∃ f : ℕ → ℝ, (∀ n, f n ∈ hyperbolicVolumes) ∧ LinearIndependent ℚ f := by
  sorry

end Thurston23
