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
closed formula; a Kleinian group is a group acting freely and properly
discontinuously by hyperbolic isometries; and the volume of the quotient
manifold is the measure of a fundamental domain.

Two milestones are stated: that passing to a subgroup of index `n` multiplies
the volume by `n`, which is the source of every known rational relation between
volumes, and that the set of volumes is nonempty, without which the goal would
be vacuous.
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

/-- A Kleinian group: a group acting on hyperbolic `3`-space by hyperbolic
isometries, freely and properly discontinuously. The quotient of `ℍ³` by such
an action is a hyperbolic `3`-manifold, and every hyperbolic `3`-manifold
arises this way. -/
structure KleinianAction (G : Type) [Group G] where
  /-- the action map -/
  act : G → H3 → H3
  one_act : ∀ p, act 1 p = p
  mul_act : ∀ g h p, act (g * h) p = act g (act h p)
  /-- each element acts by a hyperbolic isometry -/
  isometry : ∀ g p q, hdist (act g p) (act g q) = hdist p q
  /-- the action is free: no element except the identity fixes a point -/
  free : ∀ g : G, g ≠ 1 → ∀ p, act g p ≠ p
  /-- the action is properly discontinuous -/
  properly_discontinuous :
    ∀ K : Set H3, IsCompact K → {g : G | (act g '' K ∩ K).Nonempty}.Finite

/-- `F` is a fundamental domain for the action of the subgroup `H` on `ℍ³`:
every point of `ℍ³` has exactly one translate in `F` under `H`. -/
def IsFundDomain {G : Type} [Group G] (A : KleinianAction G) (H : Subgroup G)
    (F : Set H3) : Prop :=
  MeasurableSet F ∧ ∀ p : H3, ∃! g : H, A.act (g : G) p ∈ F

/-- The set of volumes of finite-volume hyperbolic `3`-manifolds: the measures
of fundamental domains of Kleinian actions. -/
def hyperbolicVolumes : Set ℝ :=
  {v | ∃ (G : Type) (_ : Group G) (A : KleinianAction G) (F : Set H3),
      IsFundDomain A ⊤ F ∧ hvol F = ENNReal.ofReal v ∧ 0 < v}

/-! ## Milestones -/

/-- **Milestone 1.** Passing to a subgroup of index `n` multiplies the volume
by `n`: a fundamental domain for `H` is the union of `n` translates of a
fundamental domain for `G`. This is the source of every known rational relation
between the volumes of hyperbolic `3`-manifolds: commensurable manifolds, that
is manifolds with a common finite cover, have rationally related volumes. -/
theorem volume_of_finite_index {G : Type} [Group G] (A : KleinianAction G)
    (H : Subgroup G) (n : ℕ) (hn : H.index = n) (hn0 : 0 < n)
    (F FH : Set H3) (hF : IsFundDomain A ⊤ F) (hFH : IsFundDomain A H FH)
    (v w : ℝ) (hv : hvol F = ENNReal.ofReal v) (hw : hvol FH = ENNReal.ofReal w) :
    w = n * v := by
  sorry

/-- **Milestone 2.** There is at least one finite-volume hyperbolic
`3`-manifold, so the set of volumes is nonempty. Without this the goal below
would be vacuously false rather than open. -/
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
