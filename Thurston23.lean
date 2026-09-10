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
be vacuous. Milestone 1 is proved below, from a general fact about fundamental
domains of a finite-index subgroup that Mathlib does not have, and `hvol` is
checked against one explicit value, the volume of a cusp box. The positive half of
Thurston's framing is also proved: commensurable subgroups of a Kleinian group
have rationally related volumes. Milestone 2 and the goal are left open.
-/
import Mathlib

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

/-! ## Hyperbolic `3`-space -/

/-- The upper half-space model of hyperbolic `3`-space. Declared as an
`abbrev` so that the measurable and topological structures of the subtype are
inherited, without naming any auto-generated instance. -/
abbrev H3 : Type := {p : Fin 3 → ℝ // 0 < p 2}

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


/-! ## Supporting material for Milestone 1

Mathlib relates the measures of two fundamental domains of the *same* action but
has nothing relating a group to a finite-index subgroup, so that is developed
here. `measure_eq_index_smul` is the general measure-theoretic statement;
`countable_of_properlyDiscontinuous` supplies the countability of the acting
group that Mathlib's fundamental-domain API requires throughout, and which for a
Kleinian group is a consequence of proper discontinuity rather than a hypothesis.
-/

section FundamentalDomains

open Pointwise

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] [MeasurableSpace X]
  {μ : Measure X} [SMulInvariantMeasure Γ X μ] [MeasurableConstSMul Γ X]

/-- `Γ ⧸ S` is a `def` wrapper around `Quotient`, so the generic instance for
quotients of a countable type does not fire on it. -/
instance instCountableQuotientGroup [Countable Γ] (S : Subgroup Γ) : Countable (Γ ⧸ S) :=
  Quotient.countable

/-- If `F` is a fundamental domain for `Γ` and `S ≤ Γ`, then the union of the translates
of `F` by the inverses of a set of representatives of `Γ ⧸ S` is a fundamental domain
for `S`. This is the geometric content of Milestone 1: a fundamental domain for a
subgroup is assembled from one copy of `F` per coset. -/
theorem isFundamentalDomain_iUnion_out [Countable Γ] {F : Set X}
    (hF : IsFundamentalDomain Γ F μ) (S : Subgroup Γ) :
    IsFundamentalDomain S (⋃ q : Γ ⧸ S, (Quotient.out q)⁻¹ • F) μ where
  nullMeasurableSet :=
    NullMeasurableSet.iUnion fun q => hF.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [hF.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    have hmem : (Quotient.out ((g : Γ ⧸ S)))⁻¹ * g ∈ S := by
      have := QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : Γ ⧸ S))
      simpa using this
    refine ⟨⟨_, hmem⟩, Set.mem_iUnion.2 ⟨(g : Γ ⧸ S), ?_⟩⟩
    show ((Quotient.out ((g : Γ ⧸ S)))⁻¹ * g) • x ∈ _
    rw [mul_smul]
    exact Set.smul_mem_smul_set hg
  aedisjoint := by
    intro h₁ h₂ hne
    have hsmul : ∀ (h : S) (s : Set X), h • s = ((h : Γ)) • s := fun _ _ => rfl
    show μ (h₁ • _ ∩ h₂ • _) = 0
    rw [hsmul, hsmul]
    simp only [Set.smul_set_iUnion, smul_smul, Set.iUnion_inter, Set.inter_iUnion]
    refine measure_iUnion_null fun q => measure_iUnion_null fun r => hF.aedisjoint ?_
    intro hcontra
    apply hne
    have key : ((h₂ : Γ))⁻¹ * (h₁ : Γ) = (Quotient.out q)⁻¹ * (Quotient.out r) := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hcontra, inv_mul_cancel_right]
    have hmem : (Quotient.out q)⁻¹ * (Quotient.out r) ∈ S :=
      key ▸ S.mul_mem (S.inv_mem h₂.2) h₁.2
    have hqr : q = r := by
      have h := QuotientGroup.eq.mpr hmem
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    subst hqr
    exact Subtype.ext (mul_right_cancel hcontra)

/-- **Milestone 1 in general form.** If `S` has finite index in `Γ`, a fundamental domain
for `S` has `S.index` times the measure of a fundamental domain for `Γ`. -/
theorem measure_eq_index_smul [Countable Γ] (S : Subgroup Γ) (hS : 0 < S.index)
    {F FS : Set X} (hF : IsFundamentalDomain Γ F μ) (hFS : IsFundamentalDomain S FS μ) :
    μ FS = S.index • μ F := by
  haveI : S.FiniteIndex := ⟨hS.ne'⟩
  haveI : Finite (Γ ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ S) := Fintype.ofFinite _
  have hd : Pairwise
      (Function.onFun (AEDisjoint μ) (fun q : Γ ⧸ S => (Quotient.out q)⁻¹ • F)) :=
    fun q r hqr => hF.aedisjoint fun h => hqr (Quotient.out_injective (inv_injective h))
  have hm : ∀ q : Γ ⧸ S, NullMeasurableSet ((Quotient.out q)⁻¹ • F) μ :=
    fun q => hF.nullMeasurableSet_smul _
  rw [hFS.measure_eq (isFundamentalDomain_iUnion_out hF S), measure_iUnion₀ hd hm]
  simp only [measure_smul, tsum_fintype, Finset.sum_const, Finset.card_univ]
  show _ = Nat.card (Γ ⧸ S) • μ F
  rw [Nat.card_eq_fintype_card]

end FundamentalDomains

section Countability

/-- A group acting properly discontinuously on a nonempty σ-compact space is countable:
every element moves the basepoint inside some member of a countable compact covering,
and each such member admits only finitely many elements. -/
theorem countable_of_properlyDiscontinuous {Γ Y : Type*} [Group Γ] [TopologicalSpace Y]
    [MulAction Γ Y] [SigmaCompactSpace Y] (x₀ : Y)
    (hpd : ∀ K : Set Y, IsCompact K →
      {g : Γ | ((fun p : Y => g • p) '' K ∩ K).Nonempty}.Finite) :
    Countable Γ := by
  have hcov : ∀ y : Y, ∃ n, y ∈ compactCovering Y n := fun y =>
    Set.mem_iUnion.mp (by rw [iUnion_compactCovering]; trivial)
  have hsub : (Set.univ : Set Γ) ⊆ ⋃ n : ℕ,
      {g : Γ | ((fun p : Y => g • p) '' (compactCovering Y n) ∩ compactCovering Y n).Nonempty} := by
    intro g _
    obtain ⟨a, ha⟩ := hcov x₀
    obtain ⟨b, hb⟩ := hcov (g • x₀)
    refine Set.mem_iUnion.2 ⟨max a b, g • x₀, ⟨x₀, ?_, rfl⟩, ?_⟩
    · exact compactCovering_subset Y (le_max_left a b) ha
    · exact compactCovering_subset Y (le_max_right a b) hb
  exact Set.countable_univ_iff.mp
    (((Set.countable_iUnion fun n => (hpd _ (isCompact_compactCovering Y n)).countable)).mono hsub)

end Countability

section H3Topology

/-- The defining condition of `H3` is open, so `ℍ³` is an open subset of `ℝ³`. -/
theorem isOpen_upperHalfSpace : IsOpen {p : Fin 3 → ℝ | 0 < p 2} :=
  isOpen_lt continuous_const (continuous_apply 2)

instance : LocallyCompactSpace H3 := isOpen_upperHalfSpace.locallyCompactSpace

/-- A basepoint of `ℍ³`, used to witness countability of a Kleinian group. -/
def basepoint : H3 := ⟨fun _ => 1, by norm_num⟩

end H3Topology

/-! ## A sanity check on `hvol`

`hvol` is built with `Measure.comap`, which returns the zero measure when its
measurability side conditions fail — silently, with every theorem about it
still type-checking. Nothing else in the bundle evaluates `hvol` on a concrete
set, so one value is computed here: the unit cusp box `[0,1]² × [1,∞)` has
hyperbolic volume `∫₀¹∫₀¹∫₁^∞ t⁻³ = 1/2`. Consequently `hvol ≠ 0`. -/

section CuspBox

open Set

set_option maxHeartbeats 400000

/-- The unit cusp box `[0,1] × [0,1] × [1,∞)`, as a subset of `ℝ³`. -/
def cuspBox : Set (Fin 3 → ℝ) := Set.pi Set.univ ![Icc 0 1, Icc 0 1, Ici 1]

/-- The hyperbolic volume of the unit cusp box is `∫₀¹∫₀¹∫₁^∞ t⁻³ = 1/2`. -/
theorem hvol_cusp_box : hvol (Subtype.val ⁻¹' cuspBox) = 2⁻¹ := by
  set S : Fin 3 → Set ℝ := ![Icc 0 1, Icc 0 1, Ici 1] with hS
  set h : Fin 3 → ℝ → ℝ := ![fun _ => 1, fun _ => 1, fun t => (t ^ 3)⁻¹] with hh
  set f : Fin 3 → ℝ → ℝ := fun i => (S i).indicator (h i) with hf
  have hSm : ∀ i, MeasurableSet (S i) := by
    intro i; fin_cases i
    · exact measurableSet_Icc
    · exact measurableSet_Icc
    · exact measurableSet_Ici
  have hBm : MeasurableSet cuspBox := MeasurableSet.univ_pi hSm
  have hemb : MeasurableEmbedding (Subtype.val : H3 → Fin 3 → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const (measurable_pi_apply 2))
  have hBsub : cuspBox ⊆ Set.range (Subtype.val : H3 → Fin 3 → ℝ) := by
    intro x hx
    have h2 : x 2 ∈ Ici (1 : ℝ) := Set.mem_univ_pi.1 hx 2
    exact ⟨⟨x, lt_of_lt_of_le one_pos h2⟩, rfl⟩
  set F : (Fin 3 → ℝ) → ENNReal := fun x => ENNReal.ofReal ((x 2 ^ (3 : ℕ))⁻¹) with hF
  have hFm : Measurable F := ((measurable_pi_apply 2).pow_const 3).inv.ennreal_ofReal
  -- Step 1: unfold `hvol` and transport the integral from `H3` to `ℝ³`.
  have step1 : hvol (Subtype.val ⁻¹' cuspBox) = ∫⁻ x in cuspBox, F x := by
    show ((volume : Measure (Fin 3 → ℝ)).comap Subtype.val).withDensity
      (fun p : H3 => F p.1) (Subtype.val ⁻¹' cuspBox) = _
    rw [withDensity_apply _ (hemb.measurable hBm), ← lintegral_indicator (hemb.measurable hBm),
      ← lintegral_indicator hBm]
    calc ∫⁻ p, (Subtype.val ⁻¹' cuspBox).indicator (fun p : H3 => F p.1) p
            ∂(volume.comap Subtype.val)
        = ∫⁻ p, cuspBox.indicator F (Subtype.val p) ∂(volume.comap Subtype.val) :=
          lintegral_congr fun p => rfl
      _ = ∫⁻ x, cuspBox.indicator F x ∂((volume.comap Subtype.val).map Subtype.val) :=
          (lintegral_map (hFm.indicator hBm) hemb.measurable).symm
      _ = ∫⁻ x, cuspBox.indicator F x ∂(volume.restrict (Set.range Subtype.val)) := by
          rw [hemb.map_comap]
      _ = ∫⁻ x, cuspBox.indicator F x := by
          rw [lintegral_indicator hBm, lintegral_indicator hBm, Measure.restrict_restrict hBm,
            Set.inter_eq_left.2 hBsub]
  -- Step 2: the integrand is a product of one-variable functions.
  have hpt : ∀ x, cuspBox.indicator F x = ENNReal.ofReal (∏ i, f i (x i)) := by
    intro x
    by_cases hx : x ∈ cuspBox
    · have hxi : ∀ i, x i ∈ S i := Set.mem_univ_pi.1 hx
      rw [Set.indicator_of_mem hx, Fin.prod_univ_three]
      simp only [hf, Set.indicator_of_mem (hxi 0), Set.indicator_of_mem (hxi 1),
        Set.indicator_of_mem (hxi 2), hh]
      simp [hF]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ S i := by
        by_contra hcon
        push_neg at hcon
        exact hx (Set.mem_univ_pi.2 hcon)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hf, Set.indicator_of_notMem hi])]
      simp
  -- Step 3: each factor is integrable and nonnegative.
  have hfi : ∀ i, Integrable (f i) := by
    intro i; fin_cases i
    · exact (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc
    · exact (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc
    · show Integrable ((Ici (1 : ℝ)).indicator fun t => (t ^ 3)⁻¹)
      refine (integrable_indicator_iff measurableSet_Ici).2 ?_
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      refine (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) one_pos).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) ≤ t := (lt_trans zero_lt_one ht).le
      simp [Real.rpow_neg ht0]
  have hint : Integrable (fun x : Fin 3 → ℝ => ∏ i, f i (x i)) := Integrable.fintype_prod hfi
  have hnn : 0 ≤ᵐ[(volume : Measure (Fin 3 → ℝ))] fun x => ∏ i, f i (x i) := by
    refine Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun t ht => ?_) _
    fin_cases i
    · exact zero_le_one
    · exact zero_le_one
    · have ht1 : (1 : ℝ) ≤ t := ht
      show (0 : ℝ) ≤ (t ^ 3)⁻¹
      positivity
  -- Step 4: Fubini, then three one-dimensional integrals.
  have I0 : ∫ t, f 0 t = 1 := by
    show ∫ t, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t = 1
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le zero_le_one]
    simp
  have I1 : ∫ t, f 1 t = 1 := by
    show ∫ t, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t = 1
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le zero_le_one]
    simp
  have I2 : ∫ t, f 2 t = 1 / 2 := by
    show ∫ t, (Ici (1 : ℝ)).indicator (fun t => (t ^ 3)⁻¹) t = 1 / 2
    have hcongr : ∫ t in Ioi (1 : ℝ), (t ^ 3)⁻¹ = ∫ t in Ioi (1 : ℝ), t ^ (-3 : ℝ) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        have ht0 : (0 : ℝ) ≤ t := (lt_trans zero_lt_one ht).le
        simp [Real.rpow_neg ht0]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, hcongr,
      integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  rw [step1, ← lintegral_indicator hBm]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_fintype_prod_volume_eq_prod,
    Fin.prod_univ_three, I0, I1, I2, one_mul, one_mul, one_div,
    ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- Consequently the hyperbolic volume is neither the zero measure nor identically infinite. -/
theorem hvol_ne_zero : hvol ≠ 0 := by
  intro h
  have := hvol_cusp_box
  rw [h] at this
  simp at this
  exact (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) this.symm

end CuspBox

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
  haveI : SMulInvariantMeasure G H3 hvol :=
    ⟨fun g _ hs => (hG.measure_preserving g).measure_preimage hs.nullMeasurableSet⟩
  haveI : MeasurableConstSMul G H3 := ⟨fun g => (hG.measure_preserving g).measurable⟩
  haveI : Countable G :=
    countable_of_properlyDiscontinuous basepoint hG.properly_discontinuous
  exact measure_eq_index_smul H hH hF hFH

/-! ## Commensurable groups have rationally related volumes

The positive half of Thurston's framing, stated exactly. If `Γ₁` and `Γ₂` are
subgroups of one Kleinian group and are commensurable — Mathlib's definition is
that `Γ₁ ⊓ Γ₂` has finite index in both — then Milestone 1 applied twice to the
same fundamental domain for the intersection gives
`[Γ₁ : Γ₁ ⊓ Γ₂] · vol Γ₁ = vol (Γ₁ ⊓ Γ₂) = [Γ₂ : Γ₁ ⊓ Γ₂] · vol Γ₂`, so the ratio of
the volumes is rational. Every known rational relation between volumes of
hyperbolic `3`-manifolds arises this way. The converse is false: Ruberman's
mutation preserves volume and typically destroys commensurability.

The general statement is proved for any countable group acting on any measure
space with an invariant measure, as Milestone 1 was, and then specialised. -/

section Commensurable

open Pointwise

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] [MeasurableSpace X] {μ : Measure X}

/-- A subgroup's action preserves whatever the ambient action preserves. -/
instance instSMulInvariantMeasureSubgroup (S : Subgroup Γ) [SMulInvariantMeasure Γ X μ] :
    SMulInvariantMeasure S X μ :=
  ⟨fun c _ hs => SMulInvariantMeasure.measure_preimage_smul (c : Γ) hs⟩

/-- A subgroup's action is measurable whenever the ambient action is. -/
instance instMeasurableConstSMulSubgroup (S : Subgroup Γ) [MeasurableConstSMul Γ X] :
    MeasurableConstSMul S X :=
  ⟨fun c => measurable_const_smul (c : Γ)⟩

/-- `Γ₁ ⊓ Γ₂` viewed inside `Γ₁` is the same group as viewed inside `Γ₂`: swap the two
membership proofs. Built by hand so that everything about it is `rfl`. -/
def subgroupOfSwap (Γ₁ Γ₂ : Subgroup Γ) : ↥(Γ₂.subgroupOf Γ₁) ≃ ↥(Γ₁.subgroupOf Γ₂) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Commensurable subgroups have rationally related covolumes**, in the form free of
rationals and of finiteness hypotheses: the two relative indices weight the two
volumes equally, both being the volume of a fundamental domain for `Γ₁ ⊓ Γ₂`. -/
theorem relIndex_smul_measure_eq [Countable Γ] [SMulInvariantMeasure Γ X μ]
    [MeasurableConstSMul Γ X] {Γ₁ Γ₂ : Subgroup Γ} (h : Subgroup.Commensurable Γ₁ Γ₂)
    {F₁ F₂ : Set X} (hF₁ : IsFundamentalDomain Γ₁ F₁ μ) (hF₂ : IsFundamentalDomain Γ₂ F₂ μ) :
    Γ₂.relIndex Γ₁ • μ F₁ = Γ₁.relIndex Γ₂ • μ F₂ := by
  -- one fundamental domain for the intersection, built inside `Γ₂` ...
  have hH₂ : IsFundamentalDomain (Γ₁.subgroupOf Γ₂)
      (⋃ q : Γ₂ ⧸ Γ₁.subgroupOf Γ₂, (Quotient.out q)⁻¹ • F₂) μ :=
    isFundamentalDomain_iUnion_out hF₂ _
  -- ... is also one inside `Γ₁`, since both act through `Γ`
  have hH₁ : IsFundamentalDomain (Γ₂.subgroupOf Γ₁)
      (⋃ q : Γ₂ ⧸ Γ₁.subgroupOf Γ₂, (Quotient.out q)⁻¹ • F₂) μ := by
    have := hH₂.image_of_equiv (Equiv.refl X) (Measure.QuasiMeasurePreserving.id μ)
      (subgroupOfSwap Γ₁ Γ₂) (fun g x => rfl)
    simpa using this
  have e₂ := measure_eq_index_smul (Γ₁.subgroupOf Γ₂)
    (Nat.pos_of_ne_zero h.1) hF₂ hH₂
  have e₁ := measure_eq_index_smul (Γ₂.subgroupOf Γ₁)
    (Nat.pos_of_ne_zero h.2) hF₁ hH₁
  show (Γ₂.subgroupOf Γ₁).index • μ F₁ = (Γ₁.subgroupOf Γ₂).index • μ F₂
  rw [← e₁, ← e₂]

/-- The same, as a rational multiple. -/
theorem exists_rat_measure_eq [Countable Γ] [SMulInvariantMeasure Γ X μ]
    [MeasurableConstSMul Γ X] {Γ₁ Γ₂ : Subgroup Γ} (h : Subgroup.Commensurable Γ₁ Γ₂)
    {F₁ F₂ : Set X} (hF₁ : IsFundamentalDomain Γ₁ F₁ μ) (hF₂ : IsFundamentalDomain Γ₂ F₂ μ) :
    ∃ q : ℚ, 0 < q ∧ μ F₁ = ENNReal.ofReal q * μ F₂ := by
  have key := relIndex_smul_measure_eq h hF₁ hF₂
  have h₁ : 0 < Γ₂.relIndex Γ₁ := Nat.pos_of_ne_zero h.2
  have h₂ : 0 < Γ₁.relIndex Γ₂ := Nat.pos_of_ne_zero h.1
  set n₁ := Γ₂.relIndex Γ₁
  set n₂ := Γ₁.relIndex Γ₂
  refine ⟨(n₂ : ℚ) / n₁, div_pos (by exact_mod_cast h₂) (by exact_mod_cast h₁), ?_⟩
  rw [nsmul_eq_mul, nsmul_eq_mul] at key
  have hn₁ : (n₁ : ENNReal) ≠ 0 := by exact_mod_cast h₁.ne'
  have hn₁' : (n₁ : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n₁
  calc μ F₁ = (n₁ : ENNReal)⁻¹ * (n₁ * μ F₁) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hn₁ hn₁', one_mul]
    _ = (n₁ : ENNReal)⁻¹ * (n₂ * μ F₂) := by rw [key]
    _ = ENNReal.ofReal (((n₂ : ℚ) / n₁ : ℚ) : ℝ) * μ F₂ := by
        rw [← mul_assoc]
        congr 1
        rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
          ENNReal.ofReal_div_of_pos (by exact_mod_cast h₁), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]

end Commensurable

/-- A subgroup of a Kleinian group is Kleinian: all four conditions restrict. -/
theorem IsKleinian.subgroup {G : Type} [Group G] [MulAction G H3] (hG : IsKleinian G)
    (Γ : Subgroup G) : IsKleinian Γ where
  isometry g p q := hG.isometry (g : G) p q
  measure_preserving g := hG.measure_preserving (g : G)
  free g hg p := hG.free (g : G) (fun h => hg (Subtype.ext h)) p
  properly_discontinuous K hK := by
    show (Subtype.val ⁻¹' {g : G | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}).Finite
    exact (hG.properly_discontinuous K hK).preimage Subtype.coe_injective.injOn

/-- The volume of a subgroup's quotient is a hyperbolic volume. -/
theorem mem_hyperbolicVolumes_of_subgroup {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) (Γ : Subgroup G) {F : Set H3} (hF : IsFundamentalDomain Γ F hvol)
    {v : ℝ} (hv : hvol F = ENNReal.ofReal v) (hpos : 0 < v) : v ∈ hyperbolicVolumes :=
  ⟨Γ, inferInstance, inferInstance, hG.subgroup Γ, F, hF, hv, hpos⟩

/-- **Commensurable Kleinian groups have rationally related volumes.** For subgroups
`Γ₁, Γ₂` of one Kleinian group with a common finite-index subgroup, the volumes of
their quotients have rational ratio. This is the source of every known rational
relation in `hyperbolicVolumes`; Thurston's question is whether it is the only one. -/
theorem hvol_ratio_rational_of_commensurable {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) {Γ₁ Γ₂ : Subgroup G} (h : Subgroup.Commensurable Γ₁ Γ₂)
    {F₁ F₂ : Set H3} (hF₁ : IsFundamentalDomain Γ₁ F₁ hvol)
    (hF₂ : IsFundamentalDomain Γ₂ F₂ hvol) {v₁ v₂ : ℝ}
    (hv₁ : hvol F₁ = ENNReal.ofReal v₁) (hv₂ : hvol F₂ = ENNReal.ofReal v₂)
    (h₁ : 0 < v₁) (h₂ : 0 < v₂) : ∃ q : ℚ, v₁ = q * v₂ := by
  haveI : SMulInvariantMeasure G H3 hvol :=
    ⟨fun g _ hs => (hG.measure_preserving g).measure_preimage hs.nullMeasurableSet⟩
  haveI : MeasurableConstSMul G H3 := ⟨fun g => (hG.measure_preserving g).measurable⟩
  haveI : Countable G :=
    countable_of_properlyDiscontinuous basepoint hG.properly_discontinuous
  obtain ⟨q, hq, hqv⟩ := exists_rat_measure_eq h hF₁ hF₂
  refine ⟨q, ?_⟩
  rw [hv₁, hv₂, ← ENNReal.ofReal_mul (by positivity)] at hqv
  exact (ENNReal.ofReal_eq_ofReal_iff h₁.le (by positivity)).1 hqv

/-! ## Toward Milestone 2: the Möbius action of `SL(2, ℂ)`

Milestone 2 needs a lattice, and every lattice comes from `PSL(2, ℂ)`. This section
gives `ℍ³` its action by `SL(2, ℂ)`: the point `(x, y, t)` is the quaternion
`x + y i + t j`, and `g = !![a, b; c, d]` acts by `q ↦ (a q + b)(c q + d)⁻¹`. Nothing
here is hyperbolic geometry yet — isometry and volume preservation are the next
sub-problems — but the action is what everything after it is stated about. -/

section Mobius

open MatrixGroups Quaternion

/-- Mathlib's `Star ℍ[R]` instance is stated with the `Zero`, `One`, `Neg` arguments of
`Quaternion R` derived from `[CommRing R]`, while `ℍ` elaborates them directly; instance
search cannot unify the two while the ring instance is still a metavariable, so `star`
fails to elaborate on `ℍ` in a fresh file. This is Mathlib's instance, restated. -/
instance instStarH : Star ℍ := Quaternion.instStar

/-! The point `(x, y, t)` of the upper half-space is the quaternion `x + y i + t j`, and
`g = !![a, b; c, d]` acts by `q ↦ (a q + b)(c q + d)⁻¹`, with the complex entries
embedded in the quaternions. The image has `k`-part `t · Im(det g)` and `j`-part
`t · Re(det g)` before normalising, so `det g = 1` is exactly what keeps the action
inside the half-space. The composition law is division-ring algebra: the complex
entries sit to the left of `q` and commute among themselves. -/

/-- The point `(x, y, t)` as the quaternion `x + y i + t j`. -/
def toQ (p : H3) : ℍ := ⟨p.1 0, p.1 1, p.1 2, 0⟩

theorem toQ_imK (p : H3) : (toQ p).imK = 0 := rfl

theorem toQ_imJ_pos (p : H3) : 0 < (toQ p).imJ := p.2

theorem toQ_injective : Function.Injective toQ := by
  intro p q h
  apply Subtype.ext
  funext i
  fin_cases i
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h

/-- The Möbius transformation `q ↦ (a q + b)(c q + d)⁻¹` on the quaternions. -/
noncomputable def mobiusQ (g : SL(2, ℂ)) (q : ℍ) : ℍ :=
  (((g 0 0 : ℂ) : ℍ) * q + ((g 0 1 : ℂ) : ℍ)) * ((((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ))⁻¹)

theorem sl2_det (g : SL(2, ℂ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe (A := g)
  rwa [Matrix.det_fin_two] at this

theorem sl2_row_ne_zero (g : SL(2, ℂ)) : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
  by_contra h
  push_neg at h
  have hdet := sl2_det g
  rw [h.1, h.2] at hdet
  simp at hdet

theorem normSq_pos {a : ℍ} (ha : a ≠ 0) : 0 < normSq a :=
  lt_of_le_of_ne normSq_nonneg (Ne.symm (normSq_ne_zero.2 ha))

/-- On the half-space the denominator never vanishes: its `j` and `k` parts are
`c.re · t` and `c.im · t`. -/
theorem denom_ne_zero {c d : ℂ} (hcd : c ≠ 0 ∨ d ≠ 0) {q : ℍ} (hK : q.imK = 0)
    (hJ : 0 < q.imJ) : (c : ℍ) * q + (d : ℍ) ≠ 0 := by
  intro h
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := hcd.resolve_left (by simp)
    apply hd
    have hre := congrArg QuaternionAlgebra.re h
    have him := congrArg QuaternionAlgebra.imI h
    simp at hre him
    exact Complex.ext hre him
  · apply hc
    have hJ' : ((c : ℍ) * q + (d : ℍ)).imJ = 0 := by rw [h]; rfl
    have hK' : ((c : ℍ) * q + (d : ℍ)).imK = 0 := by rw [h]; rfl
    simp [hK, hJ.ne'] at hJ' hK'
    exact Complex.ext hJ' hK'

/-- The key computation: numerator times conjugate denominator has `j`-part `t` and
`k`-part `0`. This is where `det g = 1` enters. -/
theorem num_mul_star_denom (g : SL(2, ℂ)) {q : ℍ} (hK : q.imK = 0) :
    ((((g 0 0 : ℂ) : ℍ) * q + ((g 0 1 : ℂ) : ℍ)) *
        star (((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ))).imJ = q.imJ ∧
    ((((g 0 0 : ℂ) : ℍ) * q + ((g 0 1 : ℂ) : ℍ)) *
        star (((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ))).imK = 0 := by
  have hdet := sl2_det g
  have hre := congrArg Complex.re hdet
  have him := congrArg Complex.im hdet
  simp at hre him
  constructor
  · simp [hK]
    linear_combination q.imJ * hre
  · simp [hK]
    linear_combination q.imJ * him

/-- The Möbius transformation preserves the half-space, scaling `t` by `1 / |c q + d|²`. -/
theorem mobiusQ_imJ (g : SL(2, ℂ)) {q : ℍ} (hK : q.imK = 0) :
    (mobiusQ g q).imJ = q.imJ / normSq (((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ)) ∧
    (mobiusQ g q).imK = 0 := by
  obtain ⟨h1, h2⟩ := num_mul_star_denom g hK
  unfold mobiusQ
  rw [Quaternion.inv_def, Algebra.mul_smul_comm]
  constructor
  · rw [Quaternion.imJ_smul, h1, smul_eq_mul, div_eq_inv_mul]
  · rw [Quaternion.imK_smul, h2, smul_zero]

/-- The Möbius action of `SL(2, ℂ)` on the upper half-space model. -/
noncomputable instance instSMulSL2C : SMul SL(2, ℂ) H3 where
  smul g p := ⟨![(mobiusQ g (toQ p)).re, (mobiusQ g (toQ p)).imI, (mobiusQ g (toQ p)).imJ], by
    show 0 < (mobiusQ g (toQ p)).imJ
    rw [(mobiusQ_imJ g (toQ_imK p)).1]
    exact div_pos p.2 (normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2))⟩

theorem mobius_smul_def (g : SL(2, ℂ)) (p : H3) : (g • p).1 =
    ![(mobiusQ g (toQ p)).re, (mobiusQ g (toQ p)).imI, (mobiusQ g (toQ p)).imJ] := rfl

theorem toQ_smul (g : SL(2, ℂ)) (p : H3) : toQ (g • p) = mobiusQ g (toQ p) := by
  have h2 := (mobiusQ_imJ g (toQ_imK p)).2
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact h2.symm

/-- Composition of linear fractional maps, in any division ring, with the coefficients on
the left. Only the inner denominator needs to be nonzero. -/
theorem lf_comp {K : Type*} [DivisionRing K] (a₁ b₁ c₁ d₁ N M : K) (hM : M ≠ 0) :
    (a₁ * (N * M⁻¹) + b₁) * (c₁ * (N * M⁻¹) + d₁)⁻¹ =
      (a₁ * N + b₁ * M) * (c₁ * N + d₁ * M)⁻¹ := by
  have e1 : a₁ * (N * M⁻¹) + b₁ = (a₁ * N + b₁ * M) * M⁻¹ := by
    rw [add_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ hM, mul_one]
  have e2 : c₁ * (N * M⁻¹) + d₁ = (c₁ * N + d₁ * M) * M⁻¹ := by
    rw [add_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ hM, mul_one]
  rw [e1, e2, mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc M⁻¹, inv_mul_cancel₀ hM, one_mul]

theorem mobiusQ_mul (g₁ g₂ : SL(2, ℂ)) {q : ℍ}
    (hM : ((g₂ 1 0 : ℂ) : ℍ) * q + ((g₂ 1 1 : ℂ) : ℍ) ≠ 0) :
    mobiusQ g₁ (mobiusQ g₂ q) = mobiusQ (g₁ * g₂) q := by
  unfold mobiusQ
  rw [lf_comp _ _ _ _ _ _ hM]
  have hn : ((g₁ 0 0 : ℂ) : ℍ) * (((g₂ 0 0 : ℂ) : ℍ) * q + ((g₂ 0 1 : ℂ) : ℍ)) +
      ((g₁ 0 1 : ℂ) : ℍ) * (((g₂ 1 0 : ℂ) : ℍ) * q + ((g₂ 1 1 : ℂ) : ℍ)) =
      (((g₁ * g₂) 0 0 : ℂ) : ℍ) * q + (((g₁ * g₂) 0 1 : ℂ) : ℍ) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      coeComplex_add, coeComplex_mul]
    noncomm_ring
  have hd : ((g₁ 1 0 : ℂ) : ℍ) * (((g₂ 0 0 : ℂ) : ℍ) * q + ((g₂ 0 1 : ℂ) : ℍ)) +
      ((g₁ 1 1 : ℂ) : ℍ) * (((g₂ 1 0 : ℂ) : ℍ) * q + ((g₂ 1 1 : ℂ) : ℍ)) =
      (((g₁ * g₂) 1 0 : ℂ) : ℍ) * q + (((g₁ * g₂) 1 1 : ℂ) : ℍ) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      coeComplex_add, coeComplex_mul]
    noncomm_ring
  rw [hn, hd]

noncomputable instance instMulActionSL2C : MulAction SL(2, ℂ) H3 where
  one_smul p := toQ_injective (by
    rw [toQ_smul]
    unfold mobiusQ
    simp [Matrix.SpecialLinearGroup.coe_one])
  mul_smul g₁ g₂ p := toQ_injective (by
    rw [toQ_smul, toQ_smul, toQ_smul]
    exact (mobiusQ_mul g₁ g₂ (denom_ne_zero (sl2_row_ne_zero g₂) (toQ_imK p) p.2)).symm)

end Mobius

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
