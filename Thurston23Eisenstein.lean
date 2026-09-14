import Thurston23
import EisensteinLogSin

/-!
# A hyperbolic volume that is a rational multiple of `√3 L(2, χ₋₃)`

The Eisenstein counterpart of the Catalan ladder (H1–H5 in `PROBLEMS.md`): the Bianchi group
`SL(2, ℤ[ω])`, `ω = e^{2πi/3}`, acts on `ℍ³` properly discontinuously; its congruence subgroup of
level `3 + ω` (a prime of norm `7`) is torsion free, hence Kleinian; a fundamental domain for the
Bianchi group acting effectively is the region above the unit sphere over the rhombus
`0 ≤ x ≤ ½`, `0 ≤ x + √3 y ≤ 1`; and its volume is `√3 L(2, χ₋₃)/8`.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

/-! ## The Eisenstein integers -/

section EisensteinRing

/-- `ω = e^{2πi/3} = -½ + (√3/2) i`. -/
noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

/-- The Eisenstein integer `a + b ω`. -/
@[ext] structure EisInt where
  a : ℤ
  b : ℤ
deriving DecidableEq

namespace EisInt

instance : Zero EisInt := ⟨⟨0, 0⟩⟩
instance : One EisInt := ⟨⟨1, 0⟩⟩
instance : Add EisInt := ⟨fun z w => ⟨z.a + w.a, z.b + w.b⟩⟩
instance : Neg EisInt := ⟨fun z => ⟨-z.a, -z.b⟩⟩
instance : Sub EisInt := ⟨fun z w => ⟨z.a - w.a, z.b - w.b⟩⟩
/-- `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd) ω`, since `ω² = -1 - ω`. -/
instance : Mul EisInt := ⟨fun z w => ⟨z.a * w.a - z.b * w.b, z.a * w.b + z.b * w.a - z.b * w.b⟩⟩
instance : SMul ℕ EisInt := ⟨fun n z => ⟨n * z.a, n * z.b⟩⟩
instance : SMul ℤ EisInt := ⟨fun n z => ⟨n * z.a, n * z.b⟩⟩
instance : NatCast EisInt := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast EisInt := ⟨fun n => ⟨n, 0⟩⟩
instance : Pow EisInt ℕ := ⟨fun z n => npowRec n z⟩

/-- The embedding `a + bω ↦ a + b ω` in `ℂ`. -/
noncomputable def toC (z : EisInt) : ℂ := (z.a : ℂ) + (z.b : ℂ) * omega

theorem toC_re (z : EisInt) : (toC z).re = z.a - z.b / 2 := by
  simp only [toC, omega, Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  ring

theorem toC_im (z : EisInt) : (toC z).im = z.b * (Real.sqrt 3 / 2) := by
  simp only [toC, omega, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
  ring

theorem toC_ext {z w : ℂ} (h1 : z.re = w.re) (h2 : z.im = w.im) : z = w := Complex.ext h1 h2

theorem toC_injective : Function.Injective toC := by
  intro z w h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  rw [toC_im, toC_im] at him
  rw [toC_re, toC_re] at hre
  have hb : (z.b : ℝ) = w.b := by
    have hs : Real.sqrt 3 / 2 ≠ 0 := by have := sqrt3_pos; positivity
    exact mul_right_cancel₀ hs him
  have hb' : z.b = w.b := by exact_mod_cast hb
  have ha : (z.a : ℝ) = w.a := by rw [hb] at hre; linarith
  exact EisInt.ext (by exact_mod_cast ha) hb'

theorem toC_zero : toC 0 = 0 := by
  apply toC_ext
  · rw [toC_re]; show ((0:ℤ):ℝ) - ((0:ℤ):ℝ) / 2 = 0; simp
  · rw [toC_im]; show ((0:ℤ):ℝ) * _ = 0; simp

theorem toC_one : toC 1 = 1 := by
  apply toC_ext
  · rw [toC_re]; show ((1:ℤ):ℝ) - ((0:ℤ):ℝ) / 2 = 1; simp
  · rw [toC_im]; show ((0:ℤ):ℝ) * _ = 0; simp

theorem toC_add (z w : EisInt) : toC (z + w) = toC z + toC w := by
  apply toC_ext
  · rw [Complex.add_re, toC_re, toC_re, toC_re]
    show (((z.a + w.a : ℤ)) : ℝ) - ((z.b + w.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.add_im, toC_im, toC_im, toC_im]
    show ((z.b + w.b : ℤ) : ℝ) * _ = _
    push_cast; ring

theorem toC_neg (z : EisInt) : toC (-z) = -toC z := by
  apply toC_ext
  · rw [Complex.neg_re, toC_re, toC_re]
    show ((-z.a : ℤ) : ℝ) - ((-z.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.neg_im, toC_im, toC_im]
    show ((-z.b : ℤ) : ℝ) * _ = _
    push_cast; ring

theorem toC_sub (z w : EisInt) : toC (z - w) = toC z - toC w := by
  apply toC_ext
  · rw [Complex.sub_re, toC_re, toC_re, toC_re]
    show (((z.a - w.a : ℤ)) : ℝ) - ((z.b - w.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.sub_im, toC_im, toC_im, toC_im]
    show ((z.b - w.b : ℤ) : ℝ) * _ = _
    push_cast; ring

theorem toC_mul (z w : EisInt) : toC (z * w) = toC z * toC w := by
  apply toC_ext
  · rw [Complex.mul_re, toC_re, toC_re, toC_re, toC_im, toC_im]
    show ((z.a * w.a - z.b * w.b : ℤ) : ℝ) - ((z.a * w.b + z.b * w.a - z.b * w.b : ℤ) : ℝ) / 2 = _
    push_cast
    linear_combination ((z.b : ℝ) * w.b / 4) * sqrt3_sq
  · rw [Complex.mul_im, toC_im, toC_im, toC_im, toC_re, toC_re]
    show ((z.a * w.b + z.b * w.a - z.b * w.b : ℤ) : ℝ) * _ = _
    push_cast
    ring

theorem toC_nsmul (n : ℕ) (z : EisInt) : toC (n • z) = n • toC z := by
  rw [nsmul_eq_mul]
  apply toC_ext
  · rw [Complex.mul_re, toC_re, toC_re, toC_im]
    show ((n * z.a : ℤ) : ℝ) - ((n * z.b : ℤ) : ℝ) / 2 = _
    simp; ring
  · rw [Complex.mul_im, toC_im, toC_im, toC_re]
    show ((n * z.b : ℤ) : ℝ) * _ = _
    simp; ring

theorem toC_zsmul (n : ℤ) (z : EisInt) : toC (n • z) = n • toC z := by
  rw [zsmul_eq_mul]
  apply toC_ext
  · rw [Complex.mul_re, toC_re, toC_re, toC_im]
    show ((n * z.a : ℤ) : ℝ) - ((n * z.b : ℤ) : ℝ) / 2 = _
    simp; ring
  · rw [Complex.mul_im, toC_im, toC_im, toC_re]
    show ((n * z.b : ℤ) : ℝ) * _ = _
    simp; ring

theorem toC_pow (z : EisInt) (n : ℕ) : toC (z ^ n) = toC z ^ n := by
  induction n with
  | zero => exact toC_one
  | succ n ih =>
    show toC (z ^ n * z) = _
    rw [toC_mul, ih, pow_succ]

theorem toC_natCast (n : ℕ) : toC n = n := by
  apply toC_ext
  · rw [toC_re]; show ((n : ℤ) : ℝ) - ((0 : ℤ) : ℝ) / 2 = _; simp
  · rw [toC_im]; show ((0 : ℤ) : ℝ) * _ = _; simp

theorem toC_intCast (n : ℤ) : toC n = n := by
  apply toC_ext
  · rw [toC_re]; show ((n : ℤ) : ℝ) - ((0 : ℤ) : ℝ) / 2 = _; simp
  · rw [toC_im]; show ((0 : ℤ) : ℝ) * _ = _; simp

noncomputable instance : CommRing EisInt :=
  toC_injective.commRing toC toC_zero toC_one toC_add toC_mul toC_neg toC_sub toC_nsmul
    toC_zsmul toC_pow toC_natCast toC_intCast

/-- The embedding as a ring homomorphism. -/
noncomputable def toComplex : EisInt →+* ℂ where
  toFun := toC
  map_one' := toC_one
  map_mul' := toC_mul
  map_zero' := toC_zero
  map_add' := toC_add

@[simp] theorem toComplex_apply (z : EisInt) : toComplex z = toC z := rfl

/-- `|a + bω|² = a² - ab + b²`. -/
theorem normSq_toC (z : EisInt) :
    Complex.normSq (toC z) = ((z.a ^ 2 - z.a * z.b + z.b ^ 2 : ℤ) : ℝ) := by
  rw [Complex.normSq_apply, toC_re, toC_im]
  push_cast
  linear_combination ((z.b : ℝ) ^ 2 / 4) * sqrt3_sq

/-- The conjugate `a + bω² = (a - b) - bω`. -/
def conjE (z : EisInt) : EisInt := ⟨z.a - z.b, -z.b⟩

theorem toC_conjE (z : EisInt) : toC (conjE z) = (starRingEnd ℂ) (toC z) := by
  apply toC_ext
  · rw [Complex.conj_re, toC_re, toC_re]
    show ((z.a - z.b : ℤ) : ℝ) - ((-z.b : ℤ) : ℝ) / 2 = _
    push_cast; ring
  · rw [Complex.conj_im, toC_im, toC_im]
    show ((-z.b : ℤ) : ℝ) * _ = _
    push_cast; ring

end EisInt

end EisensteinRing

/-! ## The Bianchi group `SL(2, ℤ[ω])` acts properly discontinuously -/

section EisGroup

open MatrixGroups Quaternion

/-- The Bianchi group `SL(2, ℤ[ω])` inside `SL(2, ℂ)`. -/
noncomputable def eisGroup : Subgroup SL(2, ℂ) :=
  (Matrix.SpecialLinearGroup.map EisInt.toComplex).range

theorem entry_mem_of_mem_eisGroup {g : SL(2, ℂ)} (hg : g ∈ eisGroup) (i j : Fin 2) :
    ∃ z : EisInt, EisInt.toC z = g i j := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, by simp⟩

theorem mem_eisGroup_iff {g : SL(2, ℂ)} :
    g ∈ eisGroup ↔ ∀ i j, ∃ z : EisInt, EisInt.toC z = g i j := by
  refine ⟨entry_mem_of_mem_eisGroup, fun hg => ?_⟩
  choose h hh using hg
  have hdet : (Matrix.of h).det = 1 := by
    apply EisInt.toC_injective
    change EisInt.toComplex _ = EisInt.toComplex 1
    rw [RingHom.map_det, map_one]
    convert g.2 using 2
    ext i j
    simp [hh]
  exact ⟨⟨Matrix.of h, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp [hh]⟩

/-- Only finitely many Eisenstein integers lie in a disc: `2(a² - ab + b²) ≥ a², b²`. -/
theorem finite_eisInt_normSq_le (M : ℝ) :
    {w : ℂ | (∃ z : EisInt, EisInt.toC z = w) ∧ Complex.normSq w ≤ M}.Finite := by
  have key : ∀ k : ℤ, (k : ℝ) ^ 2 ≤ 2 * M → k ∈ Set.Icc (-⌈1 + 2 * M⌉) ⌈1 + 2 * M⌉ := by
    intro k hk
    have hc := Int.le_ceil (1 + 2 * M)
    have h1 : (k : ℝ) ≤ ⌈1 + 2 * M⌉ := by nlinarith [sq_nonneg ((k : ℝ) - 1), sq_nonneg (k : ℝ)]
    have h2 : (-⌈1 + 2 * M⌉ : ℝ) ≤ k := by nlinarith [sq_nonneg ((k : ℝ) + 1), sq_nonneg (k : ℝ)]
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
  refine (((Set.finite_Icc (-⌈1 + 2 * M⌉) ⌈1 + 2 * M⌉).prod
    (Set.finite_Icc (-⌈1 + 2 * M⌉) ⌈1 + 2 * M⌉)).image
    fun x : ℤ × ℤ => EisInt.toC ⟨x.1, x.2⟩).subset ?_
  rintro w ⟨⟨z, rfl⟩, hw⟩
  rw [EisInt.normSq_toC] at hw
  push_cast at hw
  exact ⟨(z.a, z.b), ⟨key _ (by nlinarith [sq_nonneg ((z.a : ℝ) - z.b), sq_nonneg (z.b : ℝ)]),
    key _ (by nlinarith [sq_nonneg ((z.a : ℝ) - z.b), sq_nonneg (z.a : ℝ)])⟩, rfl⟩

theorem finite_eisGroup_entries_le (M : ℝ) :
    {g : SL(2, ℂ) | g ∈ eisGroup ∧ ∀ i j, Complex.normSq (g i j) ≤ M}.Finite := by
  have hS := Set.Finite.pi (ι := Fin 2) fun _ => Set.Finite.pi (ι := Fin 2) fun _ =>
    finite_eisInt_normSq_le M
  refine (hS.preimage (f := fun (g : SL(2, ℂ)) (i j : Fin 2) => g i j)
    fun g₁ _ g₂ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j =>
      congrFun (congrFun h i) j).subset ?_
  rintro g ⟨hg, hb⟩
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  exact fun i j => ⟨entry_mem_of_mem_eisGroup hg i j, hb i j⟩

/-- A subgroup of `SL(2, ℂ)` with only finitely many elements whose entries lie in any given
disc acts properly discontinuously: the argument of M2.4, with the arithmetic isolated. -/
theorem properlyDiscontinuous_of_finite_entries {Γ : Subgroup SL(2, ℂ)}
    (hfin : ∀ M : ℝ, {g : SL(2, ℂ) | g ∈ Γ ∧ ∀ i j, Complex.normSq (g i j) ≤ M}.Finite)
    (K : Set H3) (hK : IsCompact K) :
    {g : Γ | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite := by
  obtain ⟨t₀, T, R, ht₀, hbox⟩ := exists_box_of_isCompact hK
  refine ((hfin (entryBound t₀ T R)).preimage Subtype.val_injective.injOn).subset ?_
  rintro g ⟨_, ⟨p, hp, rfl⟩, hgp⟩
  exact ⟨g.2, entries_bound (g : SL(2, ℂ)) ht₀ (hbox p hp) (hbox _ hgp)⟩

/-- Every subgroup of the Bianchi group acts properly discontinuously on `ℍ³`. -/
theorem properlyDiscontinuous_of_le_eisGroup {Γ : Subgroup SL(2, ℂ)} (hΓ : Γ ≤ eisGroup)
    (K : Set H3) (hK : IsCompact K) :
    {g : Γ | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite :=
  properlyDiscontinuous_of_finite_entries
    (fun M => (finite_eisGroup_entries_le M).subset fun _ hg => ⟨hΓ hg.1, hg.2⟩) K hK

end EisGroup

/-! ## A torsion-free subgroup of finite index: level `3 + ω`, of norm `7`

For `g ≡ 1 (mod 3 + ω)` the trace is `≡ 2`; at a fixed point it is a real integer in `[-2, 2]`,
and `3 + ω` divides an integer only if `7` does, so the trace is `2` and `g = 1`. -/

section EisCongruence

open MatrixGroups

/-- The prime ideal `(3 + ω)` of `ℤ[ω]`, of norm `7`. -/
noncomputable def idealP : Ideal EisInt := Ideal.span {⟨3, 1⟩}

/-- `a + bω ∈ (3 + ω)` iff `7 ∣ 2a + b`: `(3 + ω)(c + dω) = (3c - d) + (c + 2d)ω`. -/
theorem mem_idealP_iff (z : EisInt) : z ∈ idealP ↔ (7 : ℤ) ∣ 2 * z.a + z.b := by
  rw [idealP, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    change (7 : ℤ) ∣ 2 * (3 * c.a - 1 * c.b) + (3 * c.b + 1 * c.a - 1 * c.b)
    exact ⟨c.a, by ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, 3 * k - z.a⟩, ?_⟩
    apply EisInt.ext
    · change z.a = 3 * k - 1 * (3 * k - z.a); ring
    · change z.b = 3 * (3 * k - z.a) + 1 * k - 1 * (3 * k - z.a); omega

/-- Every Eisenstein integer is congruent modulo `3 + ω` to one of `0, …, 6`: `ω ≡ -3`. -/
instance : Finite (EisInt ⧸ idealP) := by
  refine Set.finite_univ_iff.1 (((Set.finite_Icc (0 : ℤ) 6).image
    fun n : ℤ => Ideal.Quotient.mk idealP (n : EisInt)).subset ?_)
  rintro x -
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(z.a - 3 * z.b) % 7, ⟨by omega, by omega⟩, ?_⟩
  show Ideal.Quotient.mk idealP (((z.a - 3 * z.b) % 7 : ℤ) : EisInt) = Ideal.Quotient.mk idealP z
  rw [Ideal.Quotient.eq, mem_idealP_iff]
  change (7 : ℤ) ∣ 2 * ((z.a - 3 * z.b) % 7 - z.a) + (0 - z.b)
  omega

instance : Finite SL(2, EisInt ⧸ idealP) :=
  Finite.of_injective (fun (g : SL(2, EisInt ⧸ idealP)) (i j : Fin 2) => g i j)
    fun _ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j

/-- The principal congruence subgroup of level `3 + ω` of `SL(2, ℤ[ω])`. -/
noncomputable def gammaSevenZ : Subgroup SL(2, EisInt) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealP)).ker

/-- The same subgroup inside `SL(2, ℂ)`. -/
noncomputable def gammaSeven : Subgroup SL(2, ℂ) :=
  gammaSevenZ.map (Matrix.SpecialLinearGroup.map EisInt.toComplex)

theorem gammaSeven_le_eisGroup : gammaSeven ≤ eisGroup := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem eisMap_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map EisInt.toComplex :
      SL(2, EisInt) →* SL(2, ℂ)) := fun g₁ g₂ h =>
  Matrix.SpecialLinearGroup.ext _ _ fun i j => EisInt.toC_injective (by
    simpa using congrArg (fun g : SL(2, ℂ) => g i j) h)

/-- The congruence subgroup has finite index in the Bianchi group. -/
theorem relIndex_gammaSeven_eisGroup : gammaSeven.relIndex eisGroup ≠ 0 := by
  rw [gammaSeven, eisGroup, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ eisMap_injective, Subgroup.relIndex_top_right]
  show (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealP)).ker.index ≠ 0
  exact Subgroup.FiniteIndex.index_ne_zero

theorem sub_one_mem_of_mem_gammaSevenZ {h : SL(2, EisInt)} (hh : h ∈ gammaSevenZ)
    (i : Fin 2) : h i i - 1 ∈ idealP := by
  rw [gammaSevenZ, MonoidHom.mem_ker] at hh
  have e := congrArg (fun g : SL(2, EisInt ⧸ idealP) => g i i) hh
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at e
  rw [← map_one (Ideal.Quotient.mk idealP), Ideal.Quotient.eq] at e
  exact e

theorem trace_sub_two_mem_idealP {h : SL(2, EisInt)} (hh : h ∈ gammaSevenZ) :
    h 0 0 + h 1 1 - 2 ∈ idealP := by
  have := add_mem (sub_one_mem_of_mem_gammaSevenZ hh 0) (sub_one_mem_of_mem_gammaSevenZ hh 1)
  convert this using 1
  ring

/-- The only real Eisenstein integer in `[-2, 2]` congruent to `2` modulo `3 + ω` is `2`. -/
theorem eq_two_of_sub_two_mem_idealP {τ : EisInt} (hmem : τ - 2 ∈ idealP) (hb : τ.b = 0)
    (hlo : -2 ≤ τ.a) (hhi : τ.a ≤ 2) : τ = 2 := by
  rw [mem_idealP_iff] at hmem
  change (7 : ℤ) ∣ 2 * (τ.a - ((2 : ℕ) : ℤ)) + (τ.b - 0) at hmem
  apply EisInt.ext
  · change τ.a = ((2 : ℕ) : ℤ); omega
  · change τ.b = 0; exact hb

/-- **Freeness.** No element of the congruence subgroup other than the identity fixes a point. -/
theorem gammaSeven_free {g : SL(2, ℂ)} (hg : g ∈ gammaSeven) (hne : g ≠ 1) (p : H3) :
    g • p ≠ p := by
  intro hfix
  obtain ⟨him, hlo, hhi, hone⟩ := fixed_point_trace g p hfix
  refine hne (hone ?_)
  obtain ⟨h, hh, rfl⟩ := hg
  have htr : (Matrix.SpecialLinearGroup.map EisInt.toComplex h) 0 0 +
      (Matrix.SpecialLinearGroup.map EisInt.toComplex h) 1 1 = EisInt.toC (h 0 0 + h 1 1) := by
    rw [EisInt.toC_add]
    simp
  rw [htr] at him hlo hhi ⊢
  rw [EisInt.toC_im] at him
  rw [EisInt.toC_re] at hlo hhi
  have hb : (h 0 0 + h 1 1).b = 0 := by
    have hs : Real.sqrt 3 / 2 ≠ 0 := by have := sqrt3_pos; positivity
    have h0 : ((h 0 0 + h 1 1).b : ℝ) = 0 := (mul_eq_zero.1 him).resolve_right hs
    exact_mod_cast h0
  rw [hb] at hlo hhi
  have hlo' : (-2 : ℝ) ≤ ((h 0 0 + h 1 1).a : ℝ) := by simpa using hlo
  have hhi' : ((h 0 0 + h 1 1).a : ℝ) ≤ 2 := by simpa using hhi
  rw [eq_two_of_sub_two_mem_idealP (trace_sub_two_mem_idealP hh) hb
    (by exact_mod_cast hlo') (by exact_mod_cast hhi')]
  exact map_ofNat EisInt.toComplex 2

/-- The congruence subgroup of level `3 + ω` is a Kleinian group. -/
theorem isKleinian_gammaSeven : IsKleinian gammaSeven where
  isometry g p q := hdist_smul (g : SL(2, ℂ)) p q
  measure_preserving g := measurePreserving_smul (g : SL(2, ℂ))
  free g hg p := gammaSeven_free g.2 (fun h => hg (Subtype.ext h)) p
  properly_discontinuous := properlyDiscontinuous_of_le_eisGroup gammaSeven_le_eisGroup

end EisCongruence

/-! ## The base rhombus and the Voronoi cell of `ℤ[ω]`

The base is the rhombus `0 ≤ x ≤ ½`, `0 ≤ x + √3 y ≤ 1`: a third of the hexagonal Voronoi cell
of the lattice `ℤ[ω]`, a fundamental domain for its translations and the rotations by `ω`. In the
coordinates `u = x`, `v = x + √3 y` the function `|w - f|² - |w|²` is affine, and at the four
corners of the rhombus its values are `N(f) - a`, `N(f) - b`, `N(f) - (a - b)`, `N(f)`, all
nonnegative for integers, `N(f) = a² - ab + b²` being the norm of `f = a + bω`. -/

section EisBase

open Complex

/-- The closed rhombus `0 ≤ x ≤ ½`, `0 ≤ x + √3 y ≤ 1`. -/
def eisBase (w : ℂ) : Prop :=
  0 ≤ w.re ∧ w.re ≤ 1 / 2 ∧ 0 ≤ w.re + Real.sqrt 3 * w.im ∧ w.re + Real.sqrt 3 * w.im ≤ 1

/-- The open rhombus. -/
def eisBaseOpen (w : ℂ) : Prop :=
  0 < w.re ∧ w.re < 1 / 2 ∧ 0 < w.re + Real.sqrt 3 * w.im ∧ w.re + Real.sqrt 3 * w.im < 1

theorem eisBase_of_open {w : ℂ} (h : eisBaseOpen w) : eisBase w :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

/-- `|w - f|² = |w|² + N(f) - 2(a - b) u - b v`. -/
theorem normSq_sub_toC (w : ℂ) (f : EisInt) :
    normSq (w - EisInt.toC f) = normSq w + ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ)
      - 2 * (f.a - f.b) * w.re - f.b * (w.re + Real.sqrt 3 * w.im) := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    EisInt.toC_re, EisInt.toC_im]
  push_cast
  linear_combination ((f.b : ℝ) ^ 2 / 4) * sqrt3_sq

theorem int_mul_pred_nonneg (n : ℤ) : 0 ≤ n * (n - 1) := by
  rcases le_or_gt n 0 with h | h
  · nlinarith
  · nlinarith

/-- The corner values are nonnegative. -/
theorem eis_corner (a b : ℤ) : 0 ≤ a ^ 2 - a * b + b ^ 2 - a ∧ 0 ≤ a ^ 2 - a * b + b ^ 2 - b ∧
    0 ≤ a ^ 2 - a * b + b ^ 2 - (a - b) := by
  have h1 := int_mul_pred_nonneg a
  have h2 := int_mul_pred_nonneg b
  have h3 := int_mul_pred_nonneg (-b)
  have h4 := int_mul_pred_nonneg (a - b)
  have h5 := int_mul_pred_nonneg (b - a)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- A nonzero Eisenstein integer has norm at least `1`: `4N = (2a - b)² + 3b²`. -/
theorem eis_norm_pos {f : EisInt} (hf : f ≠ 0) : 1 ≤ f.a ^ 2 - f.a * f.b + f.b ^ 2 := by
  by_contra h
  push_neg at h
  have hb2 : f.b ^ 2 = 0 := by nlinarith [sq_nonneg (2 * f.a - f.b), sq_nonneg f.b]
  have hb : f.b = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hb2
  have ha2 : f.a ^ 2 = 0 := by rw [hb] at h; nlinarith [sq_nonneg f.a]
  have ha : f.a = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ha2
  exact hf (EisInt.ext ha hb)

/-- The difference `|w - f|² - |w|²` as a convex combination of the corner values. -/
theorem normSq_sub_toC_sub (w : ℂ) (f : EisInt) :
    normSq (w - EisInt.toC f) - normSq w =
      (1 - 2 * w.re) * (1 - (w.re + Real.sqrt 3 * w.im)) * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ)
      + 2 * w.re * (1 - (w.re + Real.sqrt 3 * w.im))
          * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - (f.a - f.b) : ℤ) : ℝ)
      + (1 - 2 * w.re) * (w.re + Real.sqrt 3 * w.im)
          * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.b : ℤ) : ℝ)
      + 2 * w.re * (w.re + Real.sqrt 3 * w.im) * ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.a : ℤ) : ℝ) := by
  rw [normSq_sub_toC]
  push_cast
  ring

/-- **The rhombus lies in the Voronoi cell of `0`**: `|w| ≤ |w - f|` for every `f ∈ ℤ[ω]`. -/
theorem cell_of_eisBase {w : ℂ} (hw : eisBase w) (f : EisInt) :
    normSq w ≤ normSq (w - EisInt.toC f) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  obtain ⟨c1, c2, c3⟩ := eis_corner f.a f.b
  have c0 : (0 : ℤ) ≤ f.a ^ 2 - f.a * f.b + f.b ^ 2 := by nlinarith [c1, int_mul_pred_nonneg f.a]
  have e := normSq_sub_toC_sub w f
  have k0 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast c0
  have k1 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.a : ℤ) : ℝ) := by exact_mod_cast c1
  have k2 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.b : ℤ) : ℝ) := by exact_mod_cast c2
  have k3 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - (f.a - f.b) : ℤ) : ℝ) := by
    exact_mod_cast c3
  have t0 : 0 ≤ 1 - 2 * w.re := by linarith
  have t1 : 0 ≤ 1 - (w.re + Real.sqrt 3 * w.im) := by linarith
  have := mul_nonneg (mul_nonneg t0 t1) k0
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) t1) k3
  have := mul_nonneg (mul_nonneg t0 h3) k2
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) h3) k1
  linarith

/-- **The open rhombus lies in the open Voronoi cell**: `|w| < |w - f|` for `f ≠ 0`. -/
theorem cell_strict_of_eisBaseOpen {w : ℂ} (hw : eisBaseOpen w) {f : EisInt} (hf : f ≠ 0) :
    normSq w < normSq (w - EisInt.toC f) := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  obtain ⟨c1, c2, c3⟩ := eis_corner f.a f.b
  have c0 := eis_norm_pos hf
  have e := normSq_sub_toC_sub w f
  have k0 : (1 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast c0
  have k1 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.a : ℤ) : ℝ) := by exact_mod_cast c1
  have k2 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - f.b : ℤ) : ℝ) := by exact_mod_cast c2
  have k3 : (0 : ℝ) ≤ ((f.a ^ 2 - f.a * f.b + f.b ^ 2 - (f.a - f.b) : ℤ) : ℝ) := by
    exact_mod_cast c3
  have t0 : 0 < 1 - 2 * w.re := by linarith
  have t1 : 0 < 1 - (w.re + Real.sqrt 3 * w.im) := by linarith
  have := mul_le_mul_of_nonneg_left k0 (mul_pos t0 t1).le
  have := mul_pos t0 t1
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) t1.le) k3
  have := mul_nonneg (mul_nonneg t0.le h3.le) k2
  have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * w.re) h3.le) k1
  nlinarith

/-- A point of the closed cell translated into the open rhombus was not translated. -/
theorem eq_zero_of_cell_of_eisBaseOpen {w : ℂ}
    (hw : ∀ f : EisInt, normSq w ≤ normSq (w - EisInt.toC f)) {e : EisInt}
    (he : eisBaseOpen (w + EisInt.toC e)) : e = 0 := by
  by_contra hne
  have h1 := cell_strict_of_eisBaseOpen he hne
  rw [add_sub_cancel_right] at h1
  have h2 := hw (-e)
  have hneg : EisInt.toC (-e) = -EisInt.toC e := map_neg EisInt.toComplex e
  rw [hneg, sub_neg_eq_add] at h2
  linarith

/-- The Voronoi cell is invariant under multiplication by a unit. -/
theorem cell_mul_unit {w : ℂ} (hw : ∀ f : EisInt, normSq w ≤ normSq (w - EisInt.toC f))
    {U : EisInt} (hU : normSq (EisInt.toC U) = 1) (f : EisInt) :
    normSq (EisInt.toC U * w) ≤ normSq (EisInt.toC U * w - EisInt.toC f) := by
  have hu1 : EisInt.toC U * (starRingEnd ℂ) (EisInt.toC U) = 1 := by
    rw [Complex.mul_conj, hU, Complex.ofReal_one]
  have hm : EisInt.toC (EisInt.conjE U * f) = EisInt.toC (EisInt.conjE U) * EisInt.toC f :=
    map_mul EisInt.toComplex _ _
  have hfac : EisInt.toC U * w - EisInt.toC f
      = EisInt.toC U * (w - EisInt.toC (EisInt.conjE U * f)) := by
    rw [hm, EisInt.toC_conjE]
    linear_combination (EisInt.toC f) * hu1
  rw [hfac, Complex.normSq_mul, Complex.normSq_mul, hU, one_mul, one_mul]
  exact hw _

/-- On the rhombus `|w|² ≤ ⅓`. -/
theorem normSq_le_of_eisBase {w : ℂ} (hw : eisBase w) : normSq w ≤ 1 / 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  have hsq : (Real.sqrt 3 * w.im) ^ 2 = 3 * w.im ^ 2 := by rw [mul_pow, sqrt3_sq]
  rw [Complex.normSq_apply]
  nlinarith [mul_nonneg h1 (by linarith : (0:ℝ) ≤ 1 / 2 - w.re),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (w.re + Real.sqrt 3 * w.im))
      (by linarith : (0:ℝ) ≤ 1 + (w.re + Real.sqrt 3 * w.im) - 2 * w.re)]

/-- The coordinates of `(c + dω) w`. -/
theorem toC_mul_re (U : EisInt) (w : ℂ) :
    (EisInt.toC U * w).re = (U.a - U.b / 2) * w.re - U.b * (Real.sqrt 3 / 2) * w.im := by
  rw [Complex.mul_re, EisInt.toC_re, EisInt.toC_im]

theorem toC_mul_im (U : EisInt) (w : ℂ) :
    (EisInt.toC U * w).im = (U.a - U.b / 2) * w.im + U.b * (Real.sqrt 3 / 2) * w.re := by
  rw [Complex.mul_im, EisInt.toC_re, EisInt.toC_im]

/-- The rotations by `ω` and `ω²` move the open rhombus off itself. -/
theorem not_eisBaseOpen_rot {w : ℂ} (hw : eisBaseOpen w) {U : EisInt}
    (hU : (U.a = -1 ∧ U.b = -1) ∨ (U.a = 0 ∧ U.b = 1)) :
    ¬ eisBaseOpen (EisInt.toC U * w) := by
  rintro ⟨g1, -, g3, -⟩
  obtain ⟨h1, -, h3, -⟩ := hw
  rw [toC_mul_re] at g1 g3
  rw [toC_mul_im] at g3
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, sqrt3_sq]
  rcases hU with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb] at g1 g3
    push_cast at g1 g3
    nlinarith [hs3]
  · rw [ha, hb] at g1 g3
    push_cast at g1 g3
    nlinarith [hs3]

/-- The units of `ℤ[ω]`: `N(U) = 1` leaves six possibilities. -/
theorem eis_unit_cases {U : EisInt} (hU : U.a ^ 2 - U.a * U.b + U.b ^ 2 = 1) :
    (U.a = 1 ∧ U.b = 0) ∨ (U.a = -1 ∧ U.b = 0) ∨ (U.a = 0 ∧ U.b = 1) ∨ (U.a = 0 ∧ U.b = -1) ∨
      (U.a = 1 ∧ U.b = 1) ∨ (U.a = -1 ∧ U.b = -1) := by
  have hb : U.b ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * U.a - U.b)]
  have hb1 : -1 ≤ U.b ∧ U.b ≤ 1 := by constructor <;> nlinarith
  have ha1 : -1 ≤ U.a ∧ U.a ≤ 1 := by
    have : (2 * U.a - U.b) ^ 2 ≤ 4 := by nlinarith [sq_nonneg U.b]
    constructor <;> nlinarith
  obtain ⟨ha0, ha2⟩ := ha1
  obtain ⟨hb0, hb2⟩ := hb1
  have hA : U.a = -1 ∨ U.a = 0 ∨ U.a = 1 := by omega
  have hB : U.b = -1 ∨ U.b = 0 ∨ U.b = 1 := by omega
  rcases hA with ha | ha | ha <;> rcases hB with hb' | hb' | hb' <;> rw [ha, hb'] at hU <;>
    norm_num at hU <;> simp [ha, hb']

end EisBase

/-! ## Reduction theory for the Bianchi group

Every orbit has a point of maximal height; translating it by the nearest point of `ℤ[ω]` puts
it in the Voronoi cell of `0`, where `|q| ≥ 1` since `S` would otherwise raise the height; a
rotation by a power of `ω` then puts it over the rhombus. -/

section EisReduction

open Set MatrixGroups Quaternion Pointwise

theorem EisInt.toC_neg_one : EisInt.toC (-1) = -1 := by
  show EisInt.toComplex (-1) = -1
  rw [map_neg, map_one]

theorem T_mem_eisGroup (z : EisInt) : T (EisInt.toC z) ∈ eisGroup :=
  mem_eisGroup_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨1, by simp [T, EisInt.toC_one]⟩, ⟨z, by simp [T]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨0, by simp [T, EisInt.toC_zero]⟩, ⟨1, by simp [T, EisInt.toC_one]⟩⟩⟩)

theorem S_mem_eisGroup : S ∈ eisGroup :=
  mem_eisGroup_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨0, by simp [S, EisInt.toC_zero]⟩, ⟨-1, by simp [S, EisInt.toC_neg_one]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨1, by simp [S, EisInt.toC_one]⟩, ⟨0, by simp [S, EisInt.toC_zero]⟩⟩⟩)

/-- For a unit, the inverse is the conjugate. -/
theorem EisInt.toC_inv_of_normSq {U : EisInt} (hU : Complex.normSq (EisInt.toC U) = 1) :
    (EisInt.toC U)⁻¹ = EisInt.toC (EisInt.conjE U) := by
  rw [Complex.inv_def, hU, inv_one, Complex.ofReal_one, mul_one, EisInt.toC_conjE]

theorem D_mem_eisGroup {U : EisInt} (hU : Complex.normSq (EisInt.toC U) = 1)
    (h : EisInt.toC U ≠ 0) : D (EisInt.toC U) h ∈ eisGroup :=
  mem_eisGroup_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨U, by simp [D]⟩, ⟨0, by simp [D, EisInt.toC_zero]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨0, by simp [D, EisInt.toC_zero]⟩,
        ⟨EisInt.conjE U, by simp [D, EisInt.toC_inv_of_normSq hU]⟩⟩⟩)

theorem zc_T_smul (b : ℂ) (p : H3) : zc (T b • p) = zc p + b := by
  apply Complex.ext <;> simp [zc, T_smul_val]

theorem height_T_smul (b : ℂ) (p : H3) : (T b • p).1 2 = p.1 2 := by
  simp [T_smul_val]

theorem zc_D_smul (a : ℂ) (ha : a ≠ 0) (p : H3) : zc (D a ha • p) = a ^ 2 * zc p := by
  obtain ⟨h0, h1, -⟩ := D_smul_coord a ha p
  apply Complex.ext
  · rw [zc_re, h0]
    simp only [sq, Complex.mul_re, Complex.mul_im, zc_re, zc_im]
    ring
  · rw [zc_im, h1]
    simp only [sq, Complex.mul_re, Complex.mul_im, zc_re, zc_im]
    ring

theorem N_eq_normSq_zc (p : H3) : N p.1 = Complex.normSq (zc p) + p.1 2 * p.1 2 := by
  unfold N
  rw [Complex.normSq_apply, zc_re, zc_im]

theorem N_D_smul_of_normSq (a : ℂ) (ha : a ≠ 0) (hn : Complex.normSq a = 1) (p : H3) :
    N (D a ha • p).1 = N p.1 ∧ (D a ha • p).1 2 = p.1 2 := by
  obtain ⟨-, -, h2⟩ := D_smul_coord a ha p
  have hn' : a.re ^ 2 + a.im ^ 2 = 1 := by rw [Complex.normSq_apply] at hn; linarith
  have ht : (D a ha • p).1 2 = p.1 2 := by rw [h2, hn', one_mul]
  refine ⟨?_, ht⟩
  rw [N_eq_normSq_zc, N_eq_normSq_zc, zc_D_smul, Complex.normSq_mul, map_pow Complex.normSq, hn,
    one_pow, one_mul, ht]

/-- Along an orbit of the Bianchi group only finitely many heights are at least the starting
one. -/
theorem finite_heights_eis (p : H3) :
    ((fun g : SL(2, ℂ) => (g • p).1 2) '' {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2}).Finite := by
  have ht0 : 0 < p.1 2 := p.2
  refine (((finite_eisInt_normSq_le (1 / p.1 2 ^ 2)).prod
    (finite_eisInt_normSq_le (2 * (1 + 1 / p.1 2 ^ 2 * normSq (toQ p))))).image
      fun cd : ℂ × ℂ => p.1 2 / normSq ((cd.1 : ℍ) * toQ p + (cd.2 : ℍ))).subset ?_
  rintro _ ⟨g, ⟨hg, hle⟩, rfl⟩
  have hh := smul_height g p
  have hMpos := normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hc := normSq_mul_imJ_le (g 1 0) (g 1 1) (toQ_imK p)
  rw [show (toQ p).imJ = p.1 2 from rfl] at hc
  generalize hM : ((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ) = M at hh hMpos hc
  have hM1 : normSq M ≤ 1 := by
    rw [hh, le_div_iff₀ hMpos] at hle
    nlinarith
  have hcb : Complex.normSq (g 1 0) ≤ 1 / p.1 2 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hd : ((g 1 1 : ℂ) : ℍ) = M + -(((g 1 0 : ℂ) : ℍ) * toQ p) := by rw [← hM]; abel
  have hdb := normSq_add_le M (-(((g 1 0 : ℂ) : ℍ) * toQ p))
  rw [← hd, normSq_neg, map_mul, normSq_coeComplex, normSq_coeComplex] at hdb
  have hcq : Complex.normSq (g 1 0) * normSq (toQ p) ≤ 1 / p.1 2 ^ 2 * normSq (toQ p) :=
    mul_le_mul_of_nonneg_right hcb normSq_nonneg
  refine ⟨(g 1 0, g 1 1), ⟨⟨entry_mem_of_mem_eisGroup hg 1 0, hcb⟩,
    ⟨entry_mem_of_mem_eisGroup hg 1 1, by linarith⟩⟩, ?_⟩
  show p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) = (g • p).1 2
  rw [hM, hh]

/-- Every orbit of the Bianchi group has a point of maximal height. -/
theorem exists_max_height_eis (p : H3) :
    ∃ g₀ ∈ eisGroup, ∀ g ∈ eisGroup, (g • p).1 2 ≤ (g₀ • p).1 2 := by
  have h1 : (1 : SL(2, ℂ)) ∈ {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2} :=
    ⟨eisGroup.one_mem, by simp only [one_smul, le_refl]⟩
  have hne : ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2}).Nonempty := ⟨_, 1, h1, rfl⟩
  have hbdd := (finite_heights_eis p).bddAbove
  obtain ⟨g₀, ⟨hg₀, -⟩, hmax⟩ := hne.csSup_mem (finite_heights_eis p)
  have hmax' : (g₀ • p).1 2 = sSup ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ eisGroup ∧ p.1 2 ≤ (g • p).1 2}) := hmax
  refine ⟨g₀, hg₀, fun g hg => ?_⟩
  rw [hmax']
  by_cases hle : p.1 2 ≤ (g • p).1 2
  · exact le_csSup hbdd ⟨g, ⟨hg, hle⟩, rfl⟩
  · exact (not_le.1 hle).le.trans (le_csSup hbdd ⟨1, h1, by simp only [one_smul]⟩)

/-- Every complex number has a nearest point of `ℤ[ω]`, within distance `1`. -/
theorem exists_nearest_eis (z : ℂ) : ∃ e : EisInt, Complex.normSq (z - EisInt.toC e) ≤ 1 ∧
    ∀ f : EisInt, Complex.normSq (z - EisInt.toC e) ≤ Complex.normSq (z - EisInt.toC e - EisInt.toC f) := by
  set Sfin : Set EisInt := {e | Complex.normSq (z - EisInt.toC e) ≤ 1} with hSfin
  have hfin : Sfin.Finite := by
    refine ((finite_eisInt_normSq_le (2 * (Complex.normSq z + 1))).preimage
      EisInt.toC_injective.injOn).subset ?_
    intro e he
    refine ⟨⟨e, rfl⟩, ?_⟩
    have he' : Complex.normSq (z - EisInt.toC e) ≤ 1 := he
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at he' ⊢
    nlinarith [sq_nonneg (2 * z.re - (EisInt.toC e).re), sq_nonneg (2 * z.im - (EisInt.toC e).im)]
  have hne : Sfin.Nonempty := by
    have hs := sqrt3_pos
    set t : ℝ := 2 * z.im / Real.sqrt 3 with ht
    have hzim : z.im = t * Real.sqrt 3 / 2 := by rw [ht]; field_simp
    set rt : ℝ := ((round t : ℤ) : ℝ) with hrt
    set R : ℝ := ((round (z.re + rt / 2) : ℤ) : ℝ) with hR
    refine ⟨⟨round (z.re + rt / 2), round t⟩, ?_⟩
    show Complex.normSq (z - EisInt.toC _) ≤ 1
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, EisInt.toC_re, EisInt.toC_im]
    have h1 := abs_le.1 (abs_sub_round (z.re + rt / 2))
    have h2 := abs_le.1 (abs_sub_round t)
    rw [← hR] at h1
    rw [← hrt] at h2
    simp only
    rw [← hR, ← hrt, hzim]
    have e2 : (t * Real.sqrt 3 / 2 - rt * (Real.sqrt 3 / 2)) * (t * Real.sqrt 3 / 2 - rt * (Real.sqrt 3 / 2))
        = 3 / 4 * (t - rt) ^ 2 := by
      linear_combination ((t - rt) ^ 2 / 4) * sqrt3_sq
    rw [e2]
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨e, he, hmin⟩ := Set.exists_min_image Sfin (fun e => Complex.normSq (z - EisInt.toC e)) hfin hne
  refine ⟨e, he, fun f => ?_⟩
  have hadd : EisInt.toC (e + f) = EisInt.toC e + EisInt.toC f := map_add EisInt.toComplex e f
  by_cases h : Complex.normSq (z - EisInt.toC e - EisInt.toC f) ≤ 1
  · have hmem : e + f ∈ Sfin := by
      show Complex.normSq (z - EisInt.toC (e + f)) ≤ 1
      rw [hadd, ← sub_sub]
      exact h
    have := hmin (e + f) hmem
    simp only at this
    rw [hadd, ← sub_sub] at this
    exact this
  · push_neg at h
    exact le_trans he h.le

/-- The Voronoi cell together with the sector `x ≥ 0`, `x + √3 y ≥ 0` gives the rhombus. -/
theorem eisBase_of_cell {w : ℂ} (hw : ∀ f : EisInt, Complex.normSq w ≤ Complex.normSq (w - EisInt.toC f))
    (h0 : 0 ≤ w.re) (h1 : 0 ≤ w.re + Real.sqrt 3 * w.im) : eisBase w := by
  have c1 := hw ⟨1, 0⟩
  have c2 := hw ⟨1, 1⟩
  rw [normSq_sub_toC] at c1 c2
  push_cast at c1 c2
  exact ⟨h0, by linarith, h1, by linarith⟩

/-- The closed box over the rhombus, above the unit sphere. -/
def eisBox : Set H3 := {p | eisBase (zc p) ∧ 1 ≤ N p.1}

/-- The open box. -/
def eisBoxOpen : Set H3 := {p | eisBaseOpen (zc p) ∧ 1 < N p.1}

/-- **Reduction.** The Bianchi group carries every point into the box over the rhombus. -/
theorem exists_smul_mem_eisBox (p : H3) : ∃ g ∈ eisGroup, g • p ∈ eisBox := by
  obtain ⟨g₀, hg₀, hmax⟩ := exists_max_height_eis p
  obtain ⟨e, -, hcell⟩ := exists_nearest_eis (zc (g₀ • p))
  have hg₁ : T (EisInt.toC (-e)) * g₀ ∈ eisGroup := eisGroup.mul_mem (T_mem_eisGroup _) hg₀
  set g₁ := T (EisInt.toC (-e)) * g₀ with hg₁def
  have hneg : EisInt.toC (-e) = -EisInt.toC e := map_neg EisInt.toComplex e
  have hz₁ : zc (g₁ • p) = zc (g₀ • p) - EisInt.toC e := by
    rw [hg₁def, mul_smul, zc_T_smul, hneg, ← sub_eq_add_neg]
  have ht₁ : (g₁ • p).1 2 = (g₀ • p).1 2 := by rw [hg₁def, mul_smul, height_T_smul]
  -- `|q| ≥ 1`, since otherwise `S` raises the height
  have hN₁ : 1 ≤ N (g₁ • p).1 := by
    by_contra hlt
    push_neg at hlt
    have hS10 : S 1 0 = 1 := by simp [S]
    have hS11 : S 1 1 = 0 := by simp [S]
    have hht : ((S * g₁) • p).1 2 = (g₁ • p).1 2 / N (g₁ • p).1 := by
      rw [mul_smul, smul_height S (g₁ • p), hS10, hS11, coeComplex_one, coeComplex_zero, one_mul,
        add_zero, normSq_toQ]
    have hNpos : 0 < N (g₁ • p).1 := N_pos (g₁ • p).2
    have hle := hmax _ (eisGroup.mul_mem S_mem_eisGroup hg₁)
    rw [hht, ht₁, div_le_iff₀ hNpos] at hle
    nlinarith [mul_lt_mul_of_pos_left hlt (g₀ • p).2]
  have hcell₁ : ∀ f : EisInt, Complex.normSq (zc (g₁ • p)) ≤ Complex.normSq (zc (g₁ • p) - EisInt.toC f) := by
    rw [hz₁]; exact hcell
  set w := zc (g₁ • p) with hw
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq, sqrt3_sq]
  -- rotate into the sector
  by_cases hA : 0 ≤ w.re ∧ 0 ≤ w.re + Real.sqrt 3 * w.im
  · exact ⟨g₁, hg₁, eisBase_of_cell hcell₁ hA.1 hA.2, hN₁⟩
  -- the two rotations, `z ↦ ω z` by `D(ω²)` and `z ↦ ω² z` by `D(ω)`
  have hn1 : Complex.normSq (EisInt.toC ⟨-1, -1⟩) = 1 := by
    rw [EisInt.normSq_toC]; norm_num
  have hn2 : Complex.normSq (EisInt.toC ⟨0, 1⟩) = 1 := by
    rw [EisInt.normSq_toC]; norm_num
  have hne1 : EisInt.toC ⟨-1, -1⟩ ≠ 0 := fun h => by
    rw [h, map_zero] at hn1; exact zero_ne_one hn1
  have hne2 : EisInt.toC ⟨0, 1⟩ ≠ 0 := fun h => by
    rw [h, map_zero] at hn2; exact zero_ne_one hn2
  have hsq1 : EisInt.toC ⟨-1, -1⟩ ^ 2 = EisInt.toC ⟨0, 1⟩ := by
    rw [sq, show EisInt.toC ⟨-1, -1⟩ * EisInt.toC ⟨-1, -1⟩
      = EisInt.toC ((⟨-1, -1⟩ : EisInt) * ⟨-1, -1⟩) from (map_mul EisInt.toComplex _ _).symm]
    exact congrArg EisInt.toC (EisInt.ext (by decide) (by decide))
  have hsq2 : EisInt.toC ⟨0, 1⟩ ^ 2 = EisInt.toC ⟨-1, -1⟩ := by
    rw [sq, show EisInt.toC ⟨0, 1⟩ * EisInt.toC ⟨0, 1⟩
      = EisInt.toC ((⟨0, 1⟩ : EisInt) * ⟨0, 1⟩) from (map_mul EisInt.toComplex _ _).symm]
    exact congrArg EisInt.toC (EisInt.ext (by decide) (by decide))
  by_cases hB : w.re + Real.sqrt 3 * w.im ≤ 0 ∧ 0 ≤ w.re - Real.sqrt 3 * w.im
  · refine ⟨D (EisInt.toC ⟨-1, -1⟩) hne1 * g₁,
      eisGroup.mul_mem (D_mem_eisGroup hn1 hne1) hg₁, ?_, ?_⟩
    · rw [mul_smul, zc_D_smul, hsq1, ← hw]
      refine eisBase_of_cell (cell_mul_unit hcell₁ hn2) ?_ ?_
      · rw [toC_mul_re]; push_cast; nlinarith [hB.1]
      · rw [toC_mul_re, toC_mul_im]; push_cast; nlinarith [hB.2, hs3]
    · rw [mul_smul, (N_D_smul_of_normSq _ hne1 hn1 _).1]; exact hN₁
  · refine ⟨D (EisInt.toC ⟨0, 1⟩) hne2 * g₁,
      eisGroup.mul_mem (D_mem_eisGroup hn2 hne2) hg₁, ?_, ?_⟩
    · rw [mul_smul, zc_D_smul, hsq2, ← hw]
      push_neg at hA hB
      refine eisBase_of_cell (cell_mul_unit hcell₁ hn1) ?_ ?_
      · rw [toC_mul_re]; push_cast
        by_cases hx : 0 ≤ w.re
        · have h1 := hA hx
          have h2 := hB h1.le
          nlinarith
        · push_neg at hx
          by_cases hv : w.re + Real.sqrt 3 * w.im ≤ 0
          · have := hB hv; nlinarith
          · push_neg at hv; nlinarith
      · rw [toC_mul_re, toC_mul_im]; push_cast
        by_cases hx : 0 ≤ w.re
        · have := hA hx
          by_cases hv : w.re + Real.sqrt 3 * w.im ≤ 0
          · have := hB hv; nlinarith [hs3]
          · push_neg at hv; nlinarith [hs3]
        · push_neg at hx; nlinarith [hs3]
    · rw [mul_smul, (N_D_smul_of_normSq _ hne2 hn2 _).1]; exact hN₁

end EisReduction

/-! ## Uniqueness on the open box

If `g` carries a point of the open box into the open box and the height does not drop, then
`|c q + d|² ≤ 1`. On the open box `t² > ⅔`, so `|c|² ≤ 1`; and `|c| = 1` is impossible, since
then `|c z + d| = |z + c̄ d| ≥ |z|` by the Voronoi property and `|z|² + t² > 1`. So `c = 0`, and
`g` acts by `z ↦ a² z + ba` with `a` a unit. The translation vanishes by the Voronoi property of
the rotated point, and `a² ∈ {1, ω, ω²}` must be `1` because the rotations by `ω`, `ω²` move the
open rhombus off itself. -/

section EisUniqueness

open Set MatrixGroups Quaternion Pointwise

theorem sq_height_gt_eis {p : H3} (hp : p ∈ eisBoxOpen) : 2 / 3 < p.1 2 ^ 2 := by
  obtain ⟨hb, hN⟩ := hp
  have h1 := normSq_le_of_eisBase (eisBase_of_open hb)
  rw [N_eq_normSq_zc] at hN
  nlinarith

theorem bottomLeft_eq_zero_of_le_one_eis {g : SL(2, ℂ)} (hg : g ∈ eisGroup) {p : H3}
    (hp : p ∈ eisBoxOpen)
    (hD : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ 1) : g 1 0 = 0 := by
  obtain ⟨C, hC⟩ := entry_mem_of_mem_eisGroup hg 1 0
  obtain ⟨Dd, hDd⟩ := entry_mem_of_mem_eisGroup hg 1 1
  rw [normSq_denom] at hD
  have ht2 := sq_height_gt_eis hp
  obtain ⟨hb, hN⟩ := hp
  have hnC : Complex.normSq (g 1 0) = ((C.a ^ 2 - C.a * C.b + C.b ^ 2 : ℤ) : ℝ) := by
    rw [← hC, EisInt.normSq_toC]
  have hn0 : 0 ≤ C.a ^ 2 - C.a * C.b + C.b ^ 2 := by
    nlinarith [sq_nonneg (2 * C.a - C.b), sq_nonneg C.b]
  rw [hnC] at hD
  have hz0 := Complex.normSq_nonneg (g 1 0 * zc p + g 1 1)
  have hnle : C.a ^ 2 - C.a * C.b + C.b ^ 2 ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h2 : (2 : ℝ) ≤ ((C.a ^ 2 - C.a * C.b + C.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast hlt
    nlinarith
  by_cases hC0 : C = 0
  · rw [← hC, hC0]
    exact map_zero EisInt.toComplex
  exfalso
  have hn1 : C.a ^ 2 - C.a * C.b + C.b ^ 2 = 1 := le_antisymm hnle (eis_norm_pos hC0)
  have hc1 : Complex.normSq (g 1 0) = 1 := by rw [hnC, hn1]; norm_num
  have hu1 : g 1 0 * (starRingEnd ℂ) (g 1 0) = 1 := by
    rw [Complex.mul_conj, hc1, Complex.ofReal_one]
  have hm : EisInt.toC (-(EisInt.conjE C * Dd)) = -((starRingEnd ℂ) (g 1 0) * g 1 1) := by
    rw [show EisInt.toC (-(EisInt.conjE C * Dd)) = -(EisInt.toC (EisInt.conjE C) * EisInt.toC Dd)
      from by
        rw [show EisInt.toC (-(EisInt.conjE C * Dd)) = EisInt.toComplex (-(EisInt.conjE C * Dd))
          from rfl, map_neg, map_mul]
        rfl,
      EisInt.toC_conjE, hC, hDd]
  have hfac : g 1 0 * zc p + g 1 1
      = g 1 0 * (zc p - EisInt.toC (-(EisInt.conjE C * Dd))) := by
    rw [hm]
    linear_combination (-(g 1 1)) * hu1
  have hcell := cell_of_eisBase (eisBase_of_open hb) (-(EisInt.conjE C * Dd))
  rw [hfac, Complex.normSq_mul, hc1, one_mul] at hD
  rw [N_eq_normSq_zc] at hN
  have : ((C.a ^ 2 - C.a * C.b + C.b ^ 2 : ℤ) : ℝ) = 1 := by rw [hn1]; norm_num
  rw [this, one_mul] at hD
  nlinarith

/-- **Uniqueness, the triangular case.** -/
theorem smul_eq_self_of_le_one_eis {g : SL(2, ℂ)} (hg : g ∈ eisGroup) {p : H3}
    (hp : p ∈ eisBoxOpen) (hgp : g • p ∈ eisBoxOpen)
    (hD : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ 1) :
    ∀ q : H3, g • q = q := by
  have hc : g 1 0 = 0 := bottomLeft_eq_zero_of_le_one_eis hg hp hD
  obtain ⟨A, hA⟩ := entry_mem_of_mem_eisGroup hg 0 0
  obtain ⟨B, hB⟩ := entry_mem_of_mem_eisGroup hg 0 1
  obtain ⟨Dg, hDg⟩ := entry_mem_of_mem_eisGroup hg 1 1
  have hdet := sl2_det g
  rw [hc, mul_zero, sub_zero] at hdet
  have ha0 : g 0 0 ≠ 0 := fun h => by rw [h, zero_mul] at hdet; exact zero_ne_one hdet
  have hd0 : g 1 1 ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  have hDval : Complex.normSq (g 1 1) ≤ 1 := by
    have h := hD
    rw [normSq_denom, hc] at h
    simpa using h
  have hDint : Complex.normSq (g 1 1) = ((Dg.a ^ 2 - Dg.a * Dg.b + Dg.b ^ 2 : ℤ) : ℝ) := by
    rw [← hDg, EisInt.normSq_toC]
  have hDg0 : Dg ≠ 0 := fun h => hd0 (by rw [← hDg, h]; exact map_zero EisInt.toComplex)
  have hDge := eis_norm_pos hDg0
  have hDone : Complex.normSq (g 1 1) = 1 := by
    have : (1 : ℝ) ≤ ((Dg.a ^ 2 - Dg.a * Dg.b + Dg.b ^ 2 : ℤ) : ℝ) := by exact_mod_cast hDge
    rw [hDint] at hDval ⊢
    linarith
  have hnormA : Complex.normSq (g 0 0) = 1 := by
    have hprod : Complex.normSq (g 0 0) * Complex.normSq (g 1 1) = 1 := by
      rw [← Complex.normSq_mul, hdet, Complex.normSq_one]
    rwa [hDone, mul_one] at hprod
  have hAint : A.a ^ 2 - A.a * A.b + A.b ^ 2 = 1 := by
    have h : ((A.a ^ 2 - A.a * A.b + A.b ^ 2 : ℤ) : ℝ) = 1 := by
      rw [← EisInt.normSq_toC, hA, hnormA]
    exact_mod_cast h
  -- `g = T (b a) * D a` acts by `z ↦ a² z + b a`
  have hfac : g = T (g 0 1 * g 0 0) * D (g 0 0) ha0 := sl2_eq_of_eq_zero' g hc ha0
  have hsmul : zc (g • p) = g 0 0 ^ 2 * zc p + g 0 1 * g 0 0 := by
    have : g • p = T (g 0 1 * g 0 0) • (D (g 0 0) ha0 • p) := by
      conv_lhs => rw [hfac]
      rw [mul_smul]
    rw [this, zc_T_smul, zc_D_smul]
  have hU : g 0 0 ^ 2 = EisInt.toC (A * A) := by
    rw [sq, ← hA]
    exact (map_mul EisInt.toComplex A A).symm
  have hE : g 0 1 * g 0 0 = EisInt.toC (B * A) := by
    rw [← hA, ← hB]
    exact (map_mul EisInt.toComplex B A).symm
  have hnU : Complex.normSq (EisInt.toC (A * A)) = 1 := by
    rw [← hU, map_pow Complex.normSq, hnormA, one_pow]
  have hcellw := cell_mul_unit (cell_of_eisBase (eisBase_of_open hp.1)) hnU
  have hgp' : eisBaseOpen (EisInt.toC (A * A) * zc p + EisInt.toC (B * A)) := by
    have := hgp.1
    rwa [hsmul, hU, hE] at this
  have hBA : B * A = 0 := eq_zero_of_cell_of_eisBaseOpen hcellw hgp'
  have hBA0 : EisInt.toC (B * A) = 0 := by rw [hBA]; exact map_zero EisInt.toComplex
  have hb0 : g 0 1 = 0 := by
    have h0 : g 0 1 * g 0 0 = 0 := by rw [hE, hBA0]
    exact (mul_eq_zero.1 h0).resolve_right ha0
  have hrot : eisBaseOpen (EisInt.toC (A * A) * zc p) := by
    rw [hBA0, add_zero] at hgp'
    exact hgp'
  have hAAa : (A * A).a = A.a * A.a - A.b * A.b := rfl
  have hAAb : (A * A).b = A.a * A.b + A.b * A.a - A.b * A.b := rfl
  have h00 : g 0 0 = 1 ∨ g 0 0 = -1 := by
    rcases eis_unit_cases hAint with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
        ⟨ha, hb⟩
    · left
      rw [← hA, show A = 1 from EisInt.ext ha hb]
      exact EisInt.toC_one
    · right
      rw [← hA, show A = -1 from EisInt.ext ha hb]
      exact EisInt.toC_neg_one
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inl ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inl ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inr ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
    · exact absurd hrot (not_eisBaseOpen_rot hp.1
        (Or.inr ⟨by rw [hAAa, ha, hb]; norm_num, by rw [hAAb, ha, hb]; norm_num⟩))
  have hdinv : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  have hmat : (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    rcases h00 with h | h
    · refine Or.inl ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h, hb0, hc, hdinv]
    · refine Or.inr ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h, hb0, hc, hdinv]
  exact smul_eq_self_of_coe_eq_pm_one hmat

/-- **Uniqueness for the Bianchi group.** An element carrying a point of the open box to a
point of the open box acts trivially. -/
theorem smul_eq_self_of_mem_eisBoxOpen {g : SL(2, ℂ)} (hg : g ∈ eisGroup) {p : H3}
    (hp : p ∈ eisBoxOpen) (hgp : g • p ∈ eisBoxOpen) : ∀ q : H3, g • q = q := by
  rcases le_or_gt (normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ))) 1 with hD | hD
  · exact smul_eq_self_of_le_one_eis hg hp hgp hD
  have hginv : g⁻¹ ∈ eisGroup := eisGroup.inv_mem hg
  have hpos : 0 < normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
    normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hpos' : 0 < normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) :=
    normSq_pos (denom_ne_zero (sl2_row_ne_zero g⁻¹) (toQ_imK (g • p)) (g • p).2)
  have h1 : (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
    smul_height g p
  have h2 : (g⁻¹ • (g • p)).1 2 = (g • p).1 2 /
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) := smul_height g⁻¹ (g • p)
  rw [inv_smul_smul, h1, div_div] at h2
  have hne : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) ≠ 0 :=
    ne_of_gt (mul_pos hpos hpos')
  have h3 := (eq_div_iff hne).1 h2
  have hmul : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
      normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) = 1 := by
    have h4 : p.1 2 * (normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) *
        normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ))) = p.1 2 * 1 := by
      rw [h3, mul_one]
    exact mul_left_cancel₀ (ne_of_gt p.2) h4
  have hDinv : normSq (((g⁻¹ 1 0 : ℂ) : ℍ) * toQ (g • p) + ((g⁻¹ 1 1 : ℂ) : ℍ)) ≤ 1 := by
    nlinarith [hmul, hD, hpos, hpos']
  have key : ∀ q : H3, g⁻¹ • q = q :=
    smul_eq_self_of_le_one_eis hginv hgp (by rw [inv_smul_smul]; exact hp) hDinv
  intro q
  have h := key (g • q)
  rw [inv_smul_smul] at h
  exact h.symm

end EisUniqueness

/-! ## The fundamental domain for the Bianchi group acting effectively -/

section EisFundamentalDomain

open Set MatrixGroups Quaternion Pointwise

/-- The plane `x + √3 y = c` of `ℝ³` is null: it is the preimage of a coordinate plane under a
shear of determinant `1`. -/
theorem volume_plane_sqrt3 (c : ℝ) :
    volume {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c} = 0 := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := !![1, Real.sqrt 3, 0; 0, 1, 0; 0, 0, 1] with hM
  have hdet : LinearMap.det (Matrix.toLin' M) ≠ 0 := by
    rw [LinearMap.det_toLin', Matrix.det_fin_three]
    simp [hM]
  have hset : {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c}
      = (Matrix.toLin' M) ⁻¹' {y : Fin 3 → ℝ | y 0 = c} := by
    ext x
    simp [hM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hset, Measure.addHaar_preimage_linearMap (μ := volume) hdet, volume_coord_eq, mul_zero]

theorem measurableSet_eisBox : MeasurableSet eisBox := by
  have h0 : Measurable fun p : H3 => p.1 0 := (measurable_pi_apply 0).comp measurable_subtype_coe
  have h1 : Measurable fun p : H3 => p.1 1 := (measurable_pi_apply 1).comp measurable_subtype_coe
  have h2 : Measurable fun p : H3 => p.1 2 := (measurable_pi_apply 2).comp measurable_subtype_coe
  have hv : Measurable fun p : H3 => p.1 0 + Real.sqrt 3 * p.1 1 := h0.add (h1.const_mul _)
  have hN : Measurable fun p : H3 => N p.1 := by
    unfold N
    exact ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
  have hset : eisBox = {p : H3 | 0 ≤ p.1 0} ∩ {p : H3 | p.1 0 ≤ 1 / 2} ∩
      {p : H3 | 0 ≤ p.1 0 + Real.sqrt 3 * p.1 1} ∩ {p : H3 | p.1 0 + Real.sqrt 3 * p.1 1 ≤ 1} ∩
      {p : H3 | 1 ≤ N p.1} := by
    ext p
    simp only [eisBox, eisBase, zc_re, zc_im, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset]
  exact ((((measurableSet_le measurable_const h0).inter (measurableSet_le h0 measurable_const)).inter
    (measurableSet_le measurable_const hv)).inter (measurableSet_le hv measurable_const)).inter
    (measurableSet_le measurable_const hN)

/-- **The boundary of the box is null.** It lies in two coordinate planes, two planes
`x + √3 y = c`, and the unit sphere. -/
theorem hvol_eisBox_sdiff_eisBoxOpen : hvol (eisBox \ eisBoxOpen) = 0 := by
  have hsub : eisBox \ eisBoxOpen ⊆
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 = 0}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 = 1 / 2}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = 0}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = 1}) ∪
      (Subtype.val ⁻¹' {x : Fin 3 → ℝ | N x = 1}) := by
    rintro p ⟨⟨⟨h1, h2, h3, h4⟩, hN⟩, hopen⟩
    have hopen' : ¬ (eisBaseOpen (zc p) ∧ 1 < N p.1) := hopen
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · rcases h3.lt_or_eq with h3 | h3
        · rcases h4.lt_or_eq with h4 | h4
          · exact Or.inr (le_antisymm (not_lt.1 fun hlt => hopen' ⟨⟨h1, h2, h3, h4⟩, hlt⟩) hN)
          · exact Or.inl (Or.inr h4)
        · exact Or.inl (Or.inl (Or.inr h3.symm))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h2)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl h1.symm)))
  refine measure_mono_null hsub ?_
  have hplane : ∀ (i : Fin 3) (c : ℝ),
      hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x i = c}) = 0 := by
    intro i c
    refine hvol_preimage_eq_zero ?_ (volume_coord_eq i c)
    have hset : {x : Fin 3 → ℝ | x i = c} = (fun f : Fin 3 → ℝ => f i) ⁻¹' {c} := rfl
    rw [hset]
    exact measurable_pi_apply i (measurableSet_singleton c)
  have hplane3 : ∀ c : ℝ,
      hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c}) = 0 := by
    intro c
    refine hvol_preimage_eq_zero ?_ (volume_plane_sqrt3 c)
    have hset : {x : Fin 3 → ℝ | x 0 + Real.sqrt 3 * x 1 = c}
        = (fun f : Fin 3 → ℝ => f 0 + Real.sqrt 3 * f 1) ⁻¹' {c} := rfl
    rw [hset]
    exact ((measurable_pi_apply 0).add ((measurable_pi_apply 1).const_mul _))
      (measurableSet_singleton c)
  have hsphere : hvol (Subtype.val ⁻¹' {x : Fin 3 → ℝ | N x = 1}) = 0 := by
    refine hvol_preimage_eq_zero ?_ volume_normOne
    have : {x : Fin 3 → ℝ | N x = 1}
        = (fun x : Fin 3 → ℝ => x 0 * x 0 + x 1 * x 1 + x 2 * x 2) ⁻¹' {1} := rfl
    rw [this]
    exact ((((measurable_pi_apply 0).mul (measurable_pi_apply 0)).add
      ((measurable_pi_apply 1).mul (measurable_pi_apply 1))).add
      ((measurable_pi_apply 2).mul (measurable_pi_apply 2))) (measurableSet_singleton 1)
  exact measure_union_null (measure_union_null (measure_union_null (measure_union_null
    (hplane 0 0) (hplane 0 (1 / 2))) (hplane3 0)) (hplane3 1)) hsphere

noncomputable def eisKer : Subgroup eisGroup := MonoidHom.ker (MulAction.toPermHom eisGroup H3)

instance eisKer.instNormal : eisKer.Normal :=
  MonoidHom.normal_ker (MulAction.toPermHom eisGroup H3)

/-- The Bianchi group made effective: the quotient by the kernel of its action, so
that `±1` is divided out. This is the group the box is a fundamental domain
for. -/
abbrev EisEff : Type := eisGroup ⧸ eisKer

noncomputable instance : MulAction EisEff H3 :=
  MulAction.compHom H3 (QuotientGroup.kerLift (MulAction.toPermHom eisGroup H3))

theorem EisEff.mk_smul (g : eisGroup) (p : H3) :
    (QuotientGroup.mk g : EisEff) • p = (g : SL(2, ℂ)) • p := rfl

theorem EisEff.mk_smul_set (g : eisGroup) (S : Set H3) :
    (QuotientGroup.mk g : EisEff) • S = (g : SL(2, ℂ)) • S := rfl

theorem EisEff.measurePreserving (q : EisEff) :
    MeasurePreserving (fun p : H3 => q • p) hvol hvol := by
  induction q using QuotientGroup.induction_on with
  | H g => exact measurePreserving_smul (g : SL(2, ℂ))

/-- **The fundamental domain.** The closed box over the rhombus is a fundamental domain for the Bianchi group acting
effectively. Covering is `exists_smul_mem_eisBox`; disjointness is uniqueness on
the open box, since the boundary is null. -/
theorem isFundamentalDomain_eisBox : IsFundamentalDomain EisEff eisBox hvol := by
  refine IsFundamentalDomain.mk'' measurableSet_eisBox.nullMeasurableSet ?_ ?_ ?_
  · filter_upwards with p
    obtain ⟨g, hg, hgp⟩ := exists_smul_mem_eisBox p
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, hgp⟩
  · intro q hq
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hsub : ((QuotientGroup.mk g : EisEff) • eisBox) ∩ eisBox ⊆
          ((g : SL(2, ℂ)) • (eisBox \ eisBoxOpen)) ∪ (eisBox \ eisBoxOpen) := by
        rintro p ⟨hp1, hp2⟩
        by_contra hcon
        rw [Set.mem_union, not_or] at hcon
        obtain ⟨hcon1, hcon2⟩ := hcon
        have hopen : p ∈ eisBoxOpen := by
          by_contra h
          exact hcon2 ⟨hp2, h⟩
        have hinv : (g : SL(2, ℂ))⁻¹ • p ∈ eisBox := by
          rw [EisEff.mk_smul_set, Set.mem_smul_set_iff_inv_smul_mem] at hp1
          exact hp1
        have hinvopen : (g : SL(2, ℂ))⁻¹ • p ∈ eisBoxOpen := by
          by_contra h
          refine hcon1 ?_
          rw [Set.mem_smul_set_iff_inv_smul_mem]
          exact ⟨hinv, h⟩
        have htriv : ∀ r : H3, (g : SL(2, ℂ))⁻¹ • r = r :=
          smul_eq_self_of_mem_eisBoxOpen (eisGroup.inv_mem g.2) hopen hinvopen
        have htrivg : ∀ r : H3, (g : SL(2, ℂ)) • r = r := by
          intro r
          have h := htriv ((g : SL(2, ℂ)) • r)
          rw [inv_smul_smul] at h
          exact h.symm
        refine hq ?_
        refine (QuotientGroup.eq_one_iff _).2 ?_
        rw [eisKer, MonoidHom.mem_ker]
        refine Equiv.ext fun r => ?_
        exact htrivg r
      refine measure_mono_null hsub ?_
      refine measure_union_null ?_ hvol_eisBox_sdiff_eisBoxOpen
      rw [measure_smul]
      exact hvol_eisBox_sdiff_eisBoxOpen
  · intro q
    exact (EisEff.measurePreserving q).quasiMeasurePreserving


instance : Countable eisGroup :=
  countable_of_properlyDiscontinuous basepoint (properlyDiscontinuous_of_le_eisGroup le_rfl)


instance : SMulInvariantMeasure EisEff H3 hvol :=
  ⟨fun q _ hs => (EisEff.measurePreserving q).measure_preimage hs.nullMeasurableSet⟩

instance : MeasurableConstSMul EisEff H3 :=
  ⟨fun q => (EisEff.measurePreserving q).measurable⟩

/-- The image of `Γ(3+ω)` in the effectively acting Bianchi group. -/
noncomputable def gammaSevenEff : Subgroup EisEff :=
  (gammaSeven.subgroupOf eisGroup).map (QuotientGroup.mk' eisKer)

/-- An element of `Γ(3+ω)` acting trivially is the identity: the action is free. -/
theorem eq_one_of_mem_gammaSeven_of_smul_eq {g : SL(2, ℂ)} (hg : g ∈ gammaSeven)
    (h : ∀ p : H3, g • p = p) : g = 1 := by
  by_contra hne
  exact gammaSeven_free hg hne basepoint (h basepoint)

/-- `Γ(3+ω)` injects into the effective quotient. -/
theorem gammaSeven_toEff_injective :
    Function.Injective (fun γ : gammaSeven =>
      (QuotientGroup.mk ⟨(γ : SL(2, ℂ)), gammaSeven_le_eisGroup γ.2⟩ : EisEff)) := by
  intro γ₁ γ₂ h
  have hmem : (⟨(γ₁ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₁.2⟩ : eisGroup)⁻¹ *
      ⟨(γ₂ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₂.2⟩ ∈ eisKer := QuotientGroup.eq.mp h
  rw [eisKer, MonoidHom.mem_ker] at hmem
  have htriv : ∀ p : H3, ((γ₁ : SL(2, ℂ))⁻¹ * (γ₂ : SL(2, ℂ))) • p = p := by
    intro p
    have := congrArg (fun e : Equiv.Perm H3 => e p) hmem
    simpa using this
  have hmul : (γ₁ : SL(2, ℂ))⁻¹ * (γ₂ : SL(2, ℂ)) ∈ gammaSeven :=
    gammaSeven.mul_mem (gammaSeven.inv_mem γ₁.2) γ₂.2
  have hone := eq_one_of_mem_gammaSeven_of_smul_eq hmul htriv
  exact Subtype.ext (inv_mul_eq_one.1 hone)

/-- A fundamental domain for the image of `Γ(3+ω)` is one for `Γ(3+ω)` itself. -/
theorem isFundamentalDomain_of_eisEff {F : Set H3}
    (h : IsFundamentalDomain gammaSevenEff F hvol) : IsFundamentalDomain gammaSeven F hvol := by
  refine ⟨h.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [h.ae_covers] with x hx
    obtain ⟨q, hq⟩ := hx
    obtain ⟨g, hg, hgq⟩ := Subgroup.mem_map.1 q.2
    refine ⟨⟨(g : SL(2, ℂ)), Subgroup.mem_subgroupOf.1 hg⟩, ?_⟩
    have : ((g : eisGroup) : EisEff) = (q : EisEff) := hgq
    show (g : SL(2, ℂ)) • x ∈ F
    have hq' : (q : EisEff) • x ∈ F := hq
    rw [← this] at hq'
    exact hq'
  · intro γ₁ γ₂ hne
    have hinj := gammaSeven_toEff_injective
    have hne' : (QuotientGroup.mk ⟨(γ₁ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₁.2⟩ : EisEff) ≠
        QuotientGroup.mk ⟨(γ₂ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₂.2⟩ := fun h' => hne (hinj h')
    have hmem : ∀ γ : gammaSeven,
        (QuotientGroup.mk ⟨(γ : SL(2, ℂ)), gammaSeven_le_eisGroup γ.2⟩ : EisEff) ∈
          gammaSevenEff := by
      intro γ
      exact Subgroup.mem_map.2 ⟨⟨(γ : SL(2, ℂ)), gammaSeven_le_eisGroup γ.2⟩,
        Subgroup.mem_subgroupOf.2 γ.2, rfl⟩
    exact h.aedisjoint (i := ⟨_, hmem γ₁⟩) (j := ⟨_, hmem γ₂⟩)
      (fun hcon => hne' (congrArg Subtype.val hcon))

/-- The covolume of `Γ(3+ω)` is a positive integer multiple of the volume of
the box: the index of its image in the effective Bianchi group. With the value of that volume,
`√3 L(2, χ₋₃)/8`, this is the covolume in closed form up to the index. -/
theorem exists_fundamentalDomain_gammaSeven_eq_nsmul :
    ∃ (n : ℕ) (F : Set H3), 0 < n ∧ IsFundamentalDomain gammaSeven F hvol ∧
      hvol F = n • hvol eisBox := by
  have hindex : gammaSevenEff.index ≠ 0 := by
    have hdvd : gammaSevenEff.index ∣ (gammaSeven.subgroupOf eisGroup).index :=
      Subgroup.index_map_dvd (gammaSeven.subgroupOf eisGroup) (QuotientGroup.mk'_surjective _)
    intro h
    rw [h] at hdvd
    exact relIndex_gammaSeven_eisGroup (zero_dvd_iff.1 hdvd)
  refine ⟨gammaSevenEff.index, ⋃ q : EisEff ⧸ gammaSevenEff, (Quotient.out q)⁻¹ • eisBox,
    Nat.pos_of_ne_zero hindex, ?_, ?_⟩
  · exact isFundamentalDomain_of_eisEff
      (isFundamentalDomain_iUnion_out isFundamentalDomain_eisBox gammaSevenEff)
  · exact measure_eq_index_smul gammaSevenEff (Nat.pos_of_ne_zero hindex)
      isFundamentalDomain_eisBox
      (isFundamentalDomain_iUnion_out isFundamentalDomain_eisBox gammaSevenEff)


end EisFundamentalDomain

/-! ## The volume of the box: `√3 L(2, χ₋₃)/8`

The box lies above the graph of `√(1 - x² - y²)` over the rhombus, so its volume is
`∫ dx dy / (2(1 - x² - y²))` over the rhombus (`hvol_above_graph`). In polar coordinates the
rhombus is `θ ∈ [-π/6, π/2]`, `r ≤ 1/(2 max(cos θ, cos(θ - π/3)))`; the radial integral is
`-¼ log (1 - R²)`, and the angle folds onto `[0, π/6]` by `θ ↦ θ - π/3` and `θ ↦ -θ`. -/

section EisVolume

open Set MatrixGroups Quaternion Pointwise
open scoped Real

/-- The rhombus as a subset of `ℝ²`. -/
def eisBaseSet : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 / 2 ∧ 0 ≤ z.1 + Real.sqrt 3 * z.2 ∧ z.1 + Real.sqrt 3 * z.2 ≤ 1}

theorem measurableSet_eisBaseSet : MeasurableSet eisBaseSet := by
  have hv : Measurable fun z : ℝ × ℝ => z.1 + Real.sqrt 3 * z.2 :=
    measurable_fst.add (measurable_snd.const_mul _)
  have hset : eisBaseSet = {z : ℝ × ℝ | 0 ≤ z.1} ∩ {z : ℝ × ℝ | z.1 ≤ 1 / 2} ∩
      {z : ℝ × ℝ | 0 ≤ z.1 + Real.sqrt 3 * z.2} ∩ {z : ℝ × ℝ | z.1 + Real.sqrt 3 * z.2 ≤ 1} := by
    ext z
    simp only [eisBaseSet, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset]
  exact (((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (measurableSet_le measurable_const hv)).inter (measurableSet_le hv measurable_const)

theorem eisBaseSet_pos {z : ℝ × ℝ} (hz : z ∈ eisBaseSet) : 2 / 3 ≤ 1 - z.1 ^ 2 - z.2 ^ 2 := by
  have h := normSq_le_of_eisBase (w := ⟨z.1, z.2⟩) hz
  rw [Complex.normSq_mk] at h
  nlinarith

theorem eisBox_eq_above_graph :
    eisBox = {p : H3 | ((p.1 0, p.1 1) ∈ eisBaseSet) ∧
      Real.sqrt (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2) ≤ p.1 2} := by
  ext p
  have ht : 0 < p.1 2 := p.2
  have hNval : N p.1 = p.1 0 * p.1 0 + p.1 1 * p.1 1 + p.1 2 * p.1 2 := rfl
  constructor
  · rintro ⟨hb, hN⟩
    refine ⟨hb, ?_⟩
    have hsq : 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2 ≤ (p.1 2) ^ 2 := by
      rw [hNval] at hN
      nlinarith [hN]
    calc Real.sqrt (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2)
        ≤ Real.sqrt ((p.1 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = p.1 2 := Real.sqrt_sq ht.le
  · rintro ⟨hz, hge⟩
    have hpos := eisBaseSet_pos hz
    have hsq : 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2 ≤ (p.1 2) ^ 2 := by
      have h := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - (p.1 0) ^ 2 - (p.1 1) ^ 2)
      nlinarith [hge, Real.sqrt_nonneg (1 - (p.1 0) ^ 2 - (p.1 1) ^ 2), h]
    refine ⟨hz, ?_⟩
    rw [hNval]
    nlinarith [hsq]

theorem hvol_eisBox_eq_plane_integral :
    hvol eisBox = ∫⁻ z in eisBaseSet, ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹) := by
  have hgm : Measurable fun z : ℝ × ℝ => Real.sqrt (1 - z.1 ^ 2 - z.2 ^ 2) := by
    fun_prop
  have hgpos : ∀ z ∈ eisBaseSet, 0 < Real.sqrt (1 - z.1 ^ 2 - z.2 ^ 2) := by
    intro z hz
    have := eisBaseSet_pos hz
    exact Real.sqrt_pos.2 (by linarith)
  rw [eisBox_eq_above_graph, hvol_above_graph measurableSet_eisBaseSet hgm hgpos]
  refine setLIntegral_congr_fun measurableSet_eisBaseSet fun z hz => ?_
  have hpos : 0 ≤ 1 - z.1 ^ 2 - z.2 ^ 2 := by
    have := eisBaseSet_pos hz
    linarith
  rw [Real.sq_sqrt hpos]

theorem cos_sub_pi_div_three' (θ : ℝ) :
    Real.cos (θ - π / 3) = Real.cos θ / 2 + Real.sqrt 3 / 2 * Real.sin θ := by
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring

/-- The radial extent of the rhombus in the direction `θ`. -/
noncomputable def eisRadial (θ : ℝ) : ℝ :=
  1 / (2 * max (Real.cos θ) (Real.cos (θ - π / 3)))

theorem half_lt_max_cos {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) :
    1 / 2 < max (Real.cos θ) (Real.cos (θ - π / 3)) := by
  have hpi := Real.pi_pos
  rcases le_or_gt θ (π / 6) with h | h
  · have habs : |θ| < π / 3 := abs_lt.2 ⟨by linarith [hθ.1], by linarith⟩
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith) habs
    rw [Real.cos_abs, Real.cos_pi_div_three] at this
    exact lt_max_of_lt_left this
  · have habs : |θ - π / 3| < π / 3 := abs_lt.2 ⟨by linarith, by linarith [hθ.2]⟩
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
    rw [Real.cos_abs, Real.cos_pi_div_three] at this
    exact lt_max_of_lt_right this

theorem eisRadial_pos {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) : 0 < eisRadial θ := by
  unfold eisRadial
  have := half_lt_max_cos hθ
  have : 0 < max (Real.cos θ) (Real.cos (θ - π / 3)) := by linarith
  positivity

theorem eisRadial_lt_one {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) : eisRadial θ < 1 := by
  unfold eisRadial
  have := half_lt_max_cos hθ
  rw [div_lt_one (by linarith)]
  linarith

theorem cos_nonneg_of_mem_eis {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) :
    0 ≤ Real.cos θ ∧ 0 ≤ Real.cos (θ - π / 3) := by
  have hpi := Real.pi_pos
  exact ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hθ.1]) hθ.2,
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hθ.1]) (by linarith [hθ.2])⟩

/-- A point of the polar target lies over the rhombus iff its angle is in `[-π/6, π/2]` and its
radius is at most `eisRadial`. -/
theorem polarCoord_symm_mem_eisBaseSet_iff {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    polarCoord.symm p ∈ eisBaseSet ↔ p.2 ∈ Icc (-(π / 6)) (π / 2) ∧ p.1 ≤ eisRadial p.2 := by
  obtain ⟨r, θ⟩ := p
  have ht : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  rw [ht] at hp
  simp only [mem_prod, mem_Ioi, mem_Ioo] at hp
  obtain ⟨hr, hθ1, hθ2⟩ := hp
  have hpi := Real.pi_pos
  have hsymm : polarCoord.symm (r, θ) = (r * Real.cos θ, r * Real.sin θ) := rfl
  have hv : r * Real.cos θ + Real.sqrt 3 * (r * Real.sin θ) = 2 * r * Real.cos (θ - π / 3) := by
    rw [cos_sub_pi_div_three']
    ring
  rw [hsymm]
  simp only [eisBaseSet, mem_setOf_eq, mem_Icc]
  rw [hv]
  constructor
  · rintro ⟨hx1, hx2, hv1, hv2⟩
    have hc1 : 0 ≤ Real.cos θ := by
      by_contra h
      push_neg at h
      nlinarith [mul_pos hr (neg_pos.2 h)]
    have hc2 : 0 ≤ Real.cos (θ - π / 3) := by
      by_contra h
      push_neg at h
      nlinarith [mul_pos hr (neg_pos.2 h)]
    have hθle : θ ≤ π / 2 := by
      by_contra h
      push_neg at h
      exact absurd hc1 (not_le.2 (Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith)))
    have hθge : -(π / 6) ≤ θ := by
      by_contra h
      push_neg at h
      have hneg := Real.cos_neg_of_pi_div_two_lt_of_lt (x := π / 3 - θ) (by linarith)
        (by linarith)
      rw [← Real.cos_neg, neg_sub] at hneg
      exact absurd hc2 (not_le.2 hneg)
    refine ⟨⟨hθge, hθle⟩, ?_⟩
    have hM := half_lt_max_cos ⟨hθge, hθle⟩
    unfold eisRadial
    rw [le_div_iff₀ (by linarith)]
    rcases le_total (Real.cos θ) (Real.cos (θ - π / 3)) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · rintro ⟨hθ, hR⟩
    have hM := half_lt_max_cos hθ
    obtain ⟨hc1, hc2⟩ := cos_nonneg_of_mem_eis hθ
    unfold eisRadial at hR
    rw [le_div_iff₀ (by linarith)] at hR
    have h1 : r * Real.cos θ ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left (le_max_left (Real.cos θ) (Real.cos (θ - π / 3))) hr.le
      linarith
    have h2 : r * Real.cos (θ - π / 3) ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left (le_max_right (Real.cos θ) (Real.cos (θ - π / 3))) hr.le
      linarith
    exact ⟨mul_nonneg hr.le hc1, h1, by nlinarith [mul_nonneg hr.le hc2], by linarith⟩

/-- The plane integral in polar coordinates. -/
theorem lintegral_eisBaseSet_polar :
    ∫⁻ z in eisBaseSet, ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹)
      = ∫⁻ θ in Icc (-(π / 6)) (π / 2), ∫⁻ r in Ioc 0 (eisRadial θ),
          ENNReal.ofReal (r / (2 * (1 - r ^ 2))) := by
  set F : ℝ × ℝ → ENNReal := fun z => ENNReal.ofReal ((2 * (1 - z.1 ^ 2 - z.2 ^ 2))⁻¹) with hF
  set G : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (p.1 / (2 * (1 - p.1 ^ 2))) with hG
  set S : Set (ℝ × ℝ) :=
    {p | p.2 ∈ Icc (-(π / 6)) (π / 2) ∧ 0 < p.1 ∧ p.1 ≤ eisRadial p.2} with hS
  have hGm : Measurable G := by fun_prop
  have hRm : Measurable eisRadial := by
    unfold eisRadial
    fun_prop
  have hSm : MeasurableSet S := by
    refine (measurableSet_Icc.preimage measurable_snd).inter ?_
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hRm.comp measurable_snd))
  have ht : polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π := rfl
  have hpt : ∀ p : ℝ × ℝ, polarCoord.target.indicator
      (fun p => ENNReal.ofReal p.1 • eisBaseSet.indicator F (polarCoord.symm p)) p
      = S.indicator G p := by
    intro p
    by_cases hp : p ∈ polarCoord.target
    · rw [indicator_of_mem hp]
      have hr : 0 < p.1 := by
        rw [ht] at hp
        exact hp.1
      by_cases hpS : p ∈ S
      · rw [indicator_of_mem hpS]
        have hmem : polarCoord.symm p ∈ eisBaseSet :=
          (polarCoord_symm_mem_eisBaseSet_iff hp).2 ⟨hpS.1, hpS.2.2⟩
        rw [indicator_of_mem hmem]
        have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
        simp only [hF, hG, smul_eq_mul, hsymm]
        rw [← ENNReal.ofReal_mul hr.le]
        congr 1
        have key : 1 - (p.1 * Real.cos p.2) ^ 2 - (p.1 * Real.sin p.2) ^ 2 = 1 - p.1 ^ 2 := by
          have := Real.sin_sq_add_cos_sq p.2
          linear_combination (-(p.1 ^ 2)) * this
        rw [key, div_eq_mul_inv]
      · rw [indicator_of_notMem hpS]
        have hnot : polarCoord.symm p ∉ eisBaseSet := fun h =>
          hpS ⟨((polarCoord_symm_mem_eisBaseSet_iff hp).1 h).1, hr,
            ((polarCoord_symm_mem_eisBaseSet_iff hp).1 h).2⟩
        rw [indicator_of_notMem hnot, smul_zero]
    · rw [indicator_of_notMem hp]
      have hpS : p ∉ S := by
        intro h
        apply hp
        rw [ht]
        exact ⟨h.2.1, ⟨by linarith [h.1.1, Real.pi_pos], by linarith [h.1.2, Real.pi_pos]⟩⟩
      rw [indicator_of_notMem hpS]
  calc ∫⁻ z in eisBaseSet, F z
      = ∫⁻ z, eisBaseSet.indicator F z := (lintegral_indicator measurableSet_eisBaseSet F).symm
    _ = ∫⁻ p in polarCoord.target,
          ENNReal.ofReal p.1 • eisBaseSet.indicator F (polarCoord.symm p) :=
        (lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p, S.indicator G p := by
        rw [← lintegral_indicator polarCoord.open_target.measurableSet]
        exact lintegral_congr hpt
    _ = ∫⁻ θ, ∫⁻ r, S.indicator G (r, θ) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_symm _ (hGm.indicator hSm).aemeasurable
    _ = ∫⁻ θ in Icc (-(π / 6)) (π / 2), ∫⁻ r in Ioc 0 (eisRadial θ),
          ENNReal.ofReal (r / (2 * (1 - r ^ 2))) := by
        rw [← lintegral_indicator measurableSet_Icc]
        refine lintegral_congr fun θ => ?_
        by_cases hθ : θ ∈ Icc (-(π / 6)) (π / 2)
        · rw [indicator_of_mem hθ, ← lintegral_indicator measurableSet_Ioc]
          refine lintegral_congr fun r => ?_
          by_cases hr : r ∈ Ioc 0 (eisRadial θ)
          · rw [indicator_of_mem hr, indicator_of_mem (show (r, θ) ∈ S from ⟨hθ, hr.1, hr.2⟩)]
          · rw [indicator_of_notMem hr, indicator_of_notMem (fun h => hr ⟨h.2.1, h.2.2⟩)]
        · rw [indicator_of_notMem hθ]
          have h0 : ∀ r, S.indicator G (r, θ) = 0 := fun r =>
            indicator_of_notMem (fun h => hθ h.1) _
          simp_rw [h0]
          simp

theorem lintegral_radial_eis {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 2)) :
    ∫⁻ r in Ioc 0 (eisRadial θ), ENNReal.ofReal (r / (2 * (1 - r ^ 2)))
      = ENNReal.ofReal (-(1/4) * Real.log (1 - eisRadial θ ^ 2)) := by
  have hR0 := eisRadial_pos hθ
  have hR1 := eisRadial_lt_one hθ
  have hpos : ∀ r ∈ Icc (0:ℝ) (eisRadial θ), 0 < 1 - r ^ 2 := by
    intro r hr
    nlinarith [hr.1, hr.2]
  have hcont : ContinuousOn (fun r : ℝ => r / (2 * (1 - r ^ 2))) (Icc 0 (eisRadial θ)) := by
    refine ContinuousOn.div continuousOn_id (by fun_prop) fun r hr => ?_
    have := hpos r hr
    positivity
  have hint : IntegrableOn (fun r : ℝ => r / (2 * (1 - r ^ 2))) (Ioc 0 (eisRadial θ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).1
      (ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le hR0.le]))
  rw [← ofReal_integral_eq_lintegral_ofReal hint, ← intervalIntegral.integral_of_le hR0.le,
    integral_radial hR0.le hR1]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  have := hpos r ⟨hr.1.le, hr.2⟩
  exact div_nonneg hr.1.le (by linarith)

theorem continuousOn_eisRadial : ContinuousOn eisRadial (Icc (-(π / 6)) (π / 2)) := by
  unfold eisRadial
  refine ContinuousOn.div continuousOn_const (by fun_prop) fun θ hθ => ?_
  have := half_lt_max_cos hθ
  exact ne_of_gt (by linarith)

theorem continuousOn_g_eis :
    ContinuousOn (fun θ => -(1/4) * Real.log (1 - eisRadial θ ^ 2)) (Icc (-(π / 6)) (π / 2)) := by
  refine continuousOn_const.mul (ContinuousOn.log ?_ fun θ hθ => ?_)
  · exact continuousOn_const.sub (continuousOn_eisRadial.pow 2)
  · have h1 := eisRadial_pos hθ
    have h2 := eisRadial_lt_one hθ
    exact ne_of_gt (by nlinarith)

theorem lintegral_Icc_g_eis :
    ∫⁻ θ in Icc (-(π / 6)) (π / 2), ENNReal.ofReal (-(1/4) * Real.log (1 - eisRadial θ ^ 2))
      = ENNReal.ofReal
          (∫ θ in (-(π / 6))..(π / 2), -(1/4) * Real.log (1 - eisRadial θ ^ 2)) := by
  have hpi := Real.pi_pos
  have hle : -(π / 6) ≤ π / 2 := by linarith
  have hint : IntegrableOn (fun θ => -(1/4) * Real.log (1 - eisRadial θ ^ 2))
      (Ioc (-(π / 6)) (π / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1
      (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hle]; exact continuousOn_g_eis))
  rw [← restrict_Ioc_eq_restrict_Icc, ← ofReal_integral_eq_lintegral_ofReal hint,
    ← intervalIntegral.integral_of_le hle]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  have h1 := eisRadial_pos ⟨hθ.1.le, hθ.2⟩
  have h2 := eisRadial_lt_one ⟨hθ.1.le, hθ.2⟩
  have hlog : Real.log (1 - eisRadial θ ^ 2) ≤ 0 :=
    Real.log_nonpos (by nlinarith) (by nlinarith)
  show (0:ℝ) ≤ -(1/4) * Real.log (1 - eisRadial θ ^ 2)
  linarith

/-- On `[-π/6, π/6]` the ray leaves the rhombus through `x = ½`. -/
theorem eisRadial_of_le {θ : ℝ} (hθ : θ ∈ Icc (-(π / 6)) (π / 6)) :
    eisRadial θ = 1 / (2 * Real.cos θ) := by
  have hpi := Real.pi_pos
  have hle : Real.cos (θ - π / 3) ≤ Real.cos θ := by
    rw [← Real.cos_abs θ, ← Real.cos_neg (θ - π / 3), neg_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [hθ.1])
      (abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  rw [eisRadial, max_eq_left hle]

/-- On `[π/6, π/2]` it leaves through `x + √3 y = 1`. -/
theorem eisRadial_of_ge {θ : ℝ} (hθ : θ ∈ Icc (π / 6) (π / 2)) :
    eisRadial θ = 1 / (2 * Real.cos (θ - π / 3)) := by
  have hpi := Real.pi_pos
  have hle : Real.cos θ ≤ Real.cos (θ - π / 3) := by
    rw [← Real.cos_abs (θ - π / 3)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [hθ.2])
      (abs_le.2 ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  rw [eisRadial, max_eq_right hle]

theorem continuousOn_h_eis :
    ContinuousOn (fun θ => -(1/4) * Real.log (1 - 1 / (4 * Real.cos θ ^ 2)))
      (Icc (-(π / 6)) (π / 6)) := by
  have hpi := Real.pi_pos
  have hc : ∀ θ ∈ Icc (-(π / 6)) (π / 6), 3 / 4 ≤ Real.cos θ ^ 2 := by
    intro θ hθ
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith)
      (abs_le.2 ⟨by linarith [hθ.1], hθ.2⟩ : |θ| ≤ π / 6)
    rw [Real.cos_abs, Real.cos_pi_div_six] at h
    have hs : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, sqrt3_sq]; norm_num
    nlinarith [Real.sqrt_nonneg 3]
  refine continuousOn_const.mul (ContinuousOn.log ?_ fun θ hθ => ?_)
  · refine continuousOn_const.sub (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
    intro θ hθ
    have := hc θ hθ
    positivity
  · have h := hc θ hθ
    have h4 : 0 < 4 * Real.cos θ ^ 2 := by positivity
    have : 1 / (4 * Real.cos θ ^ 2) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ h4 (by norm_num)]; linarith
    exact ne_of_gt (by linarith)

/-- The angular integral folds onto `[0, π/6]`. -/
theorem integral_g_fold_eis :
    ∫ θ in (-(π / 6))..(π / 2), -(1/4) * Real.log (1 - eisRadial θ ^ 2)
      = -∫ θ in (0:ℝ)..π / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) := by
  set g : ℝ → ℝ := fun θ => -(1/4) * Real.log (1 - eisRadial θ ^ 2) with hg
  set h : ℝ → ℝ := fun θ => -(1/4) * Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) with hh
  have hpi := Real.pi_pos
  have hgI : ∀ a b, -(π / 6) ≤ a → a ≤ b → b ≤ π / 2 → IntervalIntegrable g volume a b := by
    intro a b ha hab hb
    exact ContinuousOn.intervalIntegrable
      (continuousOn_g_eis.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))
  have hhI : ∀ a b, -(π / 6) ≤ a → a ≤ b → b ≤ π / 6 → IntervalIntegrable h volume a b := by
    intro a b ha hab hb
    exact ContinuousOn.intervalIntegrable
      (continuousOn_h_eis.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb))
  have hsq : ∀ c : ℝ, (1 / (2 * c)) ^ 2 = 1 / (4 * c ^ 2) := fun c => by
    rw [div_pow, mul_pow]; norm_num
  have h1 : ∫ θ in (-(π / 6))..(π / 2), g θ
      = (∫ θ in (-(π / 6))..(π / 6), g θ) + ∫ θ in (π / 6)..(π / 2), g θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hgI _ _ le_rfl (by linarith) (by linarith))
      (hgI _ _ (by linarith) (by linarith) le_rfl)).symm
  have h2 : ∫ θ in (-(π / 6))..(π / 6), g θ = ∫ θ in (-(π / 6))..(π / 6), h θ := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    simp only [hg, hh, eisRadial_of_le hθ, hsq]
  have h3 : ∫ θ in (π / 6)..(π / 2), g θ = ∫ θ in (-(π / 6))..(π / 6), h θ := by
    have := intervalIntegral.integral_comp_sub_right (a := π / 6) (b := π / 2) h (π / 3)
    rw [show π / 6 - π / 3 = -(π / 6) by ring, show π / 2 - π / 3 = π / 6 by ring] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by linarith)] at hθ
    simp only [hg, hh, eisRadial_of_ge hθ, hsq]
  have h4 : ∫ θ in (-(π / 6))..(π / 6), h θ
      = (∫ θ in (-(π / 6))..0, h θ) + ∫ θ in (0:ℝ)..(π / 6), h θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hhI _ _ le_rfl (by linarith) (by linarith))
      (hhI _ _ (by linarith) (by linarith) le_rfl)).symm
  have h5 : ∫ θ in (-(π / 6))..0, h θ = ∫ θ in (0:ℝ)..(π / 6), h θ := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := π / 6) h
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hh, Real.cos_neg]
  have h6 : ∫ θ in (0:ℝ)..(π / 6), h θ
      = -(1/4) * ∫ θ in (0:ℝ)..π / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2)) :=
    intervalIntegral.integral_const_mul _ _
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- The volume of the box as a single integral. -/
theorem hvol_eisBox_eq_ofReal_integral :
    hvol eisBox = ENNReal.ofReal
      (-∫ θ in (0:ℝ)..Real.pi / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))) := by
  rw [hvol_eisBox_eq_plane_integral, lintegral_eisBaseSet_polar,
    setLIntegral_congr_fun measurableSet_Icc fun θ hθ => lintegral_radial_eis hθ,
    lintegral_Icc_g_eis, integral_g_fold_eis]

/-- **The volume of the box over the rhombus is `√3 L(2, χ₋₃)/8`**: Humbert's formula for
`ℚ(√-3)`, the covolume of `PSL(2, ℤ[ω])`. -/
theorem hvol_eisBox_eq :
    hvol eisBox = ENNReal.ofReal (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8) := by
  rw [hvol_eisBox_eq_ofReal_integral,
    EisensteinLogSin.integral_log_one_sub_inv_four_cos_sq_pi_div_six, neg_neg]

theorem isOpen_eisBoxOpen : IsOpen eisBoxOpen := by
  have h0 : Continuous fun p : H3 => p.1 0 := (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun p : H3 => p.1 1 := (continuous_apply 1).comp continuous_subtype_val
  have h2 : Continuous fun p : H3 => p.1 2 := (continuous_apply 2).comp continuous_subtype_val
  have hv : Continuous fun p : H3 => p.1 0 + Real.sqrt 3 * p.1 1 := h0.add (continuous_const.mul h1)
  have hN : Continuous fun p : H3 => N p.1 := by
    unfold N
    exact ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
  have hset : eisBoxOpen = {p : H3 | 0 < p.1 0} ∩ {p : H3 | p.1 0 < 1 / 2} ∩
      {p : H3 | 0 < p.1 0 + Real.sqrt 3 * p.1 1} ∩ {p : H3 | p.1 0 + Real.sqrt 3 * p.1 1 < 1} ∩
      {p : H3 | 1 < N p.1} := by
    ext p
    simp only [eisBoxOpen, eisBaseOpen, zc_re, zc_im, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset]
  exact ((((isOpen_lt continuous_const h0).inter (isOpen_lt h0 continuous_const)).inter
    (isOpen_lt continuous_const hv)).inter (isOpen_lt hv continuous_const)).inter
    (isOpen_lt continuous_const hN)

theorem hvol_eisBox_pos : 0 < hvol eisBox := by
  have hpt : 1 / 4 + Real.sqrt 3 * (1 / 10) < 1 := by
    have : Real.sqrt 3 < 2 := by
      rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hs := sqrt3_pos
  have hmem : (⟨![1 / 4, 1 / 10, 2], by show (0:ℝ) < 2; norm_num⟩ : H3) ∈ eisBoxOpen := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show (0:ℝ) < 1 / 4; norm_num
    · show (1:ℝ) / 4 < 1 / 2; norm_num
    · show (0:ℝ) < 1 / 4 + Real.sqrt 3 * (1 / 10); positivity
    · show (1:ℝ) / 4 + Real.sqrt 3 * (1 / 10) < 1; exact hpt
    · show (1:ℝ) < 1 / 4 * (1 / 4) + 1 / 10 * (1 / 10) + 2 * 2; norm_num
  refine lt_of_lt_of_le (hvol_pos_of_isOpen isOpen_eisBoxOpen ⟨_, hmem⟩) (measure_mono ?_)
  rintro p ⟨hb, hN⟩
  exact ⟨eisBase_of_open hb, hN.le⟩

theorem sqrt3_mul_lchi3_pos : 0 < Real.sqrt 3 * EisensteinLogSin.lchi3 / 8 := by
  have h := hvol_eisBox_pos
  rw [hvol_eisBox_eq, ENNReal.ofReal_pos] at h
  exact h

/-- **The covolume of `Γ(3 + ω)` is a positive integer multiple of `√3 L(2, χ₋₃)/8`.** -/
theorem exists_fundamentalDomain_gammaSeven_eq_lchi3 :
    ∃ (n : ℕ) (F : Set H3), 0 < n ∧ IsFundamentalDomain gammaSeven F hvol ∧
      hvol F = ENNReal.ofReal (n * (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8)) := by
  obtain ⟨n, F, hn, hF, hvolF⟩ := exists_fundamentalDomain_gammaSeven_eq_nsmul
  refine ⟨n, F, hn, hF, ?_⟩
  rw [hvolF, hvol_eisBox_eq, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_natCast]

/-- **A hyperbolic volume that is a rational multiple of `√3 L(2, χ₋₃)`**: the covolume of
`Γ(3 + ω)`, `n · √3 L(2, χ₋₃)/8`. This is the second child of the goal in the platform's
decomposition. -/
theorem exists_hyperbolicVolume_rat_mul_LChiMinusThree :
    ∃ v ∈ hyperbolicVolumes, ∃ q : ℚ, 0 < q ∧
      v = (q : ℝ) * (Real.sqrt 3 *
        ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))) := by
  obtain ⟨n, F, hn, hF, hvolF⟩ := exists_fundamentalDomain_gammaSeven_eq_lchi3
  have hpos : 0 < (n : ℝ) * (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8) := by
    have := sqrt3_mul_lchi3_pos
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  refine ⟨(n : ℝ) * (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8),
    ⟨↥gammaSeven, inferInstance, inferInstance, isKleinian_gammaSeven, F, hF, hvolF, hpos⟩,
    (n : ℚ) / 8, by positivity, ?_⟩
  unfold EisensteinLogSin.lchi3
  push_cast
  ring

end EisVolume

end Thurston23
