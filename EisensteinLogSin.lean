import CatalanLogSin

/-!
# The log-sine integral at `π/3` and `L(2, χ₋₃)`

The analytic core of the covolume of the Bianchi group `PSL(2, ℤ[ω])`:

* `integral_log_two_sin_eq_tsum`: for `0 ≤ a < π/2`,
  `∫₀^a log (2 sin θ) dθ = -∑ sin(2na)/(2n²)`, the Clausen function. This is the argument of
  `CatalanLogSin.integral_log_two_sin` with the endpoint `π/4` replaced by `a`: the Taylor series
  of `log (1 - z)` along the arc `θ ↦ r e^{2iθ}`, then `r → 1` by Abel's theorem on the series
  side and dominated convergence on the integral side.
* `hasSum_sin_two_pi_div_three`: at `a = π/3` the series is `(√3/4) L(2, χ₋₃)`, where
  `L(2, χ₋₃) = ∑ (1/(3n+1)² - 1/(3n+2)²)`, since `sin(2πn/3)` is `0`, `√3/2`, `-√3/2` according
  to `n mod 3`.
* `integral_log_one_sub_inv_four_cos_sq_pi_div_six`:
  `∫₀^{π/6} log (1 - 1/(4 cos²θ)) dθ = -√3 L(2, χ₋₃)/8`, by the same trigonometric identity as at
  `π/4`. Minus this integral is the volume of the fundamental domain of the Bianchi group.
-/

open Real MeasureTheory intervalIntegral Filter Topology

namespace EisensteinLogSin

open CatalanLogSin

/-- `L(2, χ₋₃) = ∑ (1/(3n+1)² - 1/(3n+2)²)`, the Dirichlet `L`-value of the character of
`ℚ(√-3)` at `2`. -/
noncomputable def lchi3 : ℝ :=
  ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))

/-! ### The log-sine integral on `[0, a]` -/

/-- The `n`-th term, integrated over `[0, a]`. -/
theorem integral_term_arc (a : ℝ) (n : ℕ) (r : ℝ) :
    ∫ θ in (0:ℝ)..a, r ^ n * Real.cos (n * (2 * θ)) / n
      = r ^ n * Real.sin (n * (2 * a)) / (2 * n ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hcos : ∫ θ in (0:ℝ)..a, Real.cos (n * (2 * θ)) = Real.sin (n * (2 * a)) / (2 * n) := by
    have h : ∀ θ : ℝ, Real.cos (n * (2 * θ)) = Real.cos ((2 * n) * θ) := by
      intro θ; ring_nf
    simp_rw [h]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x)
      (by positivity : (2 * (n:ℝ)) ≠ 0)]
    rw [integral_cos]
    have : (2 * (n:ℝ)) * a = n * (2 * a) := by ring
    rw [this]
    simp [smul_eq_mul]
    field_simp
  calc ∫ θ in (0:ℝ)..a, r ^ n * Real.cos (n * (2 * θ)) / n
      = (r ^ n / n) * ∫ θ in (0:ℝ)..a, Real.cos (n * (2 * θ)) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext θ
        ring
    _ = r ^ n * Real.sin (n * (2 * a)) / (2 * n ^ 2) := by
        rw [hcos]
        field_simp
        try ring

/-- Term-by-term integration along the arc `[0, a]`, for a radius inside the disk. -/
theorem integral_arc_gen {a : ℝ} (ha : 0 ≤ a) {r : ℝ} (hr : |r| < 1) :
    ∫ θ in (0:ℝ)..a, (-Real.log ‖1 - (r : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
      = ∑' n : ℕ, r ^ n * Real.sin (n * (2 * a)) / (2 * n ^ 2) := by
  have hcont : ∀ n : ℕ, Continuous fun θ : ℝ => r ^ n * Real.cos (n * (2 * θ)) / n := by
    intro n
    fun_prop
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => r ^ n * Real.cos (n * (2 * θ)) / n)
      (volume.restrict (Set.Ioc (0:ℝ) a)) := fun n => (hcont n).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∫⁻ θ in Set.Ioc (0:ℝ) a,
      ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ ≤ ENNReal.ofReal (|r| ^ n * a) := by
    intro n
    have hle : ∀ θ : ℝ, ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ ≤ ENNReal.ofReal (|r| ^ n) := by
      intro θ
      rw [← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      rw [norm_div, norm_mul]
      have h1 : ‖r ^ n‖ = |r| ^ n := by
        rw [Real.norm_eq_abs, abs_pow]
      have h2 : ‖Real.cos (n * (2 * θ))‖ ≤ 1 := by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _
      have h3 : (1:ℝ) ≤ ‖(n : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
        exact hn1
      rw [h1]
      have hnum : |r| ^ n * ‖Real.cos (n * (2 * θ))‖ ≤ |r| ^ n :=
        (mul_le_mul_of_nonneg_left h2 (by positivity)).trans_eq (mul_one _)
      have hden : |r| ^ n * ‖Real.cos (n * (2 * θ))‖ / ‖(n : ℝ)‖
          ≤ |r| ^ n * ‖Real.cos (n * (2 * θ))‖ :=
        div_le_self (by positivity) h3
      linarith
    calc ∫⁻ θ in Set.Ioc (0:ℝ) a, ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ
        ≤ ∫⁻ _ in Set.Ioc (0:ℝ) a, ENNReal.ofReal (|r| ^ n) := lintegral_mono hle
      _ = ENNReal.ofReal (|r| ^ n) * volume (Set.Ioc (0:ℝ) a) := by
          rw [setLIntegral_const]
      _ = ENNReal.ofReal (|r| ^ n * a) := by
          rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  have hsummable : Summable fun n : ℕ => |r| ^ n * a :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).mul_right _
  have hfin : ∑' n : ℕ, ∫⁻ θ in Set.Ioc (0:ℝ) a,
      ‖r ^ n * Real.cos (n * (2 * θ)) / n‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsummable]
    exact ENNReal.ofReal_ne_top
  have hpt : ∀ θ : ℝ,
      (-Real.log ‖1 - (r : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
        = ∑' n : ℕ, r ^ n * Real.cos (n * (2 * θ)) / n := fun θ =>
    ((hasSum_neg_log_norm_circle hr (2 * θ)).tsum_eq).symm
  rw [intervalIntegral.integral_of_le ha]
  simp_rw [hpt]
  rw [MeasureTheory.integral_tsum hmeas hfin]
  refine tsum_congr fun n => ?_
  have h := integral_term_arc a n r
  rw [intervalIntegral.integral_of_le ha] at h
  exact h

/-- The boundary series is absolutely summable. -/
theorem summable_sin_div (a : ℝ) :
    Summable (fun n : ℕ => Real.sin (n * (2 * a)) / (2 * n ^ 2)) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := summable_one_div_nat_pow.2 one_lt_two
  refine Summable.of_norm (hbase.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0:ℝ) < 2 * (n:ℝ) ^ 2 := by positivity
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos,
    div_le_div_iff₀ hpos (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (n * (2 * a)))
    (sq_nonneg (n:ℝ)), sq_nonneg (n:ℝ)]

/-- **The log-sine integral on `[0, a]`**, for `0 ≤ a < π/2`:
`∫₀^a log (2 sin θ) dθ = -∑ sin(2na)/(2n²)`. -/
theorem integral_log_two_sin_eq_tsum {a : ℝ} (ha0 : 0 ≤ a) (ha : a < π/2) :
    ∫ θ in (0:ℝ)..a, Real.log (2 * Real.sin θ)
      = -∑' n : ℕ, Real.sin (n * (2 * a)) / (2 * n ^ 2) := by
  have hIoo : Set.Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT (by norm_num)
  set σ : ℝ := ∑' n : ℕ, Real.sin (n * (2 * a)) / (2 * n ^ 2) with hσ
  -- Abel's limit theorem on the series side
  have habel : Tendsto (fun r : ℝ => ∑' n : ℕ, (Real.sin (n * (2 * a)) / (2 * n ^ 2)) * r ^ n)
      (𝓝[<] (1:ℝ)) (𝓝 σ) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt (summable_sin_div a).hasSum.tendsto_sum_nat
  -- inside the disk the integral is that series
  have hev : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ),
      (∫ θ in (0:ℝ)..a,
          -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
        = ∑' n : ℕ, (Real.sin (n * (2 * a)) / (2 * n ^ 2)) * r ^ n := by
    filter_upwards [hIoo] with r hr
    have habs : |r| < 1 := by
      rw [abs_of_pos hr.1]
      exact hr.2
    rw [integral_arc_gen ha0 habs]
    exact tsum_congr fun n => by ring
  -- dominated convergence on the integral side
  have hdct : Tendsto (fun r : ℝ =>
      ∫ θ in (0:ℝ)..a,
        -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
      (𝓝[<] (1:ℝ)) (𝓝 (∫ θ in (0:ℝ)..a, -Real.log (2 * Real.sin θ))) := by
    have hsin2 : ∀ θ ∈ Set.uIoc (0:ℝ) a, 0 < Real.sin (2 * θ) := by
      intro θ hθ
      rw [Set.uIoc_of_le ha0] at hθ
      refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
      have := hθ.2
      linarith
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => Real.log 2 + |Real.log (Real.sin (2 * θ))|) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun r => ?_
      refine (Real.measurable_log.comp ?_).neg.aestronglyMeasurable
      refine (Continuous.norm ?_).measurable
      fun_prop
    · filter_upwards [hIoo] with r hr
      refine Eventually.of_forall fun θ hθ => ?_
      rw [Real.norm_eq_abs, abs_neg]
      have h2θ := hsin2 θ hθ
      have := abs_log_norm_le hr.1.le hr.2.le h2θ
      simpa using this
    · have hbase : IntervalIntegrable (Real.log ∘ Real.sin) volume 0 (2 * a) :=
        intervalIntegrable_log_sin
      have hscale : IntervalIntegrable (fun x => (Real.log ∘ Real.sin) (2 * x)) volume
          (0 / 2) ((2 * a) / 2) := hbase.comp_mul_left
      have hscale' : IntervalIntegrable (fun x => Real.log (Real.sin (2 * x))) volume 0 a := by
        have h0 : (0:ℝ) / 2 = 0 := by norm_num
        have h1 : (2 * a) / 2 = a := by ring
        rw [h0, h1] at hscale
        exact hscale
      exact intervalIntegrable_const.add hscale'.abs
    · refine Eventually.of_forall fun θ hθ => ?_
      have hθ' : θ ∈ Set.Ioc (0:ℝ) a := by rwa [Set.uIoc_of_le ha0] at hθ
      have hθ2 : θ ≤ π/2 := by linarith [hθ'.2]
      have hne : ‖1 - Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖ ≠ 0 := by
        rw [norm_one_sub_exp hθ'.1.le hθ2]
        have : 0 < Real.sin θ :=
          Real.sin_pos_of_pos_of_lt_pi hθ'.1 (by linarith [Real.pi_pos])
        positivity
      have hcont : ContinuousAt
          (fun r : ℝ => -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖) 1 := by
        have hnorm : ContinuousAt
            (fun r : ℝ => ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖) 1 :=
          (Continuous.norm (by fun_prop)).continuousAt
        exact (hnorm.log (by simpa using hne)).neg
      have hlim : Tendsto (fun r : ℝ =>
          -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
          (𝓝[<] (1:ℝ))
          (𝓝 (-Real.log ‖1 - ((1:ℝ):ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hval : -Real.log ‖1 - ((1:ℝ):ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖
          = -Real.log (2 * Real.sin θ) := by
        rw [Complex.ofReal_one, one_mul, norm_one_sub_exp hθ'.1.le hθ2]
      rw [hval] at hlim
      exact hlim
  have habel' : Tendsto (fun r : ℝ =>
      ∫ θ in (0:ℝ)..a,
        -Real.log ‖1 - (r:ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)‖)
      (𝓝[<] (1:ℝ)) (𝓝 σ) := habel.congr' (hev.mono fun r h => h.symm)
  have hlimit : (∫ θ in (0:ℝ)..a, -Real.log (2 * Real.sin θ)) = σ :=
    tendsto_nhds_unique hdct habel'
  rw [intervalIntegral.integral_neg] at hlimit
  linarith [hlimit]

/-! ### The value at `π/3` -/

/-- `∑ 1/(3m+c)²` converges for `c ≥ 1`. -/
theorem summable_one_div_three_mul_add_sq {c : ℝ} (hc : 1 ≤ c) :
    Summable (fun m : ℕ => 1 / ((3 * m + c) ^ 2 : ℝ)) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := summable_one_div_nat_pow.2 one_lt_two
    have h2 := (summable_nat_add_iff 1).2 h
    refine h2.congr fun n => ?_
    push_cast
    ring
  refine hbase.of_nonneg_of_le (fun m => ?_) fun m => ?_
  · have : 0 < 3 * (m : ℝ) + c := by
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    positivity
  · have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : 0 < 3 * (m : ℝ) + c := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem sin_nat_mul_two_pi_div_three_three_mul (m : ℕ) :
    Real.sin (((3 * m : ℕ) : ℝ) * (2 * (π / 3))) = 0 := by
  have h : ((3 * m : ℕ) : ℝ) * (2 * (π / 3)) = ((2 * m : ℕ) : ℝ) * π := by
    push_cast
    ring
  rw [h, Real.sin_nat_mul_pi]

theorem sin_nat_mul_two_pi_div_three_add_one (m : ℕ) :
    Real.sin (((3 * m + 1 : ℕ) : ℝ) * (2 * (π / 3))) = Real.sqrt 3 / 2 := by
  have h : ((3 * m + 1 : ℕ) : ℝ) * (2 * (π / 3)) = (π - π / 3) + m * (2 * π) := by
    push_cast
    ring
  rw [h, Real.sin_add_nat_mul_two_pi, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem sin_nat_mul_two_pi_div_three_add_two (m : ℕ) :
    Real.sin (((3 * m + 2 : ℕ) : ℝ) * (2 * (π / 3))) = -(Real.sqrt 3 / 2) := by
  have h : ((3 * m + 2 : ℕ) : ℝ) * (2 * (π / 3)) = (π / 3 + π) + m * (2 * π) := by
    push_cast
    ring
  rw [h, Real.sin_add_nat_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_three]

/-- **The boundary series at `π/3`** is `(√3/4) L(2, χ₋₃)`. -/
theorem hasSum_sin_two_pi_div_three :
    HasSum (fun n : ℕ => Real.sin (n * (2 * (π / 3))) / (2 * n ^ 2))
      (Real.sqrt 3 / 4 * lchi3) := by
  set f : ℕ → ℝ := fun n => Real.sin (n * (2 * (π / 3))) / (2 * n ^ 2) with hf
  set A : ℕ → ℝ := fun m => 1 / ((3 * m + 1) ^ 2 : ℝ) with hA
  set B : ℕ → ℝ := fun m => 1 / ((3 * m + 2) ^ 2 : ℝ) with hB
  have hAs : Summable A := summable_one_div_three_mul_add_sq (by norm_num)
  have hBs : Summable B := summable_one_div_three_mul_add_sq (by norm_num)
  have hL : lchi3 = ∑' m, A m - ∑' m, B m := by
    unfold lchi3
    exact hAs.tsum_sub hBs
  set f₁ : ℕ → ℝ := fun n => if n % 3 = 1 then f n else 0 with hf₁
  set f₂ : ℕ → ℝ := fun n => if n % 3 = 2 then f n else 0 with hf₂
  have hg₁ : Function.Injective (fun m : ℕ => 3 * m + 1) := fun x y h => by
    simp only at h; omega
  have hg₂ : Function.Injective (fun m : ℕ => 3 * m + 2) := fun x y h => by
    simp only at h; omega
  have h₁ : HasSum f₁ (Real.sqrt 3 / 4 * ∑' m, A m) := by
    have hz : ∀ n ∉ Set.range (fun m : ℕ => 3 * m + 1), f₁ n = 0 := by
      intro n hn
      have : n % 3 ≠ 1 := fun h => hn ⟨n / 3, show 3 * (n / 3) + 1 = n by omega⟩
      simp [hf₁, this]
    rw [← hg₁.hasSum_iff hz]
    have hfun : f₁ ∘ (fun m : ℕ => 3 * m + 1) = fun m => Real.sqrt 3 / 4 * A m := by
      funext m
      have hmod : (3 * m + 1) % 3 = 1 := by omega
      simp only [Function.comp_apply, hf₁, hmod, if_true, hf, hA]
      rw [sin_nat_mul_two_pi_div_three_add_one]
      have hne : (3 * (m : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [hfun]
    exact hAs.hasSum.mul_left _
  have h₂ : HasSum f₂ (-(Real.sqrt 3 / 4) * ∑' m, B m) := by
    have hz : ∀ n ∉ Set.range (fun m : ℕ => 3 * m + 2), f₂ n = 0 := by
      intro n hn
      have : n % 3 ≠ 2 := fun h => hn ⟨n / 3, show 3 * (n / 3) + 2 = n by omega⟩
      simp [hf₂, this]
    rw [← hg₂.hasSum_iff hz]
    have hfun : f₂ ∘ (fun m : ℕ => 3 * m + 2) = fun m => -(Real.sqrt 3 / 4) * B m := by
      funext m
      have hmod : (3 * m + 2) % 3 = 2 := by omega
      simp only [Function.comp_apply, hf₂, hmod, if_true, hf, hB]
      rw [sin_nat_mul_two_pi_div_three_add_two]
      have hne : (3 * (m : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [hfun]
    exact hBs.hasSum.mul_left _
  have hsplit : f = f₁ + f₂ := by
    funext n
    simp only [Pi.add_apply, hf₁, hf₂]
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · have h1 : n % 3 ≠ 1 := by omega
      have h2 : n % 3 ≠ 2 := by omega
      rw [if_neg h1, if_neg h2, add_zero]
      obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
      simp only [hf]
      rw [sin_nat_mul_two_pi_div_three_three_mul, zero_div]
    · have h2 : n % 3 ≠ 2 := by omega
      rw [if_pos h, if_neg h2, add_zero]
    · have h1 : n % 3 ≠ 1 := by omega
      rw [if_neg h1, if_pos h, zero_add]
  rw [hsplit]
  convert h₁.add h₂ using 1
  rw [hL]
  ring

/-- **The log-sine integral at `π/3`.** `∫₀^{π/3} log (2 sin θ) dθ = -(√3/4) L(2, χ₋₃)`. -/
theorem integral_log_two_sin_pi_div_three :
    ∫ θ in (0:ℝ)..π / 3, Real.log (2 * Real.sin θ) = -(Real.sqrt 3 / 4 * lchi3) := by
  have hpi := Real.pi_pos
  rw [integral_log_two_sin_eq_tsum (by positivity) (by linarith), hasSum_sin_two_pi_div_three.tsum_eq]

/-! ### The volume integral at `π/6` -/

/-- **`∫₀^{π/6} log (1 - 1/(4 cos²θ)) dθ = -√3 L(2, χ₋₃)/8`.** Minus this is the volume of
the fundamental domain of the Bianchi group `PSL(2, ℤ[ω])`. -/
theorem integral_log_one_sub_inv_four_cos_sq_pi_div_six :
    ∫ θ in (0:ℝ)..π / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = -(Real.sqrt 3 * lchi3 / 8) := by
  have hpi := Real.pi_pos
  have hI3 : IntervalIntegrable (fun θ => Real.log (2 * Real.sin (3 * θ))) volume 0 (π / 6) := by
    have h : IntervalIntegrable (fun x => Real.log (2 * Real.sin (3 * x))) volume (0 / 3)
        ((π / 2) / 3) :=
      (intervalIntegrable_log_two_sin (a := 0) (b := π / 2) le_rfl (by positivity)
        (by linarith)).comp_mul_left
    rw [show (0:ℝ) / 3 = 0 by ring, show (π / 2) / 3 = π / 6 by ring] at h
    exact h
  have hI2 : IntervalIntegrable (fun θ => Real.log (2 * Real.sin (2 * θ))) volume 0 (π / 6) := by
    have h : IntervalIntegrable (fun x => Real.log (2 * Real.sin (2 * x))) volume (0 / 2)
        ((π / 3) / 2) :=
      (intervalIntegrable_log_two_sin (a := 0) (b := π / 3) le_rfl (by positivity)
        (by linarith)).comp_mul_left
    rw [show (0:ℝ) / 2 = 0 by ring, show (π / 3) / 2 = π / 6 by ring] at h
    exact h
  have hIc : IntervalIntegrable (fun θ => Real.log (2 * Real.cos θ)) volume 0 (π / 6) := by
    have h : IntervalIntegrable (fun x => Real.log (2 * Real.sin (π / 2 - x))) volume
        (π / 2 - π / 3) (π / 2 - π / 2) :=
      (intervalIntegrable_log_two_sin (a := π / 3) (b := π / 2) (by positivity) (by linarith)
        (by linarith)).comp_sub_left (π / 2)
    rw [sub_self, show π / 2 - π / 3 = π / 6 by ring] at h
    simpa only [Real.sin_pi_div_two_sub] using h.symm
  have hcongr : ∫ θ in (0:ℝ)..π / 6, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = ∫ θ in (0:ℝ)..π / 6, (Real.log (2 * Real.sin (3 * θ)) - Real.log (2 * Real.sin (2 * θ))
          - Real.log (2 * Real.cos θ)) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by positivity)] at hθ
    exact log_one_sub_inv_four_cos_sq hθ.1 (by linarith [hθ.2])
  -- the three log-sine integrals
  have h3 : ∫ θ in (0:ℝ)..π / 6, Real.log (2 * Real.sin (3 * θ)) = 0 := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := π / 6)
      (fun u => Real.log (2 * Real.sin u)) (c := 3) (by norm_num)
    rw [show (3:ℝ) * 0 = 0 by ring, show (3:ℝ) * (π / 6) = π / 2 by ring,
      integral_log_two_sin_pi_div_two] at h
    rw [h, smul_zero]
  have h2 : ∫ θ in (0:ℝ)..π / 6, Real.log (2 * Real.sin (2 * θ))
      = (1 / 2) * ∫ u in (0:ℝ)..π / 3, Real.log (2 * Real.sin u) := by
    have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := π / 6)
      (fun u => Real.log (2 * Real.sin u)) (c := 2) (by norm_num)
    rw [show (2:ℝ) * 0 = 0 by ring, show (2:ℝ) * (π / 6) = π / 3 by ring] at h
    rw [h, smul_eq_mul]
    norm_num
  have hc : ∫ θ in (0:ℝ)..π / 6, Real.log (2 * Real.cos θ)
      = -∫ u in (0:ℝ)..π / 3, Real.log (2 * Real.sin u) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 6)
      (fun u => Real.log (2 * Real.sin u)) (π / 2)
    rw [sub_zero, show π / 2 - π / 6 = π / 3 by ring] at h
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_log_two_sin (a := 0) (b := π / 3) le_rfl (by positivity) (by linarith))
      (intervalIntegrable_log_two_sin (a := π / 3) (b := π / 2) (by positivity) (by linarith)
        (by linarith))
    rw [integral_log_two_sin_pi_div_two] at hadj
    have hcos : ∫ θ in (0:ℝ)..π / 6, Real.log (2 * Real.cos θ)
        = ∫ θ in (0:ℝ)..π / 6, Real.log (2 * Real.sin (π / 2 - θ)) := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [Real.sin_pi_div_two_sub]
    rw [hcos, h]
    linarith
  rw [hcongr, intervalIntegral.integral_sub (hI3.sub hI2) hIc,
    intervalIntegral.integral_sub hI3 hI2, h3, h2, hc, integral_log_two_sin_pi_div_three]
  ring

end EisensteinLogSin
