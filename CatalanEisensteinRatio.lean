import Mathlib

/-!
# `G / (√3 L(2, χ₋₃))` is not a rational with small denominator

The third child of the goal's decomposition asks that Catalan's constant
`G = ∑ (-1)ⁿ/(2n+1)²` is not a rational multiple of `√3 L(2, χ₋₃)`,
`L(2, χ₋₃) = ∑ (1/(3n+1)² - 1/(3n+2)²)`. That is open. This file proves the finite
shadow of it: no rational `q` with denominator below `1733` satisfies
`G = q √3 L(2, χ₋₃)` (`catalan_ne_rat_mul_sqrt_three_LChiMinusThree_of_den_lt`).

* Tails of `∑ 1/(mk+c)²` are bracketed by telescoping sums (`tsum_le`, `le_tsum`):
  with `y = c - m/2`, the tail lies in `[1/(my) - (m/12)/y³, 1/(my)]`.
* Forty terms and those tails give `G ∈ [0.91596551, 0.91596568]` and
  `L(2, χ₋₃) ∈ [0.78130225, 0.78130260]` (`catalan_bounds`, `lchi3_bounds`).
* Hence the ratio lies strictly between `664/981` and `509/752` (`ratio_mem`), two
  Farey neighbours (`981 · 509 - 664 · 752 = 1`), and any fraction strictly between
  Farey neighbours `a/b < c/d` has denominator at least `b + d` (`add_le_den_of_farey`).
-/

set_option autoImplicit false

namespace CatalanEisensteinRatio

open Finset Filter Topology

/-! ### Telescoping bounds for `∑ 1/(mk+c)²` -/

theorem tel_upper {m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    1 / (y + m / 2) ^ 2 ≤ 1 / (m * y) - 1 / (m * (y + m)) := by
  have hym : 0 < y + m := by linarith
  have e : 1 / (m * y) - 1 / (m * (y + m)) = 1 / (y * (y + m)) := by
    field_simp
    ring
  rw [e]
  exact one_div_le_one_div_of_le (mul_pos hy hym) (by nlinarith)

theorem tel_lower {m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    (1 / (m * y) - m / 12 / y ^ 3) - (1 / (m * (y + m)) - m / 12 / (y + m) ^ 3)
      ≤ 1 / (y + m / 2) ^ 2 := by
  have hym : 0 < y + m := by linarith
  have hx : 0 < y + m / 2 := by linarith
  have e : 1 / (y + m / 2) ^ 2
      - ((1 / (m * y) - m / 12 / y ^ 3) - (1 / (m * (y + m)) - m / 12 / (y + m) ^ 3))
      = m ^ 4 * (7 * y * (y + m) + m ^ 2) / (48 * (y + m / 2) ^ 2 * (y * (y + m)) ^ 3) := by
    field_simp
    ring
  have hnn : 0 ≤ m ^ 4 * (7 * y * (y + m) + m ^ 2) / (48 * (y + m / 2) ^ 2 * (y * (y + m)) ^ 3) := by
    apply div_nonneg
    · have : 0 < y * (y + m) := mul_pos hy hym
      positivity
    · have : 0 < y * (y + m) := mul_pos hy hym
      positivity
  linarith

/-- The upper telescoping function. -/
noncomputable def upF (m c : ℝ) (k : ℕ) : ℝ := 1 / (m * (m * k + c - m / 2))

/-- The lower telescoping function. -/
noncomputable def loF (m c : ℝ) (k : ℕ) : ℝ :=
  1 / (m * (m * k + c - m / 2)) - m / 12 / (m * k + c - m / 2) ^ 3

theorem term_le {m c : ℝ} (hm : 0 < m) (hc : m / 2 < c) (k : ℕ) :
    1 / (m * k + c) ^ 2 ≤ upF m c k - upF m c (k + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hy : 0 < m * k + c - m / 2 := by nlinarith
  have h := tel_upper hm hy
  unfold upF
  push_cast
  convert h using 2 <;> ring

theorem le_term {m c : ℝ} (hm : 0 < m) (hc : m / 2 < c) (k : ℕ) :
    loF m c k - loF m c (k + 1) ≤ 1 / (m * k + c) ^ 2 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hy : 0 < m * k + c - m / 2 := by nlinarith
  have h := tel_lower hm hy
  unfold loF
  push_cast
  convert h using 2 <;> ring

theorem term_nonneg (m c : ℝ) (k : ℕ) : 0 ≤ 1 / (m * k + c) ^ 2 := by positivity

theorem upF_nonneg {m c : ℝ} (hm : 0 < m) (hc : m / 2 < c) (k : ℕ) : 0 ≤ upF m c k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hy : 0 < m * k + c - m / 2 := by nlinarith
  unfold upF
  positivity

theorem sum_range_le {m c : ℝ} (hm : 0 < m) (hc : m / 2 < c) (n : ℕ) :
    ∑ k ∈ range n, 1 / (m * k + c) ^ 2 ≤ upF m c 0 := by
  calc ∑ k ∈ range n, 1 / (m * k + c) ^ 2
      ≤ ∑ k ∈ range n, (upF m c k - upF m c (k + 1)) := sum_le_sum fun k _ => term_le hm hc k
    _ = upF m c 0 - upF m c n := sum_range_sub' _ _
    _ ≤ upF m c 0 := by linarith [upF_nonneg hm hc n]

theorem summable_sq {m c : ℝ} (hm : 0 < m) (hc : m / 2 < c) :
    Summable (fun k : ℕ => 1 / (m * k + c) ^ 2) :=
  summable_of_sum_range_le (term_nonneg m c) (sum_range_le hm hc)

/-- Summability for `c ≥ 0`, by shifting the index once. -/
theorem summable_sq0 {m c : ℝ} (hm : 0 < m) (hc : 0 ≤ c) :
    Summable (fun k : ℕ => 1 / (m * k + c) ^ 2) := by
  refine (summable_nat_add_iff 1).1 ((summable_sq (m := m) (c := m + c) hm (by linarith)).congr
    fun k => ?_)
  push_cast
  ring_nf

theorem tsum_le {m c : ℝ} (hm : 0 < m) (hc : m / 2 < c) :
    ∑' k : ℕ, 1 / (m * k + c) ^ 2 ≤ 1 / (m * (c - m / 2)) := by
  have h := Real.tsum_le_of_sum_range_le (term_nonneg m c) (sum_range_le hm hc)
  simpa [upF] using h

theorem tendsto_loF {m c : ℝ} (hm : 0 < m) :
    Tendsto (loF m c) atTop (𝓝 0) := by
  have hX : Tendsto (fun k : ℕ => m * (k : ℝ) + c - m / 2) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => m * (k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hm
    have h2 := tendsto_atTop_add_const_right atTop (c - m / 2) h1
    refine h2.congr fun k => ?_
    ring
  have hA : Tendsto (fun k : ℕ => 1 / (m * (m * (k : ℝ) + c - m / 2))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hX.const_mul_atTop hm)
  have hB : Tendsto (fun k : ℕ => m / 12 / (m * (k : ℝ) + c - m / 2) ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hX)
  have h := hA.sub hB
  rw [sub_zero] at h
  exact h

theorem le_tsum {m c : ℝ} (hm : 0 < m) (hc : m / 2 < c) :
    1 / (m * (c - m / 2)) - m / 12 / (c - m / 2) ^ 3 ≤ ∑' k : ℕ, 1 / (m * k + c) ^ 2 := by
  have hs := summable_sq hm hc
  have hbound : ∀ n : ℕ, loF m c 0 - loF m c n ≤ ∑' k : ℕ, 1 / (m * k + c) ^ 2 := by
    intro n
    calc loF m c 0 - loF m c n = ∑ k ∈ range n, (loF m c k - loF m c (k + 1)) :=
          (sum_range_sub' _ _).symm
      _ ≤ ∑ k ∈ range n, 1 / (m * k + c) ^ 2 := sum_le_sum fun k _ => le_term hm hc k
      _ ≤ ∑' k : ℕ, 1 / (m * k + c) ^ 2 := hs.sum_le_tsum _ fun k _ => term_nonneg m c k
  have hlim : Tendsto (fun n => loF m c 0 - loF m c n) atTop (𝓝 (loF m c 0 - 0)) :=
    tendsto_const_nhds.sub (tendsto_loF hm)
  have h := le_of_tendsto' hlim hbound
  simpa [loF] using h

theorem tsum_split {m c : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (K : ℕ) (c' : ℝ)
    (hc' : c' = m * K + c) :
    ∑' k : ℕ, 1 / (m * k + c) ^ 2
      = ∑ k ∈ range K, 1 / (m * k + c) ^ 2 + ∑' k : ℕ, 1 / (m * k + c') ^ 2 := by
  rw [← (summable_sq0 hm hc).sum_add_tsum_nat_add K]
  congr 1
  refine tsum_congr fun k => ?_
  rw [hc']
  push_cast
  ring_nf

/-! ### Bounds for the two constants -/

theorem catalan_eq :
    ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)
      = ∑' k : ℕ, 1 / ((4 : ℝ) * k + 1) ^ 2 - ∑' k : ℕ, 1 / ((4 : ℝ) * k + 3) ^ 2 := by
  have ev : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k) = 1 := fun k => by rw [pow_mul, neg_one_sq, one_pow]
  have od : ∀ k : ℕ, (-1 : ℝ) ^ (2 * k + 1) = -1 := fun k => by rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  have e1 : ∀ k : ℕ, 1 / ((4 : ℝ) * k + 1) ^ 2 = (-1 : ℝ) ^ (2 * k) / (2 * ((2 * k : ℕ) : ℝ) + 1) ^ 2 :=
    fun k => by rw [ev]; push_cast; ring
  have e3 : ∀ k : ℕ, -(1 / ((4 : ℝ) * k + 3) ^ 2)
      = (-1 : ℝ) ^ (2 * k + 1) / (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 :=
    fun k => by rw [od]; push_cast; ring
  have h1 := (summable_sq0 (m := 4) (c := 1) (by norm_num) (by norm_num)).congr e1
  have h2 := (summable_sq0 (m := 4) (c := 3) (by norm_num) (by norm_num)).neg.congr e3
  rw [← tsum_even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / ((2 * n + 1) ^ 2 : ℝ)) h1 h2,
    sub_eq_add_neg, ← tsum_neg]
  congr 1
  · exact (tsum_congr e1).symm
  · exact (tsum_congr e3).symm

theorem lchi3_eq :
    ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))
      = ∑' k : ℕ, 1 / ((3 : ℝ) * k + 1) ^ 2 - ∑' k : ℕ, 1 / ((3 : ℝ) * k + 2) ^ 2 :=
  (summable_sq0 (by norm_num) (by norm_num)).tsum_sub (summable_sq0 (by norm_num) (by norm_num))

theorem catalan_bounds :
    (0.91596551 : ℝ) ≤ ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) ∧
      ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) ≤ 0.91596568 := by
  rw [catalan_eq, tsum_split (m := 4) (c := 1) (by norm_num) (by norm_num) 40 161 (by norm_num),
    tsum_split (m := 4) (c := 3) (by norm_num) (by norm_num) 40 163 (by norm_num)]
  have u1 := tsum_le (m := 4) (c := 161) (by norm_num) (by norm_num)
  have l1 := le_tsum (m := 4) (c := 161) (by norm_num) (by norm_num)
  have u3 := tsum_le (m := 4) (c := 163) (by norm_num) (by norm_num)
  have l3 := le_tsum (m := 4) (c := 163) (by norm_num) (by norm_num)
  generalize (∑' k : ℕ, 1 / ((4 : ℝ) * k + 161) ^ 2) = T1 at *
  generalize (∑' k : ℕ, 1 / ((4 : ℝ) * k + 163) ^ 2) = T3 at *
  norm_num [Finset.sum_range_succ] at u1 l1 u3 l3 ⊢
  constructor <;> linarith

theorem lchi3_bounds :
    (0.78130225 : ℝ) ≤ ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ)) ∧
      ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ)) ≤ 0.78130260 := by
  rw [lchi3_eq, tsum_split (m := 3) (c := 1) (by norm_num) (by norm_num) 40 121 (by norm_num),
    tsum_split (m := 3) (c := 2) (by norm_num) (by norm_num) 40 122 (by norm_num)]
  have u1 := tsum_le (m := 3) (c := 121) (by norm_num) (by norm_num)
  have l1 := le_tsum (m := 3) (c := 121) (by norm_num) (by norm_num)
  have u2 := tsum_le (m := 3) (c := 122) (by norm_num) (by norm_num)
  have l2 := le_tsum (m := 3) (c := 122) (by norm_num) (by norm_num)
  generalize (∑' k : ℕ, 1 / ((3 : ℝ) * k + 121) ^ 2) = T1 at *
  generalize (∑' k : ℕ, 1 / ((3 : ℝ) * k + 122) ^ 2) = T2 at *
  norm_num [Finset.sum_range_succ] at u1 l1 u2 l2 ⊢
  constructor <;> linarith

/-! ### The ratio and the Farey argument -/

theorem ratio_mem (q : ℚ)
    (h : ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) =
      (q : ℝ) * (Real.sqrt 3 * ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ)))) :
    (664 / 981 : ℚ) < q ∧ q < 509 / 752 := by
  obtain ⟨hG1, hG2⟩ := catalan_bounds
  obtain ⟨hL1, hL2⟩ := lchi3_bounds
  generalize ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) = G at *
  generalize ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ)) = L at *
  have hs1 : (1.7320508 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs2 : Real.sqrt 3 < 1.7320509 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  generalize Real.sqrt 3 = s at *
  have hsL1 : (1.7320508 : ℝ) * 0.78130225 ≤ s * L :=
    mul_le_mul hs1.le hL1 (by norm_num) (by linarith)
  have hsL2 : s * L ≤ (1.7320509 : ℝ) * 0.78130260 :=
    mul_le_mul hs2.le hL2 (by linarith) (by norm_num)
  constructor
  · by_contra hq
    have hq' : (q : ℝ) ≤ 664 / 981 := by
      have h0 : (q : ℝ) ≤ ((664 / 981 : ℚ) : ℝ) := Rat.cast_le.2 (not_lt.1 hq)
      push_cast at h0
      exact h0
    have : G ≤ 664 / 981 * (s * L) := by
      rw [h]
      exact mul_le_mul_of_nonneg_right hq' (by nlinarith)
    nlinarith
  · by_contra hq
    have hq' : (509 / 752 : ℝ) ≤ q := by
      have h0 : ((509 / 752 : ℚ) : ℝ) ≤ (q : ℝ) := Rat.cast_le.2 (not_lt.1 hq)
      push_cast at h0
      exact h0
    have : 509 / 752 * (s * L) ≤ G := by
      rw [h]
      exact mul_le_mul_of_nonneg_right hq' (by nlinarith)
    nlinarith

/-- A fraction strictly between Farey neighbours `a/b < c/d` (`bc - ad = 1`) has denominator
at least `b + d`. -/
theorem add_le_den_of_farey {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d) (hdet : b * c - a * d = 1)
    (q : ℚ) (h1 : (a : ℚ) / b < q) (h2 : q < (c : ℚ) / d) : b + d ≤ (q.den : ℤ) := by
  have hD : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hq := Rat.num_div_den q
  rw [← hq] at h1 h2
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hDQ : (0 : ℚ) < (q.den : ℤ) := by exact_mod_cast hD
  have e1 : a * (q.den : ℤ) < q.num * b := by
    have := (div_lt_div_iff₀ hbQ (by exact_mod_cast q.den_pos)).1 h1
    exact_mod_cast this
  have e2 : q.num * d < c * (q.den : ℤ) := by
    have := (div_lt_div_iff₀ (by exact_mod_cast q.den_pos) hdQ).1 h2
    exact_mod_cast this
  have f1 : 1 ≤ q.num * b - a * q.den := by linarith
  have f2 : 1 ≤ c * q.den - q.num * d := by linarith
  have key : b * (c * q.den - q.num * d) + d * (q.num * b - a * q.den) = (q.den : ℤ) := by
    linear_combination (q.den : ℤ) * hdet
  nlinarith [mul_le_mul_of_nonneg_left f2 hb.le, mul_le_mul_of_nonneg_left f1 hd.le]

/-- **No rational of denominator below `1733`** is the ratio `G / (√3 L(2, χ₋₃))`. -/
theorem catalan_ne_rat_mul_sqrt_three_LChiMinusThree_of_den_lt (q : ℚ) (hq : q.den < 1733) :
    (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ≠
      (q : ℝ) * (Real.sqrt 3 *
        ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))) := by
  intro h
  obtain ⟨h1, h2⟩ := ratio_mem q h
  have := add_le_den_of_farey (a := 664) (b := 981) (c := 509) (d := 752) (by norm_num)
    (by norm_num) (by norm_num) q (by push_cast; exact h1) (by push_cast; exact h2)
  omega

end CatalanEisensteinRatio
