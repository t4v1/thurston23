import Mathlib
import CatalanEisensteinRatio

/-!
# No small polynomial relation for Catalan's constant

For each degree `d ≤ 10` this file proves that Catalan's constant
`G = ∑ (-1)ⁿ/(2n+1)²` is not a root of any nonzero integer polynomial of degree at most `d`
whose coefficients are bounded by an explicit `H(d)` (`catalan_aeval_ne_zero_deg_d`).
It is the finite shadow of the transcendence of `G`, which is open.

* **Enclosure.** `300` terms of each of `∑ 1/(4k+1)²`, `∑ 1/(4k+3)²` and Euler–Maclaurin
  telescoping brackets of orders `8` and `9` for the tails (`CatalanTail`) give
  `G` to `46` decimals (`catalan_mem`).
* **Lattice certificates.** With `X i = round (10^39 G^i)`, a relation `∑ mᵢ G^i = 0` of height
  `H` yields a vector `(m, m·X)` of squared length at most `(d+1) H² (1 + (d+1)/4)` in the
  lattice `{(m, m·X)}`. An LLL-reduced basis, given by a unimodular `U` with inverse `V`,
  and integer Gram–Schmidt vectors `Y j` certify that every nonzero lattice vector has squared
  length at least `B` (`LatticeCert.pnorm2_latVec_ge`). All certificate checks are
  integer or rational computations done by `decide +kernel`.
-/

set_option autoImplicit false

namespace CatalanTail

open Finset Filter Topology

/-- Upper Euler–Maclaurin telescoping function for `∑ 1/(4k+c)²`, `y = c - 2`. -/
noncomputable def hiF (y : ℝ) : ℝ :=
  1 / (4 * y) - (1 / 3 : ℝ) / y ^ 3 + (28 / 15 : ℝ) / y ^ 5 - (496 / 21 : ℝ) / y ^ 7 + (8128 / 15 : ℝ) / y ^ 9 - (654080 / 33 : ℝ) / y ^ 11 + (1448424448 / 1365 : ℝ) / y ^ 13 - (234852352 / 3 : ℝ) / y ^ 15 + (1941802827776 / 255 : ℝ) / y ^ 17

/-- Lower Euler–Maclaurin telescoping function. -/
noncomputable def loF (y : ℝ) : ℝ :=
  1 / (4 * y) - (1 / 3 : ℝ) / y ^ 3 + (28 / 15 : ℝ) / y ^ 5 - (496 / 21 : ℝ) / y ^ 7 + (8128 / 15 : ℝ) / y ^ 9 - (654080 / 33 : ℝ) / y ^ 11 + (1448424448 / 1365 : ℝ) / y ^ 13 - (234852352 / 3 : ℝ) / y ^ 15

theorem hi_step {y : ℝ} (hy : 0 < y) : 1 / (y + 2) ^ 2 ≤ hiF y - hiF (y + 4) := by
  have hy2 : 0 < y + 2 := by linarith
  have hy4 : 0 < y + 4 := by linarith
  have key : hiF y - hiF (y + 4) - 1 / (y + 2) ^ 2 =
      (133573113923501098465755136 * y ^ 0 + 701258848098380766945214464 * y ^ 1 + 1735077300083530403988635648 * y ^ 2 + 2689298037490263075929980928 * y ^ 3 + 2927037007085817472839843840 * y ^ 4 + 2376170909241159400812445696 * y ^ 5 + 1491187639496785771160928256 * y ^ 6 + 739598499339074142820368384 * y ^ 7 + 293765028965617491872055296 * y ^ 8 + 94047364873088627044777984 * y ^ 9 + 24279094852948979135545344 * y ^ 10 + 5024431879538339339042816 * y ^ 11 + 821892804518828174213120 * y ^ 12 + 103508358179806550949888 * y ^ 13 + 9559315567278655799296 * y ^ 14 + 586258848942842183680 * y ^ 15 + 18320589029463818240 * y ^ 16) / (255255 * y ^ 17 * (y + 2) ^ 2 * (y + 4) ^ 17) := by
    unfold hiF
    field_simp
    ring
  have hN : 0 ≤ (133573113923501098465755136 * y ^ 0 + 701258848098380766945214464 * y ^ 1 + 1735077300083530403988635648 * y ^ 2 + 2689298037490263075929980928 * y ^ 3 + 2927037007085817472839843840 * y ^ 4 + 2376170909241159400812445696 * y ^ 5 + 1491187639496785771160928256 * y ^ 6 + 739598499339074142820368384 * y ^ 7 + 293765028965617491872055296 * y ^ 8 + 94047364873088627044777984 * y ^ 9 + 24279094852948979135545344 * y ^ 10 + 5024431879538339339042816 * y ^ 11 + 821892804518828174213120 * y ^ 12 + 103508358179806550949888 * y ^ 13 + 9559315567278655799296 * y ^ 14 + 586258848942842183680 * y ^ 15 + 18320589029463818240 * y ^ 16) / (255255 * y ^ 17 * (y + 2) ^ 2 * (y + 4) ^ 17) := by positivity
  linarith

theorem lo_step {y : ℝ} (hy : 0 < y) : loF y - loF (y + 4) ≤ 1 / (y + 2) ^ 2 := by
  have hy2 : 0 < y + 2 := by linarith
  have hy4 : 0 < y + 4 := by linarith
  have key : 1 / (y + 2) ^ 2 - (loF y - loF (y + 4)) =
      (5048459271999544360960 * y ^ 0 + 23980181541997835714560 * y ^ 1 + 53255920768511431933952 * y ^ 2 + 73429790789945505349632 * y ^ 3 + 70371044483326497783808 * y ^ 4 + 49702936267717817139200 * y ^ 5 + 26753495397870382088192 * y ^ 6 + 11184302765515594530816 * y ^ 7 + 3662874658530857582592 * y ^ 8 + 939476707338014949376 * y ^ 9 + 186811664589339492352 * y ^ 10 + 28125089876878032896 * y ^ 11 + 3058606866309316608 * y ^ 12 + 217699398627622912 * y ^ 13 + 7774978522415104 * y ^ 14) / (15015 * y ^ 15 * (y + 2) ^ 2 * (y + 4) ^ 15) := by
    unfold loF
    field_simp
    ring
  have hN : 0 ≤ (5048459271999544360960 * y ^ 0 + 23980181541997835714560 * y ^ 1 + 53255920768511431933952 * y ^ 2 + 73429790789945505349632 * y ^ 3 + 70371044483326497783808 * y ^ 4 + 49702936267717817139200 * y ^ 5 + 26753495397870382088192 * y ^ 6 + 11184302765515594530816 * y ^ 7 + 3662874658530857582592 * y ^ 8 + 939476707338014949376 * y ^ 9 + 186811664589339492352 * y ^ 10 + 28125089876878032896 * y ^ 11 + 3058606866309316608 * y ^ 12 + 217699398627622912 * y ^ 13 + 7774978522415104 * y ^ 14) / (15015 * y ^ 15 * (y + 2) ^ 2 * (y + 4) ^ 15) := by positivity
  linarith

theorem tendsto_hiF (c : ℝ) : Tendsto (fun k : ℕ => hiF (c - 2 + 4 * (k : ℝ))) atTop (𝓝 0) := by
  have hX : Tendsto (fun k : ℕ => c - 2 + 4 * (k : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => 4 * (k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    refine (tendsto_atTop_add_const_right atTop (c - 2) h1).congr fun k => ?_
    ring
  have h0 : Tendsto (fun k : ℕ => 1 / (4 * (c - 2 + 4 * (k : ℝ)))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hX.const_mul_atTop (by norm_num))
  have h1 : Tendsto (fun k : ℕ => (1 / 3 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hX)
  have h2 : Tendsto (fun k : ℕ => (28 / 15 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 5) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp hX)
  have h3 : Tendsto (fun k : ℕ => (496 / 21 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 7) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp hX)
  have h4 : Tendsto (fun k : ℕ => (8128 / 15 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 9) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp hX)
  have h5 : Tendsto (fun k : ℕ => (654080 / 33 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 11) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (11 : ℕ) ≠ 0)).comp hX)
  have h6 : Tendsto (fun k : ℕ => (1448424448 / 1365 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 13) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (13 : ℕ) ≠ 0)).comp hX)
  have h7 : Tendsto (fun k : ℕ => (234852352 / 3 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 15) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (15 : ℕ) ≠ 0)).comp hX)
  have h8 : Tendsto (fun k : ℕ => (1941802827776 / 255 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 17) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (17 : ℕ) ≠ 0)).comp hX)
  have h := ((((((((h0.sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7).add h8)
  simp only [sub_zero, add_zero] at h
  exact h

theorem tendsto_loF (c : ℝ) : Tendsto (fun k : ℕ => loF (c - 2 + 4 * (k : ℝ))) atTop (𝓝 0) := by
  have hX : Tendsto (fun k : ℕ => c - 2 + 4 * (k : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => 4 * (k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    refine (tendsto_atTop_add_const_right atTop (c - 2) h1).congr fun k => ?_
    ring
  have h0 : Tendsto (fun k : ℕ => 1 / (4 * (c - 2 + 4 * (k : ℝ)))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hX.const_mul_atTop (by norm_num))
  have h1 : Tendsto (fun k : ℕ => (1 / 3 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hX)
  have h2 : Tendsto (fun k : ℕ => (28 / 15 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 5) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp hX)
  have h3 : Tendsto (fun k : ℕ => (496 / 21 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 7) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp hX)
  have h4 : Tendsto (fun k : ℕ => (8128 / 15 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 9) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp hX)
  have h5 : Tendsto (fun k : ℕ => (654080 / 33 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 11) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (11 : ℕ) ≠ 0)).comp hX)
  have h6 : Tendsto (fun k : ℕ => (1448424448 / 1365 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 13) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (13 : ℕ) ≠ 0)).comp hX)
  have h7 : Tendsto (fun k : ℕ => (234852352 / 3 : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ 15) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (15 : ℕ) ≠ 0)).comp hX)
  have h := (((((((h0.sub h1).add h2).sub h3).add h4).sub h5).add h6).sub h7)
  simp only [sub_zero, add_zero] at h
  exact h

theorem tsum_le_hiF {c : ℝ} (hc : 2 < c) :
    ∑' k : ℕ, 1 / (4 * (k : ℝ) + c) ^ 2 ≤ hiF (c - 2) := by
  have hs := CatalanEisensteinRatio.summable_sq0 (m := 4) (c := c) (by norm_num) (by linarith)
  have hstep : ∀ k : ℕ, 1 / (4 * (k : ℝ) + c) ^ 2
      ≤ hiF (c - 2 + 4 * (k : ℝ)) - hiF (c - 2 + 4 * ((k + 1 : ℕ) : ℝ)) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h := hi_step (y := c - 2 + 4 * (k : ℝ)) (by linarith)
    have e1 : c - 2 + 4 * (k : ℝ) + 2 = 4 * (k : ℝ) + c := by ring
    have e2 : c - 2 + 4 * (k : ℝ) + 4 = c - 2 + 4 * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    exact h
  have hbound : ∀ n : ℕ, ∑ k ∈ range n, 1 / (4 * (k : ℝ) + c) ^ 2
      ≤ hiF (c - 2) - hiF (c - 2 + 4 * (n : ℝ)) := by
    intro n
    calc ∑ k ∈ range n, 1 / (4 * (k : ℝ) + c) ^ 2
        ≤ ∑ k ∈ range n, (hiF (c - 2 + 4 * (k : ℝ)) - hiF (c - 2 + 4 * ((k + 1 : ℕ) : ℝ))) :=
          sum_le_sum fun k _ => hstep k
      _ = hiF (c - 2 + 4 * ((0 : ℕ) : ℝ)) - hiF (c - 2 + 4 * (n : ℝ)) :=
          sum_range_sub' (fun k : ℕ => hiF (c - 2 + 4 * (k : ℝ))) n
      _ = hiF (c - 2) - hiF (c - 2 + 4 * (n : ℝ)) := by simp
  have hlim : Tendsto (fun n : ℕ => hiF (c - 2) - hiF (c - 2 + 4 * (n : ℝ))) atTop
      (𝓝 (hiF (c - 2) - 0)) := tendsto_const_nhds.sub (tendsto_hiF c)
  rw [sub_zero] at hlim
  exact le_of_tendsto_of_tendsto' hs.hasSum.tendsto_sum_nat hlim hbound

theorem loF_le_tsum {c : ℝ} (hc : 2 < c) :
    loF (c - 2) ≤ ∑' k : ℕ, 1 / (4 * (k : ℝ) + c) ^ 2 := by
  have hs := CatalanEisensteinRatio.summable_sq0 (m := 4) (c := c) (by norm_num) (by linarith)
  have hstep : ∀ k : ℕ, loF (c - 2 + 4 * (k : ℝ)) - loF (c - 2 + 4 * ((k + 1 : ℕ) : ℝ))
      ≤ 1 / (4 * (k : ℝ) + c) ^ 2 := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h := lo_step (y := c - 2 + 4 * (k : ℝ)) (by linarith)
    have e1 : c - 2 + 4 * (k : ℝ) + 2 = 4 * (k : ℝ) + c := by ring
    have e2 : c - 2 + 4 * (k : ℝ) + 4 = c - 2 + 4 * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    exact h
  have hbound : ∀ n : ℕ, loF (c - 2) - loF (c - 2 + 4 * (n : ℝ))
      ≤ ∑ k ∈ range n, 1 / (4 * (k : ℝ) + c) ^ 2 := by
    intro n
    calc loF (c - 2) - loF (c - 2 + 4 * (n : ℝ))
        = loF (c - 2 + 4 * ((0 : ℕ) : ℝ)) - loF (c - 2 + 4 * (n : ℝ)) := by simp
      _ = ∑ k ∈ range n, (loF (c - 2 + 4 * (k : ℝ)) - loF (c - 2 + 4 * ((k + 1 : ℕ) : ℝ))) :=
          (sum_range_sub' (fun k : ℕ => loF (c - 2 + 4 * (k : ℝ))) n).symm
      _ ≤ ∑ k ∈ range n, 1 / (4 * (k : ℝ) + c) ^ 2 := sum_le_sum fun k _ => hstep k
  have hlim : Tendsto (fun n : ℕ => loF (c - 2) - loF (c - 2 + 4 * (n : ℝ))) atTop
      (𝓝 (loF (c - 2) - 0)) := tendsto_const_nhds.sub (tendsto_loF c)
  rw [sub_zero] at hlim
  exact le_of_tendsto_of_tendsto' hlim hs.hasSum.tendsto_sum_nat hbound

/-- **Catalan's constant to 46 decimals.** -/
theorem catalan_mem :
    ((9159655941772190150546035149323841107741490261 / 10 ^ 46 : ℚ) : ℝ) ≤ ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) ∧
      ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) ≤ ((9159655941772190150546035149323841107741497127 / 10 ^ 46 : ℚ) : ℝ) := by
  rw [CatalanEisensteinRatio.catalan_eq,
    CatalanEisensteinRatio.tsum_split (m := 4) (c := 1) (by norm_num) (by norm_num) 300 1201
      (by norm_num),
    CatalanEisensteinRatio.tsum_split (m := 4) (c := 3) (by norm_num) (by norm_num) 300 1203
      (by norm_num)]
  have u1 := tsum_le_hiF (c := 1201) (by norm_num)
  have l1 := loF_le_tsum (c := 1201) (by norm_num)
  have u3 := tsum_le_hiF (c := 1203) (by norm_num)
  have l3 := loF_le_tsum (c := 1203) (by norm_num)
  generalize (∑' k : ℕ, 1 / ((4 : ℝ) * k + 1201) ^ 2) = T1 at *
  generalize (∑' k : ℕ, 1 / ((4 : ℝ) * k + 1203) ^ 2) = T3 at *
  norm_num [hiF, loF, Finset.sum_range_succ] at u1 l1 u3 l3 ⊢
  constructor <;> linarith

end CatalanTail

namespace LatticeCert

open Finset Matrix

variable {n : ℕ}

/-- The lattice vector `(m, m·X)`. -/
def latVec (X : Fin n → ℤ) (m : Fin n → ℤ) : (Fin n → ℤ) × ℤ := (m, m ⬝ᵥ X)

/-- Dot product of pairs. -/
def pdot (a b : (Fin n → ℤ) × ℤ) : ℤ := a.1 ⬝ᵥ b.1 + a.2 * b.2

/-- Squared Euclidean length of a pair. -/
def pnorm2 (a : (Fin n → ℤ) × ℤ) : ℤ := pdot a a

theorem pnorm2_nonneg (a : (Fin n → ℤ) × ℤ) : 0 ≤ pnorm2 a := by
  simp only [pnorm2, pdot, dotProduct]
  exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (mul_self_nonneg _)

/-- Cauchy–Schwarz for pairs. -/
theorem pdot_sq_le (a b : (Fin n → ℤ) × ℤ) : (pdot a b) ^ 2 ≤ pnorm2 a * pnorm2 b := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (Fin.cons a.2 a.1 : Fin (n + 1) → ℤ) (Fin.cons b.2 b.1 : Fin (n + 1) → ℤ)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at cs
  simp only [pnorm2, pdot, dotProduct]
  simp only [sq] at cs ⊢
  nlinarith [cs]

/-- Expansion of `pdot (latVec X (w ᵥ* U)) Z` along the rows of `U`. -/
theorem pdot_latVec_vecMul (X : Fin n → ℤ) (U : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ)
    (Z : (Fin n → ℤ) × ℤ) :
    pdot (latVec X (w ᵥ* U)) Z = ∑ k, w k * pdot (latVec X (U k)) Z := by
  simp only [pdot, latVec, ← Matrix.dotProduct_mulVec, mul_add, Finset.sum_add_distrib]
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, mul_assoc]

/-- **The certificate theorem.** If `V * U = 1` and each `Y j` is orthogonal to the rows
`C k = latVec X (U k)` with `k < j` but not to `C j`, then every nonzero lattice vector
`latVec X m` has squared length at least `B`, whenever `B ‖Y j‖² ≤ ⟨C j, Y j⟩²` for all `j`. -/
theorem pnorm2_latVec_ge (X : Fin n → ℤ) (U V : Matrix (Fin n) (Fin n) ℤ) (hVU : V * U = 1)
    (Y : Fin n → (Fin n → ℤ) × ℤ)
    (hY : ∀ j k : Fin n, k < j → pdot (latVec X (U k)) (Y j) = 0)
    (hY0 : ∀ j, pdot (latVec X (U j)) (Y j) ≠ 0)
    (B : ℤ) (hB : ∀ j, B * pnorm2 (Y j) ≤ (pdot (latVec X (U j)) (Y j)) ^ 2)
    (m : Fin n → ℤ) (hm : m ≠ 0) : B ≤ pnorm2 (latVec X m) := by
  set w : Fin n → ℤ := m ᵥ* V with hw
  have hwU : w ᵥ* U = m := by
    rw [hw, Matrix.vecMul_vecMul, hVU, Matrix.vecMul_one]
  have hw0 : w ≠ 0 := by
    intro h
    apply hm
    rw [← hwU, h, Matrix.zero_vecMul]
  set S : Finset (Fin n) := Finset.univ.filter fun k => w k ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hw0
    exact ⟨k, by simpa [hS] using hk⟩
  set j := S.max' hSne with hj
  have hjS : j ∈ S := Finset.max'_mem S hSne
  have hwj : w j ≠ 0 := by simpa [hS] using hjS
  have hgt : ∀ k, j < k → w k = 0 := by
    intro k hk
    by_contra hne
    have hkS : k ∈ S := by simp [hS, hne]
    exact absurd (Finset.le_max' S k hkS) (not_le.2 hk)
  have hexp : pdot (latVec X m) (Y j) = w j * pdot (latVec X (U j)) (Y j) := by
    rw [← hwU, pdot_latVec_vecMul]
    rw [Finset.sum_eq_single j]
    · intro k _ hkj
      rcases lt_or_gt_of_ne hkj with h | h
      · rw [hY j k h, mul_zero]
      · rw [hgt k h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  set p := pdot (latVec X (U j)) (Y j) with hp
  have hcs := pdot_sq_le (latVec X m) (Y j)
  rw [hexp, mul_pow] at hcs
  have hw1 : (1 : ℤ) ≤ (w j) ^ 2 := by
    have h1 := Int.one_le_abs hwj
    nlinarith [sq_abs (w j), abs_nonneg (w j)]
  have hp2 : p ^ 2 ≤ pnorm2 (latVec X m) * pnorm2 (Y j) := by
    nlinarith [sq_nonneg p]
  have hQ : 0 < pnorm2 (Y j) := by
    have hcs2 := pdot_sq_le (latVec X (U j)) (Y j)
    rw [← hp] at hcs2
    have hpne : p ≠ 0 := by rw [hp]; exact hY0 j
    have hp0 : 0 < p ^ 2 := lt_of_le_of_ne (sq_nonneg p) (Ne.symm (pow_ne_zero 2 hpne))
    rcases lt_or_ge 0 (pnorm2 (Y j)) with h | h
    · exact h
    · exfalso
      have hC := pnorm2_nonneg (latVec X (U j))
      have hCQ := mul_nonpos_of_nonneg_of_nonpos hC h
      linarith
  exact le_of_mul_le_mul_right ((hB j).trans hp2) hQ

/-- **No small relation.** If `|K θ^i - X i| ≤ 1/2`, every nonzero lattice vector has squared
length at least `B`, and `H² n (n+4) < 4B`, then no nonzero integer vector of height `≤ H`
is a linear relation among `1, θ, …, θ^(n-1)`. -/
theorem no_small_relation (θ : ℝ) (K : ℕ) (X : Fin n → ℤ)
    (hX : ∀ i : Fin n, |(K : ℝ) * θ ^ (i : ℕ) - X i| ≤ 1 / 2)
    (B : ℤ) (hlat : ∀ m : Fin n → ℤ, m ≠ 0 → B ≤ pnorm2 (latVec X m))
    (H : ℤ) (hH : H ^ 2 * n * (n + 4) < 4 * B)
    (m : Fin n → ℤ) (hm : m ≠ 0) (hmH : ∀ i, |m i| ≤ H) :
    ∑ i, (m i : ℝ) * θ ^ (i : ℕ) ≠ 0 := by
  intro h0
  have hSreal : ((m ⬝ᵥ X : ℤ) : ℝ) = ∑ i, (m i : ℝ) * ((X i : ℝ) - (K : ℝ) * θ ^ (i : ℕ)) := by
    have e : ∑ i, (m i : ℝ) * ((X i : ℝ) - (K : ℝ) * θ ^ (i : ℕ))
        = ∑ i, (m i : ℝ) * (X i : ℝ) - (K : ℝ) * ∑ i, (m i : ℝ) * θ ^ (i : ℕ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, h0, mul_zero, sub_zero]
    simp [dotProduct]
  set S : ℤ := m ⬝ᵥ X with hSdef
  set T : ℤ := ∑ i, |m i| with hT
  have hST : 2 * |(S : ℝ)| ≤ T := by
    rw [hSreal]
    calc 2 * |∑ i, (m i : ℝ) * ((X i : ℝ) - (K : ℝ) * θ ^ (i : ℕ))|
        ≤ 2 * ∑ i, |(m i : ℝ) * ((X i : ℝ) - (K : ℝ) * θ ^ (i : ℕ))| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
      _ ≤ 2 * ∑ i, |(m i : ℝ)| * (1 / 2) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_sub_comm]
          exact hX i
      _ = T := by
          rw [← Finset.sum_mul, hT]
          push_cast
          ring
  have hST' : 4 * S ^ 2 ≤ T ^ 2 := by
    have h1 : (0 : ℝ) ≤ 2 * |(S : ℝ)| := by positivity
    have h2 := mul_self_le_mul_self h1 hST
    have h3 : (4 * S ^ 2 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith [sq_abs (S : ℝ)]
    exact_mod_cast h3
  have hT2 : T ^ 2 ≤ n * ∑ i, (m i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => |m i|)
    simpa [hT, sq_abs] using h
  have hsum : ∑ i, (m i) ^ 2 ≤ n * H ^ 2 := by
    calc ∑ i, (m i) ^ 2 ≤ ∑ _i : Fin n, H ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hmH i
          nlinarith [abs_nonneg (m i), sq_abs (m i)]
      _ = n * H ^ 2 := by simp
  have hlatm := hlat m hm
  have hpn : pnorm2 (latVec X m) = ∑ i, (m i) ^ 2 + S ^ 2 := by
    rw [hSdef]
    simp only [pnorm2, pdot, latVec, dotProduct, sq]
  rw [hpn] at hlatm
  have hn4 : (0 : ℤ) ≤ n + 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hn4]

/-- **Polynomial form.** -/
theorem aeval_ne_zero_of_small (θ : ℝ) (d : ℕ) (K : ℕ) (X : Fin (d + 1) → ℤ)
    (hX : ∀ i : Fin (d + 1), |(K : ℝ) * θ ^ (i : ℕ) - X i| ≤ 1 / 2)
    (B : ℤ) (hlat : ∀ m : Fin (d + 1) → ℤ, m ≠ 0 → B ≤ pnorm2 (latVec X m))
    (H : ℤ) (hH : H ^ 2 * (d + 1) * (d + 1 + 4) < 4 * B)
    (P : Polynomial ℤ) (hP : P ≠ 0) (hdeg : P.natDegree ≤ d)
    (hcoef : ∀ i, |P.coeff i| ≤ H) :
    Polynomial.aeval θ P ≠ 0 := by
  set m : Fin (d + 1) → ℤ := fun i => P.coeff i with hm
  have hm0 : m ≠ 0 := by
    intro h
    apply hP
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i ≤ d
    · have h' := congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
      simpa [hm] using h'
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hev : Polynomial.aeval θ P = ∑ i : Fin (d + 1), (m i : ℝ) * θ ^ (i : ℕ) := by
    rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hm, zsmul_eq_mul]
  rw [hev]
  have hH' : H ^ 2 * ((d + 1 : ℕ) : ℤ) * (((d + 1 : ℕ) : ℤ) + 4) < 4 * B := by
    push_cast
    linarith
  exact no_small_relation θ K X hX B hlat H hH' m hm0 fun i => hcoef i

end LatticeCert


namespace CatalanLattice

open LatticeCert Polynomial

/-- `|K θ^i - X i| ≤ 1/2` from a rational enclosure of `θ` and rational checks. -/
theorem close_of_rat {θ : ℝ} {lo hi : ℚ} (h0 : 0 ≤ lo) (hlo : (lo : ℝ) ≤ θ) (hhi : θ ≤ hi)
    (K : ℕ) {n : ℕ} (X : Fin n → ℤ)
    (hc : ∀ i : Fin n, ((X i : ℚ) - 1 / 2 ≤ K * lo ^ (i : ℕ)) ∧ (K * hi ^ (i : ℕ) ≤ (X i : ℚ) + 1 / 2)) :
    ∀ i : Fin n, |(K : ℝ) * θ ^ (i : ℕ) - X i| ≤ 1 / 2 := by
  intro i
  obtain ⟨h1, h2⟩ := hc i
  have h1' := (Rat.cast_le (K := ℝ)).2 h1
  have h2' := (Rat.cast_le (K := ℝ)).2 h2
  push_cast at h1' h2'
  have h0' : (0 : ℝ) ≤ lo := by exact_mod_cast h0
  have a := pow_le_pow_left₀ h0' hlo (i : ℕ)
  have b := pow_le_pow_left₀ (h0'.trans hlo) hhi (i : ℕ)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have a' := mul_le_mul_of_nonneg_left a hK
  have b' := mul_le_mul_of_nonneg_left b hK
  rw [abs_le]
  constructor <;> linarith

theorem catalan_close_lo :
    (0 : ℚ) ≤ 9159655941772190150546035149323841107741490261 / 10 ^ 46 := by norm_num


/-! ### Degree 1 -/

/-- `round (10^39 G^i)`, `i ≤ 1`. -/
def X1 : Fin 2 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U1 : Matrix (Fin 2) (Fin 2) ℤ := !![-10635848543770381642, 11611624510115148477; 31140689158553160555, -33997662528498999808]

/-- The inverse of `U1`. -/
def V1 : Matrix (Fin 2) (Fin 2) ℤ := !![-33997662528498999808, -11611624510115148477; -31140689158553160555, -10635848543770381642]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y1 : Fin 2 → (Fin 2 → ℤ) × ℤ := ![(![-10635848543770381642, 11611624510115148477], -18755740925374608802), (![17179613380944737157255764445587390261565843124180768284271, -18755740925374608802000000000000000000010635848543770381642], -21353695841088695700518151483547664463584580092514784010908)]

theorem lattice1 (m : Fin 2 → ℤ) (hm : m ≠ 0) : 599728915669701396536704360252621910897 ≤ pnorm2 (latVec X1 m) :=
  pnorm2_latVec_ge X1 U1 V1 (by decide +kernel) Y1 (by decide +kernel)
    (by decide +kernel) 599728915669701396536704360252621910897 (by decide +kernel) m hm

theorem close1 : ∀ i : Fin 2,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X1 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X1
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 1` with
coefficients bounded by `14100000000000000000`.** -/
theorem catalan_aeval_ne_zero_deg1 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 1)
    (hcoef : ∀ i, |P.coeff i| ≤ 14100000000000000000) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 1 (10 ^ 39) X1 close1 599728915669701396536704360252621910897 lattice1 14100000000000000000 (by norm_num) P hP hdeg hcoef


/-! ### Degree 2 -/

/-- `round (10^39 G^i)`, `i ≤ 2`. -/
def X2 : Fin 3 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U2 : Matrix (Fin 3) (Fin 3) ℤ := !![7038704728936, -8515530636847, 907311953800; -2414832453382, -6681310243046, 10172531913969; 444482938029, -864738257137, 414291377906]

/-- The inverse of `U2`. -/
def V2 : Matrix (Fin 3) (Fin 3) ℤ := !![6028568291147064789705077, 2743323563531523061031782, -80562474517144851262140943; 5521961136838463076205193, 2512789997890517358227816, -73792454839483649254658584; 5057926413727754627483668, 2301629183460360647461669, -67591349742843241607945610]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y2 : Fin 3 → (Fin 3 → ℤ) × ℤ := ![(![7038704728936, -8515530636847, 907311953800], 2928730172422), (![-715621975425320518136169571401656671310, -396598990534824642970551866350184831020, 1285938076221657965533961549963119019141], 168350756363670590840163227982182490110), (![23440947822771277912237144578907836699057133129027604682979016089, -48426127178747085842617659993247468183011602561843871056251718384, 24929551601941011550749934920855911579313471922708706786212373870], -204862491507877722653053511443503405374847473645054711853411637916)]

theorem lattice2 (m : Fin 3 → ℤ) (hm : m ≠ 0) : 131458301692589253813579589 ≤ pnorm2 (latVec X2 m) :=
  pnorm2_latVec_ge X2 U2 V2 (by decide +kernel) Y2 (by decide +kernel)
    (by decide +kernel) 131458301692589253813579589 (by decide +kernel) m hm

theorem close2 : ∀ i : Fin 3,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X2 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X2
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 2` with
coefficients bounded by `5000000000000`.** -/
theorem catalan_aeval_ne_zero_deg2 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 2)
    (hcoef : ∀ i, |P.coeff i| ≤ 5000000000000) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 2 (10 ^ 39) X2 close2 131458301692589253813579589 lattice2 5000000000000 (by norm_num) P hP hdeg hcoef


/-! ### Degree 3 -/

/-- `round (10^39 G^i)`, `i ≤ 3`. -/
def X3 : Fin 4 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U3 : Matrix (Fin 4) (Fin 4) ℤ := !![43897929, -3111921433, 2511336275, 910256145; -203082214, 497450594, -3042310936, 2992772815; 5729868983, -2781028578, -1329427215, -2689906069; 539658767, -4552694644, 215308386, 4489084475]

/-- The inverse of `U3`. -/
def V3 : Matrix (Fin 4) (Fin 4) ℤ := !![-97824486756764724923853416470, -72821862074190099449982341393, -7830342472819560881082627980, 63692662770652372185820068507; -89603864137241493974379949347, -66702320163877025182852304604, -7172324295727283517833323775, 58340287699449836819113784996; -82074056655043211097178799398, -61097030321904716195863375920, -6569602285167545156759602015, 53437696287096471579321329521; -75177012070571391430237255346, -55962777681267020118154616803, -6017529660641506335310996814, 48947091231072090028243459662]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y3 : Fin 4 → (Fin 4 → ℤ) × ℤ := ![(![43897929, -3111921433, 2511336275, 910256145], -3867534347), (![-7148151499007400618288367236, 65032080771024751500288364496, -136405766703310069518833246554, 80709687430344571341827432085], -121985413392279071758219309271), (![3949031109834505700632540004554072924440216726465, -1614442192077037479214640331221820806502611536486, -1704558895376174653580103549248908790940885694615, -1353493794396568093365823653991735402488821146082], -81544223001729892706665502094993279512047151336), (![-162881650169300001009420888868218117871926869111065032246932725737, -106161712532397132501409106378670073934292399239828597624424454013288, -39399436547344237854452453659181635766799154812055147509731734288231, 169760738236616354358276499736998827583588523366056806833874414776700], 99789748388276426043969141694679951896825673319145440537137741557098)]

theorem lattice3 (m : Fin 4 → ℤ) (hm : m ≠ 0) : 31779180094201115589 ≤ pnorm2 (latVec X3 m) :=
  pnorm2_latVec_ge X3 U3 V3 (by decide +kernel) Y3 (by decide +kernel)
    (by decide +kernel) 31779180094201115589 (by decide +kernel) m hm

theorem close3 : ∀ i : Fin 4,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X3 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X3
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 3` with
coefficients bounded by `1990000000`.** -/
theorem catalan_aeval_ne_zero_deg3 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 3)
    (hcoef : ∀ i, |P.coeff i| ≤ 1990000000) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 3 (10 ^ 39) X3 close3 31779180094201115589 lattice3 1990000000 (by norm_num) P hP hdeg hcoef


/-! ### Degree 4 -/

/-- `round (10^39 G^i)`, `i ≤ 4`. -/
def X4 : Fin 5 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321, 703909203233587508430801242257830542837]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U4 : Matrix (Fin 5) (Fin 5) ℤ := !![-20071484, 21111341, -1353268, -9394117, 12912002; 56672412, -5763137, -11213829, -58435566, 4150846; -30868602, 36113793, -7468936, -19084073, 26597023; -3803120, -4124847, 63979670, -63746664, 4107682; -6449563, -27635339, -39066954, 10301379, 80440757]

/-- The inverse of `U4`. -/
def V4 : Matrix (Fin 5) (Fin 5) ℤ := !![-16823643785642324319140979810902, -838011403845842036346213528186, 9439176554267686298826056083675, 357671592948640194215562614410, -395543500269094881470605164605; -15409878876341749847843647085050, -767589613450942140846114769726, 8645960961073476087583695593498, 327614873155513634402302261127, -362304237246918482477521748396; -14114918861167347002955541084126, -703085676368854083161662985587, 7919402768942706087930390392324, 300083951951184285648262617307, -331858215942797812547110089996; -12928780041432384549118015113545, -644002289312689344447586081146, 7253900462783319292331302458044, 274866575352014555605758389067, -303970707948636654558774896300; -11842317692637184389169568102525, -589883939581786798529308407928, 6644323247495727044210493566431, 251768326011765355277390491624, -278426710118642884251208983406]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y4 : Fin 5 → (Fin 5 → ℤ) × ℤ := ![(![-20071484, 21111341, -1353268, -9394117, 12912002], -25069269), (![85548814033627615656176, 3377337576961070635416, -20299793897944222693943, -107266065955074633518417, 15373863846993281928552], -16440173460786481651419), (![-85737994673063919428553957891860639270, 120605866370496438025059874168121640263, -30871904304846790803585566266552712925, -83896581737368987647270965253190905002, 93253583737164795758450598775813377217], 251345305859442036319839478232084746799), (![-126432885922635852479528320120361459703739856020663690, -115589005853448140129603261918633007777743986557330687, 524075060312998502344769816251306100895031381004180797, -216104326249569609924994018616023970293638058656810026, -58690980620904074769262590742828910044324789461315585], 26348354455918664463537381686314180387766987978864301), (![-2894274153921649426560256867006551902627803842809263276061486509594135, -25314108257810404847158208084494699514022085934295458157673707355486168, -1186115342541637312428567139117605428559706216004240318566640677117512, 2466294312536495704245327885894808094335146880212643651656316240614686, 35773007922103027403376150166420860857083370989825326282164967438521920], -1435413602379913163495561360238500163827835786123109910791563454989666)]

theorem lattice4 (m : Fin 5 → ℤ) (hm : m ≠ 0) : 1733822001112415 ≤ pnorm2 (latVec X4 m) :=
  pnorm2_latVec_ge X4 U4 V4 (by decide +kernel) Y4 (by decide +kernel)
    (by decide +kernel) 1733822001112415 (by decide +kernel) m hm

theorem close4 : ∀ i : Fin 5,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X4 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X4
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 4` with
coefficients bounded by `12400000`.** -/
theorem catalan_aeval_ne_zero_deg4 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 4)
    (hcoef : ∀ i, |P.coeff i| ≤ 12400000) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 4 (10 ^ 39) X4 close4 1733822001112415 lattice4 12400000 (by norm_num) P hP hdeg hcoef


/-! ### Degree 5 -/

/-- `round (10^39 G^i)`, `i ≤ 5`. -/
def X5 : Fin 6 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321, 703909203233587508430801242257830542837, 644756611586665798595725977610850243444]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U5 : Matrix (Fin 6) (Fin 6) ℤ := !![-291322, 987572, -1198285, 1865824, -50499, -1560628; -655231, 66145, -366010, -1596850, 2217795, 880579; -2223128, 1237696, 795602, 1990727, -298063, -1392937; -922461, 2927058, -604834, -950216, -1487, -806343; -750205, -564411, -1366770, 1587611, 599017, 1197633; 1763625, -1524778, 382407, -1246654, 3085593, -2949571]

/-- The inverse of `U5`. -/
def V5 : Matrix (Fin 6) (Fin 6) ℤ := !![-132004980043421390777667572561462, -112892953616060393697755902422753, 12464337683298122528066471416059, 95226511753088982450331536290489, 126648380654594847206753528733895, 55645555084231204196655864208094; -120912019979824412541570132038296, -103406061337355984499682104859827, 11416904472107666328047259036680, 87224208419342079764941556068919, 116005559237868579328941037548630, 50969413926049005449519320410908; -110751250223987645138427359237160, -94716394414397229072588256680824, 10457491688458647585643025198034, 79894373891460257486083331470837, 106257100995174871507963130463416, 46686229511638098683562998076553; -101444334717284703908641855718504, -86756958488107186207070198459797, 9578702588022354457190523644400, 73180497652908288525082082825310, 97327848648594121095587546207277, 42762979954521608584386066685060; -92919520325230370964259975053259, -79466389030567423482223140964258, 8773762007484761423809368845796, 67030818014830722041654325067943, 89148960717399956869115151453122, 39169418342831891381172755980545; -85111083645361815798502279226043, -72788478245501729400887175594533, 8036464130355289404797784569431, 61397923051139458671225470827891, 81657380773794808640672600280285, 35877839545968074770077771868871]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y5 : Fin 6 → (Fin 6 → ℤ) × ℤ := ![(![-291322, 987572, -1198285, 1865824, -50499, -1560628], -1590413), (![-2535183953846199403, 731877835365269077, -1930541483748996370, -4898955323274476506, 8066079519013251951, 2437390967170179871], -6021770532404408417), (![-18363648371350662389333957144184, 6442780193250128944168245124946, 9159767558592640228413162761067, 4038899427492033733545307428487, 4845812464333003079982488360922, -2694904880803719244292152942423], 7691928347531328590268804749763), (![18128788052430666118534707749923823863540469, 128179214554576142434889003068555082453788038, -51412552944160073005500423694074523118927749, -78518016818722469673593017443110455854065487, -24727741313494606504785881481543385884590931, -22730244012751517254830937092446916504527118], 45983754368658343745376810524953860588412936), (![-388338642253855531607681703138480313772527237153986001193, -1103792440325622552302487778914921224910389820619578810878, -6387472989295017518817625809031269446474681197113465114485, 3284874208448221835652330511198001621268759699193516981389, 3202464880993206051775377901512097119261753326061889874711, 3070594770454147212839443117831193723607118136233721009816], 4937264621637842713112439354985501924846931894544026657558), (![78974808674490398738018030763234853307465313711192506490583054112808254, -53959420361655006943252071336295154722280246774931656793599507006460010, 24100312550134156462929985422645566953153876225134975014675060178414843, -29325180942760270967395189771677806618969852176595531192373518074974517, 129007262606976822567955919465812412067741780994103643491499933479152676, -183081733860820618194947534371789376004047537811063949522506150445271517], 75022752623251029271463406800631189363589113401122221748046044089234137)]

theorem lattice5 (m : Fin 6 → ℤ) (hm : m ≠ 0) : 9393523363602 ≤ pnorm2 (latVec X5 m) :=
  pnorm2_latVec_ge X5 U5 V5 (by decide +kernel) Y5 (by decide +kernel)
    (by decide +kernel) 9393523363602 (by decide +kernel) m hm

theorem close5 : ∀ i : Fin 6,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X5 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X5
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 5` with
coefficients bounded by `791000`.** -/
theorem catalan_aeval_ne_zero_deg5 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 5)
    (hcoef : ∀ i, |P.coeff i| ≤ 791000) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 5 (10 ^ 39) X5 close5 9393523363602 lattice5 791000 (by norm_num) P hP hdeg hcoef


/-! ### Degree 6 -/

/-- `round (10^39 G^i)`, `i ≤ 6`. -/
def X6 : Fin 7 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321, 703909203233587508430801242257830542837, 644756611586665798595725977610850243444, 590574872831670752345550988173401973150]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U6 : Matrix (Fin 7) (Fin 7) ℤ := !![135290, -40257, 141519, 71950, -205227, -159060, -43053; 277500, -59984, -28557, -249267, 58831, -74516, -687; -170722, 8280, 41384, -43042, 291413, -19043, -53094; 18850, 119688, -336072, 61615, 125779, -72482, 108924; -236243, 226407, 192687, -118163, -27521, -194310, 173832; 11412, -112811, 120848, -29235, -299046, 391346, -48811; 142321, 298159, -149146, -192589, -157984, 131748, -196467]

/-- The inverse of `U6`. -/
def V6 : Matrix (Fin 7) (Fin 7) ℤ := !![-1342692172373036463946352065049200, -282256439502120291016467792213934, -1389175438135686729362622318543130, -1223896604700882147621922630847662, -205402221663826747811021556635044, -1016947954546144458079854198401943, 63006870498033184205335458948865; -1229859833464769318591755400179339, -258537187318905884821736827171672, -1272436905608352850543005293708174, -1121047180736324459484273810349542, -188141368011627914785101280525511, -931489337433166723821383176002768, 57712125572978056933685908561625; -1126509293114253055318717604252361, -236811168399468601912481787966132, -1165508426298576865240256861918128, -1026840647003843668108073306258915, -172331019940085589803163064369052, -853212184431714616399858217781273, 52862321391683122318980198621984; -1031843754013555777056889605629628, -216910882570820729252799591252793, -1067565618213131435070924573958294, -940550703358195673821803206840944, -157849285074586675292031805994881, -781513005472238454006753457298400, 48420067623120146325213335789989; -945133377243078835160572406700716, -198682905437486789301379367760037, -977853375809761080890701907679112, -861512083855290964398472228372615, -144584514193793013166342614567009, -715839024414603111116090676254238, 44351116010512369655187599737495; -865709655463178393846931241095522, -181986705531903805639409135479035, -895680048391787251584958739492727, -789115427779365721206553122538145, -132434440452342173615531173346377, -655683917333162727792102241059810, 40624096328991734011516943595945; -792960258951285755112414953153245, -166693560864884859990758095891255, -820412107717863690599696322997390, -722802581680337082643650134059322, -121305390938457128843272759217636, -600583908932516951877680409766135, 37210274531897495403856369577102]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y6 : Fin 7 → (Fin 7 → ℤ) × ℤ := ![(![135290, -40257, 141519, 71950, -205227, -159060, -43053], -217747), (![47582363643737890, -10503410851256775, -1818586529362920, -38910139388743069, 5455807606964910, -15207407822188272, -963694257918582], 23623773926897803), (![-1355138980267184488310548988, -596222610996113549840416543, 1618995130718758151824110562, -3522998022132827163934591157, 8069169944871024982123247319, -2146150318953134321467324769, -1770988628837531923083491970], -6530947622165925880741445232), (![108726472130613819207725391086408995806, 122388019229884680994372502083930132901, -364203478944683643063807571767010108581, 83615741034180415095539568810332942771, 28060709962274485858153224671016727449, -116279461929830023847338146349292227575, 128174230281585753754771531233084517245], -130998906483819209409351138912236984062), (![-51995699352219380756171082860653489089707122195608, 85797499226235197078219967022801913979824767899313, 40060810253490099916170156965184339286099453544958, -65084974513768086262563517497426670888493864614745, -28366014979476813327551659827289506868923462639873, -59401945518779238546146049394121482578674978261769, 81414515287186342314000753302055624565340126702934], 10392153655557235454190014204797458480305592263500), (![5452905198356285350370762178394727366140409574234572244286994, 854052067683886259572807361048669813312067227253991897877039, -6253355490116895769659970357217705714644191794969392796969995, -28559904491956287854087025930635896747505252575499237964499629, -17955153672356510797641353912878166768026438227831735033438761, 42251851871180812681506486537303304023681263226897604665890665, 10762284092564091850501537500293538193218693783470023776582973], -26340466810361146273981066350656553742925167715999103499867520), (![448113331252503851969429369408159341699103237838924833275952992409979895, 7076868618747020163616474551522599838568040402673623747972862411643555099, -897643268980404471733752373984625197647305224075399400197885224477223028, -1303617984037383876340435765938410658848612356713774330292423214070389907, -1171445628370160538661399118871766084119041244602066774352309136265687053, 465921355434291040027230156998658767297837773095496911178012990705409879, -7875654986295962030463886669875864349326695652808936584780965899413195954], 276817849013164279677542601220869255778027053153776284785633393693997574)]

theorem lattice6 (m : Fin 7 → ℤ) (hm : m ≠ 0) : 156545939711 ≤ pnorm2 (latVec X6 m) :=
  pnorm2_latVec_ge X6 U6 V6 (by decide +kernel) Y6 (by decide +kernel)
    (by decide +kernel) 156545939711 (by decide +kernel) m hm

theorem close6 : ∀ i : Fin 7,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X6 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X6
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 6` with
coefficients bounded by `90100`.** -/
theorem catalan_aeval_ne_zero_deg6 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 6)
    (hcoef : ∀ i, |P.coeff i| ≤ 90100) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 6 (10 ^ 39) X6 close6 156545939711 lattice6 90100 (by norm_num) P hP hdeg hcoef


/-! ### Degree 7 -/

/-- `round (10^39 G^i)`, `i ≤ 7`. -/
def X7 : Fin 8 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321, 703909203233587508430801242257830542837, 644756611586665798595725977610850243444, 590574872831670752345550988173401973150, 540946264299396859963845919561879580314]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U7 : Matrix (Fin 8) (Fin 8) ℤ := !![12927, 15539, -36177, -2154, -34825, -15345, 56973, 10367; -3601, -38885, -26863, 20176, 27857, -27666, 39323, 39296; -19857, -9695, 38754, 32067, -46116, 12056, -26986, 22563; 21208, 7059, -44177, -8908, -10645, 63674, 8717, -41544; 14823, -6686, 11467, -57703, -8236, -19948, 32073, 47587; 21435, -8375, -9633, -3151, 37684, 16074, -39154, -31476; 37386, -17775, 55172, 7650, -23348, -40300, -12, -57024; -75452, 7094, 17767, -24323, 33400, 54264, 47208, -25211]

/-- The inverse of `U7`. -/
def V7 : Matrix (Fin 8) (Fin 8) ℤ := !![8188118565604359525844770422267880, -573380290879036572067780725554957, 4813829194475433838420483490180524, -3714325704406778616119524194967593, 1149404722753278565939313462608460, 10867128812950300661598512557005616, -336640702750986204998564917322418, 2265543766489668773135758203449048; 7500034887137315449426681020867416, -525196618824523406283093505270474, 4409301918385334342702550002695430, -3402194550804672535667383658976942, 1052815179826808489963517077148944, 9953916100154398902682229501406518, -308351301319543647116135614810735, 2075160142207204187508941765997446; 6869773911746602900773126321372232, -481062033021470991101087152036969, 4038768851580574435156763504334983, -3116293153234298624425804564746973, 964342481748858324837118238477562, 9117444675068110689813799266361050, -282439182928474494450312335682121, 1900775292669704091173446914829569; 6292476542936135269776323408236066, -440636270912612630789906248058810, 3699373310882445339269900936194105, -2854417309732653763933152013239284, 883304534285426999122120599359624, 8351265629176683563583456555229203, -258704574010008393634441279540234, 1741044770347582878882967151824959; 5763692015496710141638358755051462, -403607663702505276381845816411172, 3388498672785785003830760866980175, -2614548047139009210262997391674535, 809076562586182866353859307298599, 7649471984160607760529813131775716, -236964488849441670016531292203850, 1594737107560563577487234073245964; 5279343581628937131996012960331311, -369690733497744437399079209249972, 3103748200186949593095063215253932, -2394836055502570201576929595737743, 741086294384114916897722958953914, 7006653151113661569495426606790361, -217051318827879829161859704948707, 1460724322283171247700769766830853; 4835697080612436957368507466963488, -338623992370073408927727590358203, 2842926564360713394102007460365844, -2193587430535439170187529341265163, 678809547972139267181702241106669, 6417853216753508951287447858524342, -198811540217127952417840929579152, 1337973221789220513765283555670201; 4429332149704214175172155350954798, -310167926373916368233772890604347, 2604022919726860719900974875535238, -2009250614190072681447336440816157, 621766190941469998816095754868106, 5878532735025804203988399940572971, -182104530564269679249179514020913, 1225537437089371407222923366510263]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y7 : Fin 8 → (Fin 8 → ℤ) × ℤ := ![(![12927, 15539, -36177, -2154, -34825, -15345, 56973, 10367], 24005), (![-13317026209690, -77344303414746, -28299885322168, 36965704397158, 68102030561104, -40885489896147, 39274960903424, 64195220644159], -30370228018700), (![-241186776215470886180337, -230875026795823309700369, 355857751327717461434667, 446590820427935488268934, -483211038505103920473705, 46550882436951717996584, -162887826718470149515159, 401552592463829537220996], 397626423458277746188643), (![2045484374869851991511199759595139, -8059958562008361035923180772574397, -10443383865675289839151321916335777, 6400971405987098696047377406858894, -2907752666018907865087572389048753, 19818067921427387751428133983511513, 843581835086503553106221559307213, -3788218874124499821189020130119431], -2964550855283202795984606414549407), (![24149572350297539888196510379186991579751960, -32088648164710634058576709233826754375106328, 29795884099126332918032387110502944578394358, -92500918943507526444809530377471959583906872, -18799603672659590582878061238968693741569661, 36909591684314322471877279126396822599350755, 11181600077796254961473343929241559058615202, 63151997572222566760956022360318302304262507], -13119844693154091594816846772187068520963903), (![218788349232000153974098325882490751815841366163056200, -153499756515061722028913521368963457700926684117993312, -111791574721618961225433321765843181776621457627573058, -107655780193194440200043415475852044850883447675874228, 280862490664289470965211030972388642295878837026057131, 17830872117176469365989242897355630178531975905143075, -146442522086469765124801297998292721167067553810240282, -45062237824007389022005793730370659759330784979960317], 589288164011714576253769666808761157032683051282985013), (![2506363686020874898195182340505038631449184890746319755382092228, -2629510537648906180331771380803573391160239114440101924537568114, 2067870456174851691873476425974046152846896881797604807561943803, 461579819285081220167989683076478081589574711789585435099437912, -1078077244484285159044228311198764042267412896916267802923532573, -1156891112320213884963562013319501801008912316521198138896033507, 1179683568743777358409597570559486988193020646281551629204197653, -2549938928158424923269262523440646245772062066526377909960668175], -491882355860344555603573756652917786338885087708931821633933223), (![-27622753589748535946972073590065604073028563038592033668402629518806924088, -3050141945055808268590283871436220891122535947127629954902391997260264716, 15417608677227672722019168552327548750473408557908968100973317219338500661, -6503160486554524466408577166553412737118912474367026633103270853348039664, 11119318647429659628938712175178836611323981518925704373461049869227984971, 11469289156886147846061640624098729175184895219140184634523364745713592067, 24477768516347398170280030905990472121827850645003964267781332520794629069, -13308026248679738146628216666694612647563730922117504885234513889997395093], 10616514443419577751398160805325934000928165866196906047129296153724301685)]

theorem lattice7 (m : Fin 8 → ℤ) (hm : m ≠ 0) : 4777256942 ≤ pnorm2 (latVec X7 m) :=
  pnorm2_latVec_ge X7 U7 V7 (by decide +kernel) Y7 (by decide +kernel)
    (by decide +kernel) 4777256942 (by decide +kernel) m hm

theorem close7 : ∀ i : Fin 8,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X7 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X7
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 7` with
coefficients bounded by `14100`.** -/
theorem catalan_aeval_ne_zero_deg7 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 7)
    (hcoef : ∀ i, |P.coeff i| ≤ 14100) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 7 (10 ^ 39) X7 close7 4777256942 lattice7 14100 (by norm_num) P hP hdeg hcoef


/-! ### Degree 8 -/

/-- `round (10^39 G^i)`, `i ≤ 8`. -/
def X8 : Fin 9 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321, 703909203233587508430801242257830542837, 644756611586665798595725977610850243444, 590574872831670752345550988173401973150, 540946264299396859963845919561879580314, 495488166396944002835125290273148477265]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U8 : Matrix (Fin 9) (Fin 9) ℤ := !![3283, -10200, -155, 2681, 8792, -3025, 6190, -256, -7318; -1238, -3423, 3605, -8417, -7593, 3997, 15507, -2250, 5336; -10423, 2053, 6493, 11800, -5734, 2235, -4155, -7033, 5813; 2115, -2964, 2499, 7600, 4561, -17262, -7007, -5381, 15401; -899, -5190, -14308, 12349, -6245, 12617, -5, 9078, -968; 19571, -5566, 11651, -2837, -2222, -10297, -13644, -4405, -6910; -2165, 18250, -5926, 7531, 4212, -5583, 3526, -17356, -14987; 1598, 12328, -7188, -12024, 11368, -9241, 628, 4413, -4886; 9751, 427, -1423, 9773, -16639, -21274, 15350, 9996, -11105]

/-- The inverse of `U8`. -/
def V8 : Matrix (Fin 9) (Fin 9) ℤ := !![12581967613750739993062399837583729, 20187541107446966075365167184922116, 32903972876266657065942152902864281, -877249964165624994794383708439076, 19021481621666699641181405300688609, 16173968290005364755230576498019679, -3777457980995050102565667702974712, 31330993660860539616845683581157078, -2993177791622677505956948278023187; 11524649441247723033642783199865721, 18491093085459694256155775322369723, 30138907066400686706315367670163952, -803530784668910787344202871318913, 17423022715720990044725327692475760, 14814798474958262921090580214647929, -3460021544041609161058416723885901, 28698112224732806558564320231223690, -2741647874381722045728978855415282; 10556182373136625752485602112348874, 16937205065009354916286269415370012, 27606201918927689866087818854792871, -736006552618945896887817541539447, 15958889354168560709538978498259376, 13569845687730903415689454024848978, -3169260689454051306027476775777879, 26286483415691897833096087783687766, -2511255124282763552283515405909915; 9669099859653175293435211453404959, 15513897101072697190851772812823176, 25286331143646885204709780166494896, -674156679287939390425576352770811, 14617793569699500739149081832378185, 12429511768255610146531249235435268, -2902933750518282898068254178841465, 24077514400683842819857258973032231, -2300223292044247500805137540073812; 8856562798106085695229848565127886, 14210195976188288683511247602024543, 23161409330552437232403452451796989, -617504323312518283483051801213256, 13389395972629734574731790071594260, 11385005132142986124879785275329974, -2658987437650581862624746112546653, 22054174784332923481745412078507657, -2106925394437587942579732440529262; 8112306805735094194695715038897619, 13016050600704032634468836538674898, 21215054059441247666563151065072732, -565612714409952365135817865938234, 12264226037743858138252058087583642, 10428272990574038174719256836258175, -2435541008237376314987702064205984, 20200865310419747283835038124928065, -1929871170803096778948043863646904; 7430593923463043182623542484777821, 11922254522314617737584281817980889, 19432259597057924711748976486796484, -518081786028701705793426808893447, 11233609089785773498271769719062899, 9551939266053393545795455561117712, -2230871766753131467964165440473634, 18503297596952595663731142394927137, -1767695593650143866240631012110761; 6806168378194459422206266018437059, 10920374947463945294564211898863370, 17799281208025128567080402019058804, -474545090972174602833625792872756, 10289599424680234493494235406208172, 8749247725375305923481675455480189, -2043401783367214413631001915143956, 16948383977630593052365471191921270, -1619148344762205926649597275270096; 6234216062603087128449469538031641, 10002687727391829537535541312711890, 16303529187636145539238295978280451, -434666976216210361177302138025595, 9424919050872801923240982612163150, 8014009891377074027493353306596878, -1871685728644739521916040407488412, 15524136600414064793065128997606438, -1483084175671174615239968532472527]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y8 : Fin 9 → (Fin 9 → ℤ) × ℤ := ![(![3283, -10200, -155, 2681, 8792, -3025, 6190, -256, -7318], 1), (![-327234844799, -1167130688475, 1080884968090, -2492103335968, -2161397186701, 1159589640500, 4742767730605, -679416584482, 1503421265354], -418163409803), (![-1197836233488358704833, -463580182691193725713, 919665814474809108313, 1620339964125058617588, -307040416772965912596, 163801703851167069139, 114936077951839200199, -996952335352573666185, 378594835212082441789], 1277630643991372655465), (![340464933378875309590873172943, -187143690103224443277495860537, 52123433643120726471924103857, -53607085220171350817449429628, 175561720903518081093933481756, -979492601780690712654550516829, -69064059990542769972115991689, -178895319409483183913663161025, 956496234806905336130903337461], 32717673471067421008110546865), (![149746241406339748621918732080272167008, -224679297772253526312522474113281267689, -536904780093704745967409168166798930061, 241316886629629194326951390102875929264, -188258456183496381201644662243347263230, 183875073905217954059367406825653961139, 71797919464895360975915967671623307131, 332970571714591660634896073993774391718, 227055388608213404796935905359024348342], 256562252163902811043255256843869838006), (![25466768512564478424927131522934652255825284534, -12117065087910206067196337992718151019810778464, 14418364402361168243600290771885854349156017948, 575413254949814946417818244093023293146122962, -21060835514528008202609380460496270354597876168, 2042144027370775266189381429688473735667998381, -12091525444586205371711200228187165884720123253, -4234358168589921823423261468747529802304684024, -8006886117789019130992977174036828745733900135], 3204349788635213027373392077826661017182672473), (![22197759452801073167677067047983588751075116703953200268, 36413127551024159281997732237154795903274698822202060371, -30231335994246612283043641806826733977109731095405269393, 10084999772455036064817869164436230456742523531069257016, -11597535169137091149233300337426063045940293531409437266, -17987849821444347506417210431466692771328152176194776193, 24049941277491815859027807482636809102592996901883391483, -40439429954841658987185931329339464640462454701794869270, -21198482071531588317234833944925937201375677098427187282], 15076389442510876765459455199559656606762103352902604826), (![2656146532449472487284065845675632299844200392719192581249393838, 23784111145839995236286576833011216013471783718798182346979225060, 30198086734303098339827689026797105081546809042869977865211234316, -95534039875517974820939021761051590514158692729870972922942119094, 31866078775792620118426099006732273236965604383333500373629767172, -18876078901492343106711558556728260320066513545279886123901207205, -2091360174915993301893097417760539630300810165491935704459697583, 49918061315973872262972390969235082826103756880657849543763943460, -25003544525333860909243948834369036234083998073015052267917824377], 167170041060065697167565098750348539537976227652823857894292254135), (![-27565943830552415244377487874668995578544314676577598013579360495980128628, 23543111580432149174345303228257404957622923936839876984150516964672334278, 27680931937702729001748468301312925855170488617176057065319456596743250850, 40347409642142897836590180275802780089078202257153807927593565902229835741, -60178540522159637764057458708709926576694946374889421127917328124077433335, -84502348269680334985393804482455388529478975575291638531996422096570908860, 36212981006215027833392446982380898049375486334764303150708208349001066666, 87700249875285679231013516146911176361797135694726796169940822225607328722, -40794707341527901706623202949060918096790375305840841587654469488001626503], -14761114784236482865342572966079107850518026509742116311915742417648497389)]

theorem lattice8 (m : Fin 9 → ℤ) (hm : m ≠ 0) : 300414525 ≤ pnorm2 (latVec X8 m) :=
  pnorm2_latVec_ge X8 U8 V8 (by decide +kernel) Y8 (by decide +kernel)
    (by decide +kernel) 300414525 (by decide +kernel) m hm

theorem close8 : ∀ i : Fin 9,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X8 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X8
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 8` with
coefficients bounded by `3200`.** -/
theorem catalan_aeval_ne_zero_deg8 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 8)
    (hcoef : ∀ i, |P.coeff i| ≤ 3200) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 8 (10 ^ 39) X8 close8 300414525 lattice8 3200 (by norm_num) P hP hdeg hcoef


/-! ### Degree 9 -/

/-- `round (10^39 G^i)`, `i ≤ 9`. -/
def X9 : Fin 10 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321, 703909203233587508430801242257830542837, 644756611586665798595725977610850243444, 590574872831670752345550988173401973150, 540946264299396859963845919561879580314, 495488166396944002835125290273148477265, 453850112741557578161691131254740133413]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U9 : Matrix (Fin 10) (Fin 10) ℤ := !![-1780, 2974, 479, -421, 807, -4449, 4275, 1245, 580, -4864; -434, -1735, -1160, -435, 2299, -2727, 5345, 4459, -3888, -378; -3261, 5862, -693, -5143, -389, 3592, 364, 798, 377, -992; 456, -2603, 312, -2027, 6104, 3294, 1209, -3917, -3053, -614; -7059, 3090, 2320, 3111, -1912, 1550, 777, -888, 1151, -685; -1039, 577, 2836, -3582, -960, 5016, 5188, -3056, -2649, -3906; -515, -2549, 805, 4442, -4531, 667, 4368, 2213, 489, -5506; -744, -1928, 5496, 2626, -2547, -2323, -2653, 3525, -20, -2553; 3269, 2630, -1476, 1854, -1276, 951, -5417, -1800, -5059, 2424; 1993, -1381, -1980, -410, 4094, 7226, -5222, 3648, -3791, -7279]

/-- The inverse of `U9`. -/
def V9 : Matrix (Fin 10) (Fin 10) ℤ := !![4525399598007000827951247070209026, 9624646075091852407591630179377234, -76674735941497672410269171031871567, -79289114036397048625127052567392341, 27732211516374895488065003797529460, 58951603918199432947762366188871120, -66448883058273985411867122819820657, -29471104362193109183616005780545514, -20455052379506481644951106643433871, 33158111966702950688618869974946758; 4145110331677830589020155200063255, 8815844660916947492756931270560552, -70231420065035285942013638162354588, -72626100450133698957843807458874784, 25401751599444647082631272688781563, 53997640910633616192732735582431241, -60864890652884473269594049675856153, -26994517618175042483716981739107550, -18736124206720792122354200118891148, 30371689729375824392862851456745009; 3796778447885413482375822364013300, 8075010393010855702551999785913231, -64329564409779907408648043344612888, -66523009251581106934367975166315182, 23267130496927439634278000597131307, 49459981240876629909799112110348011, -55750145731400790344671166077465079, -24726049369659109808740183178952804, -17161645141587186626358458988135054, 27819422829133867178632312272487045; 3477718426976622141234777921780355, 7396431692621407280441400482279209, -58923667687765734342420177647681082, -60932787695581126230349362480325332, 21311891010417035369323000064065147, 45303641105293668556174633058203292, -51065215360329075295795645920849219, -22648210502535058208956415809235135, -15719476489172491349709984841289116, 25481634161354893868959705532661052; 3185470425346705157975707306536492, 6774876950123181076230451709470828, -53972052284725341740831707776018857, -55812337086457306082713086057753138, 19520958912396772323598117037939703, 41496576543401798318563013407735229, -46773980329311472658492913567739209, -20744981590005256656199929445942923, -14398499622559705748182113744179796, 23340300175211957315545686988606636; 2917781310886653377233594584130799, 6205554191097124947875951354661079, -49436542939942378720868497638804528, -51122180501816103128049588407506520, 17880526729102588636443649741772794, 38009436389897477400690402186621017, -42843356684371337388795199266961049, -19001689388284634580925236499167031, -13188530262038364597472955756390249, 21378911918262669566566303537483713; 2672587292105478457409938143546742, 5684074131847209766187614144419033, -45282172428051922698354475159911054, -46826158438981027456424705561035542, 16377947289624099022906829883603047, 34815335987213653366223195972389603, -39243040661946720041139555813653828, -17404893710911092632755439829870243, -12080239957792204622369157793612154, 19582347758073895290659261308119908; 2447998007003879373450080521595539, 5206416339524789829871952177232828, -41476911973695863634472425550210621, -42891150037597855246201392676553650, 15001636220543711585515070079484216, 31889649914007669962951825197995550, -35945275057240793632692051342697858, -15942283809506021365128587263089324, -11065084170742519862441110946482485, 17936756799609088177945091974536168; 2242281949029956326263410733782611, 4768898235966805769898599074030036, -37991424320622541596777406190899855, -39286817729132569177935187310996209, 13740982634380810980603214360314109, 29209822131587536686367687509413590, -32924635225669133782311213055933400, -14602583462116041540728306793762158, -10135236397075112945092944155499707, 16429452099566211794010538829530225; 2053853117756076668661728354755058, 4368146706278026859581471117888152, -34798837551477875562104161661197936, -35985373344597015974400104591469482, 12586267323279467760397324127200172, 26755192084570460112005673188735269, -30157833067548223598105344375631134, -13375464037399551945190725806634582, -9283527828573482303004367907695172, 15048812854385323647202580655716201]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y9 : Fin 10 → (Fin 10 → ℤ) × ℤ := ![(![-1780, 2974, 479, -421, 807, -4449, 4275, 1245, 580, -4864], -1904), (![6282211864, -50010886024, -22198443929, -3852408379, 30918116189, -10675841439, 54021884005, 62351027171, -66767786492, 30143890652], 14047908672), (![-13735642000610854865, 20832319074566795543, -6565026064119695897, -26259726799492260322, 265422865017975674, 23108782775561039727, 2074049874208717195, 9157588779903037055, -5987232726972653405, 4503363551056527302], -7032833603172910263), (![53673472492800918641376237, -205564451119559886510090979, 95766897726754304171004051, -121693280178819104837824068, 580234164431249421176626683, 211942517681054268157642352, 91508973361609637827521797, -509560769416747802096793259, -173659685102673223349060808, -197524345519406098563001922], -245605058678298191702575807), (![-102191490099019077952046871539099169, 4787533501235182089031865461114373, 36219534085042038918017787253409313, 57672208122686558528371776046080936, 5955128434881754651946114101923804, 32474856866851933776941743439723291, 27289163392106921685137042922974951, -21430999702292282916091395917166607, -14584583545533550556184070266546939, 1478164151321425563543100732316104], 65054629540862990088751873413403349), (![935865164082278942798985003260035971526141, -310767811606962197380745667442807907043321, 650746884353625359079352365111366766172827, -708998000742478249187269200768837944544769, -1255064099369237817635484714752481054832906, 672916477611041640852680770099397911837270, 1007219687241563462025007055408665441400673, -444941128286496278237683421521069399451395, -338890531519754652487481683404499287072890, -857060449219799911810751560750963673237184], 912598891814366399204123845511117788638063), (![-67156588933056728290117983333207030165861487322519, -200730105724465350633894920554123281771442772561205, -66060024175670316370965513846710284729213596093457, 267858535087253301046341736908386043272410628836760, -196829416698253505880764244883807513610256372910244, 293105800760923885779503422965212669580411193436137, 59100111472915071468970289988760332209665408806629, 149515916059492699514052378611224810736450156437031, 36258738003231037749904869564262651804964258054551, -184167979328866795353553764871801135235714342032520], -382925124106185508860456813236703959005329801070201), (![-7680369507242516758705313807263765563529670683636091711111, -9462721024933251258033565698541673985921565956428617833075, 60859036057395060318622932567516388024013770430193394104821, -13051730002752846097663890383911656230227057936648734936694, -1462143493131487885960124389141727750571812633564322212566, -8391349300117434554923712068708138449666344290152211827273, -29970216719108651613238989750444811664676241063253997928141, 23033115965789970463863428862759154139077525985477653920597, -20773013227375008935223564293101208331264597225330303623429, -5971012574335636424405144992541297504879859749322189943762], -13720296414093074439854759948905145829045620914933580272071), (![733313438628508005360444903746919311733404043670806994477943127029, 2011077962414160112141444145557318468553775557973670703884337337984, -429758237362152057470716762904063336800251196787730491727632539410, 1519978286946873900557147504597512082968999281804329899725520435649, -978445158737141287641337713515452748315797428657197629877269518451, -380918349253509161313636977895164652563651097588917763760812317559, -479092941780572557751635928656167823690815042061499761078962844076, -1122267167720723778119880326021734907933570361195671175069347570419, -3292304547777134312569219816797893805499991013910578433161651782600, 160288506368808980383168603164837126210702476998830278712620053267], -735053311410200186008157704432120062517513414740817744194142841333), (![58633801595160406343449249681258744021023763254645836622553676917134152254, 34388206738453406268475631617118060576659485671990404913260266256652785969, -105772466754746403902256497117538404750960254343368619400896605091876302395, 47818098308085016991134835063375114260798239329945679073249449738846673934, 120794543803032813600130958333475827663953302480344352061617874768023323494, 80323357527116991299112268560847494684238873605692384766586440028182401981, -179182499996977184988720448009280250179289822601717430331454045034004278096, 135534159343286551381446573456447660891576106173683952546815220984272860156, -46226903438442449786858997159701649245067382619677600957224968300733362105, -263404288557885309338554066174398861716316765637605417342022415490390227513], 170351998264192955884287429147502412296356346818569272782789392302530908702)]

theorem lattice9 (m : Fin 10 → ℤ) (hm : m ≠ 0) : 52463300 ≤ pnorm2 (latVec X9 m) :=
  pnorm2_latVec_ge X9 U9 V9 (by decide +kernel) Y9 (by decide +kernel)
    (by decide +kernel) 52463300 (by decide +kernel) m hm

theorem close9 : ∀ i : Fin 10,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X9 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X9
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 9` with
coefficients bounded by `1220`.** -/
theorem catalan_aeval_ne_zero_deg9 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 9)
    (hcoef : ∀ i, |P.coeff i| ≤ 1220) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 9 (10 ^ 39) X9 close9 52463300 lattice9 1220 (by norm_num) P hP hdeg hcoef


/-! ### Degree 10 -/

/-- `round (10^39 G^i)`, `i ≤ 10`. -/
def X10 : Fin 11 → ℤ := ![1000000000000000000000000000000000000000, 915965594177219015054603514932384110774, 838992969716425876816576281275981950990, 768488694016815547546147910885287020321, 703909203233587508430801242257830542837, 644756611586665798595725977610850243444, 590574872831670752345550988173401973150, 540946264299396859963845919561879580314, 495488166396944002835125290273148477265, 453850112741557578161691131254740133413, 415711088184718625528554440060028276027]

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U10 : Matrix (Fin 11) (Fin 11) ℤ := !![-1431, 248, 1111, 1029, -919, -771, -776, 851, 968, 388, -79; -2041, 288, -47, 905, -2059, -139, 1193, 451, 2397, 1540, -421; -1684, -166, 2740, -1617, -1200, 1466, -429, 217, 1640, 714, -773; -1513, -165, 1016, -1635, 1813, -756, -370, 935, 99, 2351, -298; -180, -305, -398, 1340, -15, 2963, -1855, -453, -1645, -573, 672; 1119, -199, -1615, -4, -1581, 1909, -1632, -511, 1595, 317, 1466; -144, -3010, 102, 798, 1062, 720, 1027, 375, -1259, 656, 1220; 1425, -753, 299, -191, -1775, -681, -804, 461, -1075, 2739, 876; -863, 1907, 338, -358, -2275, 725, -221, -1787, -49, 1016, 2170; -929, 1552, -219, -911, -751, -1014, -386, 1677, -446, -30, 2716; -1035, 605, -535, -1514, -1559, 2891, 402, 3337, -1039, -576, 145]

/-- The inverse of `U10`. -/
def V10 : Matrix (Fin 11) (Fin 11) ℤ := !![169341569939592988370603938689191234, -105150437736613857268626279237097363, -76064133939552623238928398371417799, 38848004405107019791723543162208945, -103047587608932994125090695376828289, 48699290659003345257682857982759960, 40423093599130887018531205299774665, -38784686142595631390519482499705712, 102359601570342775083624883625406590, -120983234445962068918734307575615309, 74985782760196154462270807735302930; 155111051728622381943610252682999449, -96314183179412184329931608143012213, -69672129639517889537052208842200564, 35583435437523073094605776102059691, -94388044812745341649795280003309470, 44606874704483090911386988248763249, 37026162947009261644773848118397740, -35525438087579560085814951283681542, 93757873272122420534758660048632065, -110816480224777437005250986196455603, 68684397060786936742410062005380912; 142076386660060954690103954067515715, -88220478023623794669447385957475745, -63817273622853235754904420110935907, 32593202583397532916302911605011464, -86456201550132261969632181534014156, 40858362493080615229397185659634133, 33914691343859868994676931973363977, -32540079006295818923526329988274505, 85878986100492014520737885457917955, -101504083153716306081565306003525270, 62912544564487741817434022991223257; 130137081925635045745341166539872418, -80806922571506861339927312341273252, -58454426952726930437975244963395406, 29854252170440191035120818273027866, -79190906023172300997654476198639140, 37424854278082785376247940577706519, 31064690408115591352311172469567264, -29805592801575400271298961940516799, 78662196530874301103361482900412870, -92974247837307603248008955036706210, 57625726263211784921821962075986722; 119201089570503733984289882494999774, -74016360846842812950018211601174665, -53542243916043368728560210761360654, 27345467828013779987795085047059757, -72536145288947328814371639075678521, 34279878885819935502053354284786312, 28454187607600953890783400756092159, -27300897520299253444701887841348580, 72051865584687455540708549234836381, -85161212163479478796949106247250450, 52783182596576557373889487519916555; 109184096835018357265258312152560005, -67796439941913826755597926135660427, -49042853262140254097831221433335173, 25047507687140668701393987982154345, -66440613418915725896134098614494166, 31399189631973161771516097192816353, 26063056858826269747535975018399553, -25006682818752270907887012015644804, 65997029871855363170458692552905427, -78004740300173692043525847216669058, 48347579209637892372662351695518561; 100008876132190607714104951697634013, -62099206394495242131718896751256812, -44921566228402461706614853645423744, 22942655261310263410517232263819029, -60857315947756053776117570279339128, 28760577387933471974195836601297708, 23872863361769447577939339489254628, -22905261086479677859913800003807255, 60451008680505670238934373066322217, -71449658297688257381408145534813787, 44284719117786132979840193888499887; 91604689649417867040935789712664751, -56880736483067592982258708680210363, -41146609101769956229869352848113784, 21014682858429155411257604607916862, -55743207562117120355265615945340312, 26343699356018372286417913550497702, 21866721473874714273284980799152461, -20980431080861691309199058702901496, 55371044084651600678190147089533868, -65445428716401291568690688815205352, 40563279059694225563866142009125734; 83906743984148781212416240699564064, -52100797589950826843254520708596829, -37688878254280485947298738208074162, 19248726470866880641046561010232251, -51058860235978656383923083387643182, 24129922233461390299010091157185144, 20029164527525406982983180718413286, -19217353021075672443446453035906043, 50717971295210891593476227846672423, -59945761000401340991029860263592193, 37154568005689167139320670171335861; 76855690608916635492916507855604284, -47722538021586329572723118064824323, -34521715764054894236062593918053181, 17631171179042346367525816944004821, -46768159254059771086852797408182204, 22102178556022550092856821957098438, 18346025587328087567194592816111085, -17602434178462953202962501695764208, 46455916712880982592192987492882561, -54908254593138177260435004139106199, 34032305959728969304880657015471440; 70397168314496837516804299119335620, -43712202894587248373450493417595261, -31620703891839609513243037843988651, 16149546185051781932293524412742653, -42838024779719662253994461433873976, 20244835113678183687457649362952155, 16804328227887435186122247764996865, -16123224081241206985216443983616790, 42552021354961428474677171440702723, -50294072043637825655794998497246127, 31172421349624057190572859236118275]

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y10 : Fin 11 → (Fin 11 → ℤ) × ℤ := ![(![-1431, 248, 1111, 1029, -919, -771, -776, 851, 968, 388, -79], 3069), (![-27706983575, 3639880760, -7336005993, 9975831061, -31023047175, 2056718317, 25636254704, 2991150115, 36712113824, 24955995972, -6980884527], -31936832699), (![-42522236557893852, -19612663650497178, 174866183877132772, -131180603126033785, -11435772880911470, 97574580169450380, -64238361929621928, -619598385112819, 28758580256979339, -2985659366756986, -35836906205254371], -42159993366915913), (![-5725603793389440903867450, -221351762002521584175405, 328029723018507519885899, -3823100026360568527247393, 11476714157247247934467730, -8311255640031831219054351, -1903514406444170485206552, 5439706501397601427793425, -2254997023332679562630142, 11273756060128186020223819, 129005368020946533217836], -2840436264329294601954608), (![-46840777008379446757615193661455, -7972752191300680126782280331344, -26843258322979113957879603251232, 60619704438735330090767097588903, 7030130107305332311778669271818, 86186067325146387195285746737703, -58512073468710990875137945439917, 3047389918669842994160508750930, -42500586108698383017773957806038, 30252205622071612270445368073896, 23568141900696814277398474474256], -13499733072783408781935908699915), (![1255186525768862501066215139153469361094, -128859328764820349337262856694589482047, -1048966175817643499023724741547945541171, -934655906220595802851362321863603979137, -440586776071884923564441447689765299684, 5140611852902637522409146435409712645, -1777389872900736399576726080351093121546, 98656110414667123153149539915489856221, 1668328155007025230757151579951176933118, 793737060612244466831135144064613949633, 1389066156452220921845979982619406735022], 90573231258833297957777904085268470014), (![3465310493515965882646268261901963517970114033, -32877708695658227929420420596273369836014278830, 8785593978394207616845539832058270781334645095, 6449991196100798088251209035445061319268133991, -295927571431805920630251870676796273540068536, -1222329666036621528542844388236587495994247236, 9032409442310379983643349020807034323479827518, 5898097690051811690033164938289796251316010174, 505410471902847166433510862370086820922503132, 878981606848642508091230001579693193346791488, 14779338978561410669535133814555689653583729897], -707893195390445688626032537989641463253768596), (![31549426498817532625927575260910675183828271239199797, 4090921805183215072101404285141868881868671021912170, 13220939968386739254585510671597092218639108045018163, -6857879797017569885293711068632478693168820862566925, -49318042574282235105780496390175854494448913320442904, -6487573133198469533392635477750492096707099596938340, 3289021373000940286744837487556158034704024992917958, -2641827304258208644736330046956643332956057386605274, -47838189354020343859183318254114770443741060177109076, 52500126841939831606370099729593601804413402683600880, -6873936256880162727029010031209403590380879649935299], 5334156873252668763001991683267554140052966105267308), (![-29382919400750755536852548209261527158917156952578759219733, 25040101862951506412220249037862126431137204468610825523445, 9967358161070184414616121793876886535998942502008579250883, -19628571585488850436483133792719365035037280128617798212895, 16138015488438768342785293755602246137015359377878111556, -1965242218451516059370761174589331276693885448038863919795, 25392185035134006317298547303178440230768755184812961995618, -47679083151023389641817799435137501614419499618992786140764, -11084069217300256650734121174549818623974731783370561177531, 4248374375029999839551395573199138680962869223029157143320, 69241160470574841251765310670858095579400256847994104170551], 11142746228946177335885612679814339743763149188018065667823), (![-2112690393077249271874916848322592703633773341068299808928955635739, 6320897629733398062170313802840715305603678202383157741456767580815, 3024010767389768270161587666452972446346445527456367484686550318897, 1039664384498531033091920900244566303360790348657848918117929107791, -7067213842889280533145287425365877181735473219173887084729401135632, -6391652307396323190629503529759466703419349301762121961901712969961, -4276614742489979654703541241835459474177183390191714568289512696830, 14156167726863814784847723802443305523149726878876283001422056546588, -5304120112172647486059486609891813912574498545753585990579083961217, -9088324477808664462628147668743628376438158121642406056638986794732, 8908613679047441354303365181636730056677913566245274599908960502141], -8616546027572486004421085525753435264693467274227596962898274557799), (![-37631182633086224153948848859081695803225080630889661136688314354186143980, 1317329654793035537526356818318456700775373565303112338754876328741162738, -146702741631268143297933153911960506447379564622229710892484289120178467452, -192850529233345266302917301726007507522655508039956041966326079131699339137, -9074171933656693928398831423581926631890550420582093345487436778654403995, 170093481148337031621054897792658821069108411971099714778731763706467293174, 163077248925324501263713970472694775143408914510658102917814966158373765168, 218132918371634534860936189933202469820916520165157124458736611126030029946, -37147759083251970215616255676167201736540253607841739184912697673326046371, 2510424442311649996984636585885324527289931814888157488073074950021377175, 17773104342314136287333513856784154860418627024163157480262850671644664535], 132734383634166863428577479938539348878872565434168034592567640934392093845)]

theorem lattice10 (m : Fin 11 → ℤ) (hm : m ≠ 0) : 10861070 ≤ pnorm2 (latVec X10 m) :=
  pnorm2_latVec_ge X10 U10 V10 (by decide +kernel) Y10 (by decide +kernel)
    (by decide +kernel) 10861070 (by decide +kernel) m hm

theorem close10 : ∀ i : Fin 11,
    |((10 ^ 39 : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X10 i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X10
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ 10` with
coefficients bounded by `513`.** -/
theorem catalan_aeval_ne_zero_deg10 (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ 10)
    (hcoef : ∀ i, |P.coeff i| ≤ 513) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ 10 (10 ^ 39) X10 close10 10861070 lattice10 513 (by norm_num) P hP hdeg hcoef


end CatalanLattice
