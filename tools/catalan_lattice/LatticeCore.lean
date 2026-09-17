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

