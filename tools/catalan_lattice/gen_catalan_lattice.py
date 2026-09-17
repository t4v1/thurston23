"""Emit CatalanLattice.lean: tail brackets, lattice certificate theorem, enclosure of G, certificates."""
import sympy as sp, mpmath as mp, math, sys
from fractions import Fraction as Fr
from sympy.polys.matrices import DomainMatrix
from sympy import ZZ, QQ

NT   = int(sys.argv[1]) if len(sys.argv) > 1 else 300  # explicit terms per sub-series
DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10
OUT  = sys.argv[3] if len(sys.argv) > 3 else "CatalanLattice.lean"
P = 9
y = sp.symbols('y', positive=True)

def coef(j):
    b = sp.bernoulli(2*j)
    return (sp.Rational(1, 2**(2*j-1)) - 1) * b * sp.Integer(4)**(2*j-1)

def Fexpr(p): return 1/(4*y) + sum(coef(j)/y**(2*j+1) for j in range(1, p))

def Flean(p, var="y"):
    s = "1 / (4 * %s)" % var
    for j in range(1, p):
        c = coef(j)
        s += " %s (%d / %d : ℝ) / %s ^ %d" % ("-" if c < 0 else "+", abs(c.p), c.q, var, 2*j+1)
    return s

def Ffrac(p, yv):
    v = Fr(1, 4) / yv
    for j in range(1, p):
        c = coef(j); v += Fr(int(c.p), int(c.q)) / yv**(2*j+1)
    return v

def step_identity(p, kind):
    g = 1/(y+2)**2
    R = (Fexpr(p) - Fexpr(p).subs(y, y+4) - g) if kind == 'hi' else (g - (Fexpr(p) - Fexpr(p).subs(y, y+4)))
    num, den = sp.fraction(sp.cancel(sp.together(R)))
    N = sp.Poly(sp.expand(num), y)
    assert all(c >= 0 for c in N.all_coeffs())
    D = sp.Poly(sp.expand(den), y)
    # den = const * y^a * (y+2)^2 * (y+4)^a
    const = sp.factor_list(den)[0]
    a = 2*p - 1
    assert sp.expand(const * y**a * (y+2)**2 * (y+4)**a - den) == 0
    terms = ["%d * y ^ %d" % (c, k) for (k,), c in sorted(N.terms()) if c != 0]
    return " + ".join(terms), "(%d * y ^ %d * (y + 2) ^ 2 * (y + 4) ^ %d)" % (const, a, a)

# ---------- enclosure of G -------------------------------------------------
S1 = sum(Fr(1, (4*k+1)**2) for k in range(NT)); S3 = sum(Fr(1, (4*k+3)**2) for k in range(NT))
y1, y3 = Fr(4*NT+1-2), Fr(4*NT+3-2)
g_lo = S1 + Ffrac(P-1, y1) - (S3 + Ffrac(P, y3))
g_hi = S1 + Ffrac(P, y1) - (S3 + Ffrac(P-1, y3))
width = g_hi - g_lo
E = int(-math.floor(math.log10(float(width)))) + 3
den = 10**E
lo_n = math.floor(g_lo * den); hi_n = math.ceil(g_hi * den)
lo, hi = Fr(lo_n, den), Fr(hi_n, den)
mp.mp.dps = 120
assert mp.mpf(lo.numerator)/lo.denominator < mp.catalan < mp.mpf(hi.numerator)/hi.denominator
wid = hi - lo
M = int(math.floor(math.log10(0.02 / (float(wid) * (DMAX + 1) * 2))))
Kint = 10**M
mp.mp.dps = M + 80
G = mp.catalan
print("NT=%d width=%.2e E=%d M=%d" % (NT, float(wid), E, M))

def gs_int(rows):
    Q, Ys, bs = [], [], []
    for j in range(len(rows)):
        v = [Fr(x) for x in rows[j]]
        for q in Q:
            qq = sum(a*a for a in q)
            c = sum(a*b for a, b in zip(v, q)) / qq
            v = [a - c*b for a, b in zip(v, q)]
        Q.append(v)
        L = 1
        for a in v: L = L * a.denominator // math.gcd(L, a.denominator)
        Y = [int(a*L) for a in v]
        g = 0
        for a in Y: g = math.gcd(g, abs(a))
        Y = [a // g for a in Y]
        dc = sum(a*b for a, b in zip(rows[j], Y)); yy = sum(a*a for a in Y)
        Ys.append(Y); bs.append(Fr(dc*dc, yy))
    return Ys, bs

certs = []
for d in range(1, DMAX+1):
    n = d + 1
    X = [int(mp.nint(Kint * G**i)) for i in range(n)]
    for i in range(n):
        assert X[i] - Fr(1, 2) <= Kint * lo**i and Kint * hi**i <= X[i] + Fr(1, 2), (d, i)
    basis = [[1 if i == j else 0 for j in range(n)] + [X[i]] for i in range(n)]
    red = DomainMatrix([[ZZ(x) for x in r] for r in basis], (n, n+1), ZZ).lll(delta=QQ(99, 100))
    C = [[int(x) for x in r] for r in red.to_Matrix().tolist()]
    U = [r[:n] for r in C]
    Vm = sp.Matrix(U).inv(); assert all(x.q == 1 for x in Vm)
    V = [[int(x) for x in r] for r in Vm.tolist()]
    assert sp.Matrix(V) * sp.Matrix(U) == sp.eye(n)
    Ys, bs = gs_int(C)
    B = int(math.floor(min(bs)))
    H = math.isqrt(4*B // (n*(n+4)))
    while H*H*n*(n+4) >= 4*B: H -= 1
    e = len(str(H)) - 3
    if e > 0: H = (H // 10**e) * 10**e
    assert H*H*n*(n+4) < 4*B and H >= 1
    maxY = max(len(str(abs(a))) for Y in Ys for a in Y)
    print("d=%d B~10^%.1f H=%d  max |Y| digits %d" % (d, math.log10(B), H, maxY))
    certs.append((d, X, U, V, Ys, B, H))

# ---------- Lean text ------------------------------------------------------
L = []
w = L.append
w("""import Mathlib
import CatalanEisensteinRatio

/-!
# No small polynomial relation for Catalan's constant

For each degree `d ≤ %(DMAX)d` this file proves that Catalan's constant
`G = ∑ (-1)ⁿ/(2n+1)²` is not a root of any nonzero integer polynomial of degree at most `d`
whose coefficients are bounded by an explicit `H(d)` (`catalan_aeval_ne_zero_deg_d`).
It is the finite shadow of the transcendence of `G`, which is open.

* **Enclosure.** `%(NT)d` terms of each of `∑ 1/(4k+1)²`, `∑ 1/(4k+3)²` and Euler–Maclaurin
  telescoping brackets of orders `8` and `9` for the tails (`CatalanTail`) give
  `G` to `%(E)d` decimals (`catalan_mem`).
* **Lattice certificates.** With `X i = round (10^%(M)d G^i)`, a relation `∑ mᵢ G^i = 0` of height
  `H` yields a vector `(m, m·X)` of squared length at most `(d+1) H² (1 + (d+1)/4)` in the
  lattice `{(m, m·X)}`. An LLL-reduced basis, given by a unimodular `U` with inverse `V`,
  and integer Gram–Schmidt vectors `Y j` certify that every nonzero lattice vector has squared
  length at least `B` (`LatticeCert.pnorm2_latVec_ge`). All certificate checks are
  integer or rational computations done by `decide +kernel`.
-/
"""  % dict(DMAX=DMAX, NT=NT, E=E, M=M))
w("set_option autoImplicit false\n")

# ---- tail section
w("namespace CatalanTail\n\nopen Finset Filter Topology\n")
w("/-- Upper Euler–Maclaurin telescoping function for `∑ 1/(4k+c)²`, `y = c - 2`. -/")
w("noncomputable def hiF (y : ℝ) : ℝ :=\n  " + Flean(P) + "\n")
w("/-- Lower Euler–Maclaurin telescoping function. -/")
w("noncomputable def loF (y : ℝ) : ℝ :=\n  " + Flean(P-1) + "\n")
Nhi, Dhi = step_identity(P, 'hi'); Nlo, Dlo = step_identity(P-1, 'lo')
w("""theorem hi_step {y : ℝ} (hy : 0 < y) : 1 / (y + 2) ^ 2 ≤ hiF y - hiF (y + 4) := by
  have hy2 : 0 < y + 2 := by linarith
  have hy4 : 0 < y + 4 := by linarith
  have key : hiF y - hiF (y + 4) - 1 / (y + 2) ^ 2 =
      (%s) / %s := by
    unfold hiF
    field_simp
    ring
  have hN : 0 ≤ (%s) / %s := by positivity
  linarith
""" % (Nhi, Dhi, Nhi, Dhi))
w("""theorem lo_step {y : ℝ} (hy : 0 < y) : loF y - loF (y + 4) ≤ 1 / (y + 2) ^ 2 := by
  have hy2 : 0 < y + 2 := by linarith
  have hy4 : 0 < y + 4 := by linarith
  have key : 1 / (y + 2) ^ 2 - (loF y - loF (y + 4)) =
      (%s) / %s := by
    unfold loF
    field_simp
    ring
  have hN : 0 ≤ (%s) / %s := by positivity
  linarith
""" % (Nlo, Dlo, Nlo, Dlo))

def tendsto(p, name):
    s = ["theorem tendsto_%s (c : ℝ) : Tendsto (fun k : ℕ => %s (c - 2 + 4 * (k : ℝ))) atTop (𝓝 0) := by" % (name, name)]
    s.append("  have hX : Tendsto (fun k : ℕ => c - 2 + 4 * (k : ℝ)) atTop atTop := by")
    s.append("    have h1 : Tendsto (fun k : ℕ => 4 * (k : ℝ)) atTop atTop :=")
    s.append("      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)")
    s.append("    refine (tendsto_atTop_add_const_right atTop (c - 2) h1).congr fun k => ?_")
    s.append("    ring")
    s.append("  have h0 : Tendsto (fun k : ℕ => 1 / (4 * (c - 2 + 4 * (k : ℝ)))) atTop (𝓝 0) :=")
    s.append("    tendsto_const_nhds.div_atTop (hX.const_mul_atTop (by norm_num))")
    expr = "h0"
    for j in range(1, p):
        c = coef(j)
        s.append("  have h%d : Tendsto (fun k : ℕ => (%d / %d : ℝ) / (c - 2 + 4 * (k : ℝ)) ^ %d) atTop (𝓝 0) :=" % (j, abs(c.p), c.q, 2*j+1))
        s.append("    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (%d : ℕ) ≠ 0)).comp hX)" % (2*j+1))
        expr = "(%s.%s h%d)" % (expr, "sub" if c < 0 else "add", j)
    s.append("  have h := %s" % expr)
    s.append("  simp only [sub_zero, add_zero] at h")
    s.append("  exact h\n")
    return "\n".join(s)
w(tendsto(P, "hiF")); w(tendsto(P-1, "loF"))
w("""theorem tsum_le_hiF {c : ℝ} (hc : 2 < c) :
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

/-- **Catalan's constant to %(E)d decimals.** -/
theorem catalan_mem :
    ((%(lo)d / 10 ^ %(E)d : ℚ) : ℝ) ≤ ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) ∧
      ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) ≤ ((%(hi)d / 10 ^ %(E)d : ℚ) : ℝ) := by
  rw [CatalanEisensteinRatio.catalan_eq,
    CatalanEisensteinRatio.tsum_split (m := 4) (c := 1) (by norm_num) (by norm_num) %(NT)d %(c1)d
      (by norm_num),
    CatalanEisensteinRatio.tsum_split (m := 4) (c := 3) (by norm_num) (by norm_num) %(NT)d %(c3)d
      (by norm_num)]
  have u1 := tsum_le_hiF (c := %(c1)d) (by norm_num)
  have l1 := loF_le_tsum (c := %(c1)d) (by norm_num)
  have u3 := tsum_le_hiF (c := %(c3)d) (by norm_num)
  have l3 := loF_le_tsum (c := %(c3)d) (by norm_num)
  generalize (∑' k : ℕ, 1 / ((4 : ℝ) * k + %(c1)d) ^ 2) = T1 at *
  generalize (∑' k : ℕ, 1 / ((4 : ℝ) * k + %(c3)d) ^ 2) = T3 at *
  norm_num [hiF, loF, Finset.sum_range_succ] at u1 l1 u3 l3 ⊢
  constructor <;> linarith

end CatalanTail
""" % dict(E=E, lo=lo_n, hi=hi_n, NT=NT, c1=4*NT+1, c3=4*NT+3))

# ---- lattice section
w(open("LatticeCore.lean").read())

# ---- certificates
w("namespace CatalanLattice\n\nopen LatticeCert Polynomial\n")
w("""/-- `|K θ^i - X i| ≤ 1/2` from a rational enclosure of `θ` and rational checks. -/
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
    (0 : ℚ) ≤ %(lo)d / 10 ^ %(E)d := by norm_num

""" % dict(lo=lo_n, E=E))

def vec(v): return "![" + ", ".join(str(x) for x in v) + "]"
def mat(Mx): return "!![" + "; ".join(", ".join(str(x) for x in r) for r in Mx) + "]"

for (d, X, U, V, Ys, B, H) in certs:
    n = d + 1
    Yl = "![" + ", ".join("(%s, %d)" % (vec(Y[:n]), Y[n]) for Y in Ys) + "]"
    w("""/-! ### Degree %(d)d -/

/-- `round (10^%(M)d G^i)`, `i ≤ %(d)d`. -/
def X%(d)d : Fin %(n)d → ℤ := %(X)s

/-- The LLL transformation: row `k` gives the `k`-th reduced basis vector. -/
def U%(d)d : Matrix (Fin %(n)d) (Fin %(n)d) ℤ := %(U)s

/-- The inverse of `U%(d)d`. -/
def V%(d)d : Matrix (Fin %(n)d) (Fin %(n)d) ℤ := %(V)s

/-- Integer multiples of the Gram–Schmidt vectors of the reduced basis. -/
def Y%(d)d : Fin %(n)d → (Fin %(n)d → ℤ) × ℤ := %(Y)s

theorem lattice%(d)d (m : Fin %(n)d → ℤ) (hm : m ≠ 0) : %(B)d ≤ pnorm2 (latVec X%(d)d m) :=
  pnorm2_latVec_ge X%(d)d U%(d)d V%(d)d (by decide +kernel) Y%(d)d (by decide +kernel)
    (by decide +kernel) %(B)d (by decide +kernel) m hm

theorem close%(d)d : ∀ i : Fin %(n)d,
    |((10 ^ %(M)d : ℕ) : ℝ) * (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) ^ (i : ℕ) - X%(d)d i| ≤ 1 / 2 :=
  close_of_rat catalan_close_lo CatalanTail.catalan_mem.1 CatalanTail.catalan_mem.2 _ X%(d)d
    (by decide +kernel)

/-- **Catalan's constant is not a root of a nonzero integer polynomial of degree `≤ %(d)d` with
coefficients bounded by `%(H)d`.** -/
theorem catalan_aeval_ne_zero_deg%(d)d (P : ℤ[X]) (hP : P ≠ 0) (hdeg : P.natDegree ≤ %(d)d)
    (hcoef : ∀ i, |P.coeff i| ≤ %(H)d) :
    aeval (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) P ≠ 0 :=
  aeval_ne_zero_of_small _ %(d)d (10 ^ %(M)d) X%(d)d close%(d)d %(B)d lattice%(d)d %(H)d (by norm_num) P hP hdeg hcoef

""" % dict(d=d, n=n, M=M, X=vec(X), U=mat(U), V=mat(V), Y=Yl, B=B, H=H))
w("end CatalanLattice\n")
open(OUT, "w").write("\n".join(L))
print("wrote", OUT, sum(len(s) for s in L), "chars")
