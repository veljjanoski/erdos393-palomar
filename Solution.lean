module

public import Mathlib

/-!
# Erdős Problem 393: proof of `f(n) → ∞` assuming the abc conjecture

Proof of the statement of `Challenge.lean`, following Luca's proof of [Lu02, Proposition 1]. The
definitions are repeated verbatim.

If `f(n)` does not tend to infinity, then one shape `T` (the offsets of the factors from the
smallest one) occurs for infinitely many `n`: `∏_{i ∈ T} (a + i) = n!` with `d = #T ≥ 2`. Put
`y = d·a + ∑_{i ∈ T} i`. The shift removes the term of degree `d − 1`, so
`d^d n! = y^d + y^k R(y)` with `k + deg R ≤ d − 2` and `R(0) ≠ 0`. Write `j = d − k`. Then
`d^d n! = y^k N` with `N = y^j + R(y)`, so `N` divides `d^d n!`. The common factor of `y^j` and
`R(y)` divides `R(0)^j`, so it is bounded (Luca instead lets this factor cancel). After removing
it, the abc conjecture applied to `y^j + R(y) = N` gives `y^j ≲ (y^(j-1) · 4^n)^(1+ε)`, because
`rad(n!) ≤ 4^n`.
With `ε = 1/(2d)` this bounds `y` by an exponential in `n`. Since `y^d ≥ n!`, this fails for
large `n`.

*References:*
- [Lu02] Luca, Florian, *The Diophantine equation $P(x)=n!$ and a result of M. Overholt*.
  Glas. Mat. Ser. III 37 (2002), 269-273.
-/

@[expose] public section

open Filter Asymptotics
open scoped Nat

namespace ABC

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

end ABC

namespace Erdos393

/--
`f n` is $f(n)$, the minimal $m \geq 1$ such that $n! = a_1 \cdots a_t$ with
$a_1 < \cdots < a_t = a_1 + m$. The factors are recorded as a finite set
$s \subseteq [a, a + m]$ of natural numbers that contains $a = a_1$ and $a + m = a_t$. Since
$m \geq 1$ there are at least two factors, and they are positive because $n! \neq 0$.

Such a factorisation exists for $n \geq 2$. For $n \leq 1$ there is none, since $n! = 1$, and
`f n` is the junk value `0`.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
    ∏ i ∈ s, i = n !}

end Erdos393

namespace Erdos393Proof

open ABC Polynomial

/-! ### The radical -/

lemma radical_eq (n : ℕ) : radical n = ∏ p ∈ n.primeFactors, p := rfl

lemma radical_pos (n : ℕ) : 0 < radical n :=
  Finset.prod_pos fun _ hp ↦ (Nat.prime_of_mem_primeFactors hp).pos

lemma radical_zero : radical 0 = 1 := by simp [radical]

lemma radical_le_self {n : ℕ} (hn : n ≠ 0) : radical n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

lemma radical_le_of_dvd {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : radical m ≤ radical n :=
  Nat.le_of_dvd (radical_pos n)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono h hn))

lemma radical_mul_le (a b : ℕ) : radical (a * b) ≤ radical a * radical b := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_mul, radical_zero, one_mul]; exact radical_pos b
  rcases eq_or_ne b 0 with rfl | hb
  · rw [mul_zero, radical_zero, mul_one]; exact radical_pos a
  refine Nat.le_of_dvd (Nat.mul_pos (radical_pos a) (radical_pos b)) ?_
  rw [radical_eq, radical_eq, radical_eq, Nat.primeFactors_mul ha hb, ← Finset.prod_union_inter]
  exact dvd_mul_right _ _

lemma radical_pow (n : ℕ) {k : ℕ} (hk : k ≠ 0) : radical (n ^ k) = radical n := by
  rw [radical_eq, radical_eq, Nat.primeFactors_pow n hk]

/-- `rad(n!)` is the product of the primes up to `n`, which is at most `4^n`. -/
lemma radical_factorial_le (n : ℕ) : radical n ! ≤ 4 ^ n := by
  refine le_trans (Nat.le_of_dvd (primorial_pos n) ?_) (primorial_le_four_pow n)
  rw [radical_eq, primorial]
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp ↦ ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le
    ((Nat.Prime.dvd_factorial hp').1 (Nat.dvd_of_mem_primeFactors hp))), hp'⟩

/-! ### Elementary facts -/

/-- `gcd(b, a^j)` divides `gcd(b, a)^j`. -/
lemma gcd_pow_dvd (a b : ℕ) : ∀ j : ℕ, Nat.gcd b (a ^ j) ∣ Nat.gcd b a ^ j
  | 0 => by simp
  | j + 1 => by
    rw [pow_succ, pow_succ]
    exact (Nat.gcd_mul_right_dvd_mul_gcd b (a ^ j) a).trans
      (Nat.mul_dvd_mul_right (gcd_pow_dvd a b j) _)

/-- A polynomial value is at most the sum of the absolute coefficients times `y ^ deg`. -/
lemma natAbs_eval_le (R : ℤ[X]) {y : ℕ} (hy : 1 ≤ y) :
    (R.eval (y : ℤ)).natAbs ≤
      (∑ i ∈ Finset.range (R.natDegree + 1), (R.coeff i).natAbs) * y ^ R.natDegree := by
  have hy' : (1 : ℤ) ≤ y := by exact_mod_cast hy
  have h : |R.eval (y : ℤ)| ≤
      (∑ i ∈ Finset.range (R.natDegree + 1), |R.coeff i|) * (y : ℤ) ^ R.natDegree := by
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ y)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hy' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) (abs_nonneg _)
  zify
  simpa using h

/-- `n!` grows faster than any exponential. -/
lemma eventually_mul_pow_lt_factorial (K X : ℕ) : ∀ᶠ n in atTop, K * X ^ n < n ! := by
  have h2 : ∀ᶠ n in atTop, (X : ℝ) ^ n / n ! < 1 / (K + 1) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (X : ℝ)).eventually (gt_mem_nhds (by positivity))
  filter_upwards [h2] with n hn
  have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_lt_div_iff₀ hf (by positivity), one_mul] at hn
  have hX : (0 : ℝ) ≤ (X : ℝ) ^ n := by positivity
  have : (K : ℝ) * X ^ n < n ! := by nlinarith
  exact_mod_cast this

/-! ### The abc conjecture -/

/-- The type of `ABC.abc` in formal-conjectures (the abc conjecture), written with projections
instead of the pattern `(a, b, c)`. A pattern here would create an auxiliary `match` function that
the main theorem's statement would then reuse, so that statement would no longer be the same
expression as in `Challenge.lean`. -/
abbrev AbcHyp : Prop := ∀ (ε : ℝ), 0 < ε →
    {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      ({t.1, t.2.1, t.2.2} : Set ℕ).Pairwise Nat.Coprime ∧ t.1 + t.2.1 = t.2.2 ∧
      (radical <| t.1 * t.2.1 * t.2.2 : ℝ)^(1 + ε) < t.2.2}.Finite

/-- The abc conjecture in the form used below: a coprime sum `u + v = w` has `w` bounded or
`w ≤ rad(uvw)^(1+ε)`. -/
lemma abc_dichotomy (habc : AbcHyp) (ε : ℝ) (hε : 0 < ε) :
    ∃ cmax : ℕ, ∀ u v w : ℕ, 0 < u → 0 < v → Nat.Coprime u v → u + v = w →
      w ≤ cmax ∨ (w : ℝ) ≤ (radical (u * v * w) : ℝ) ^ (1 + ε) := by
  obtain ⟨cmax, hc⟩ := ((habc ε hε).image fun t : ℕ × ℕ × ℕ ↦ t.2.2).bddAbove
  refine ⟨cmax, fun u v w hu hv huv huvw ↦ ?_⟩
  by_cases h : (radical (u * v * w) : ℝ) ^ (1 + ε) < w
  · left
    have huw : Nat.Coprime u w := by
      rw [← huvw, add_comm]; exact Nat.coprime_add_self_right.2 huv
    have hvw : Nat.Coprime v w := by
      rw [← huvw]; exact Nat.coprime_add_self_right.2 huv.symm
    have hvu := huv.symm
    have hwu := huw.symm
    have hwv := hvw.symm
    refine hc ⟨(u, v, w), ⟨hu, hv, show 0 < w by omega, ?_, huvw, h⟩, rfl⟩
    show ({u, v, w} : Set ℕ).Pairwise Nat.Coprime
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) hxy <;>
      first | exact absurd rfl hxy | assumption
  · exact Or.inr (not_lt.1 h)

/-! ### The main estimate -/

/-- The core of Luca's argument. If `y^d + y^k R(y) = d^d n!` with `R(0) ≠ 0` and
`k + deg R ≤ d − 2`, and `y^d ≥ n!`, then `n!` is at most an exponential in `n`. -/
lemma core (habc : AbcHyp)
    (d k : ℕ) (R : ℤ[X]) (hR0 : R.eval 0 ≠ 0) (hdeg : k + R.natDegree + 2 ≤ d) :
    ∃ K X : ℕ, ∀ y n : ℕ, 1 ≤ y → n ! ≤ y ^ d →
      (y : ℤ) ^ d + (y : ℤ) ^ k * R.eval (y : ℤ) = (d : ℤ) ^ d * n ! → n ! ≤ K * X ^ n := by
  set j := d - k with hj
  have hkj : k + j = d := by omega
  have hd0 : d ≠ 0 := by omega
  set G0 := (R.eval 0).natAbs with hG0def
  have hG0 : 0 < G0 := Int.natAbs_pos.2 hR0
  set CR := ∑ i ∈ Finset.range (R.natDegree + 1), (R.coeff i).natAbs with hCR
  set ε : ℝ := 1 / (2 * d) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨cmax, hcmax⟩ := abc_dichotomy habc ε hε
  set G := G0 ^ d with hGdef
  set K3 := G ^ (2 * d) * (CR * d) ^ (2 * d + 1) with hK3
  refine ⟨G0 ^ d + (G * cmax) ^ d + K3, 4 ^ (2 * d + 1), ?_⟩
  intro y n hy hyd hid
  have hXn : 0 < (4 ^ (2 * d + 1)) ^ n := by positivity
  suffices h : n ! ≤ G0 ^ d ∨ n ! ≤ (G * cmax) ^ d ∨ n ! ≤ K3 * (4 ^ (2 * d + 1)) ^ n by
    rcases h with h | h | h
    · exact h.trans (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans
        (Nat.le_mul_of_pos_right _ hXn))
    · exact h.trans (((Nat.le_add_left _ _).trans (Nat.le_add_right _ _)).trans
        (Nat.le_mul_of_pos_right _ hXn))
    · exact h.trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  have hy0 : y ≠ 0 := by omega
  have hfac : (y : ℤ) ^ k * ((y : ℤ) ^ j + R.eval (y : ℤ)) = (d : ℤ) ^ d * n ! := by
    rw [← hid, mul_add, ← pow_add, hkj]
  have hsub : (y : ℤ) ∣ R.eval (y : ℤ) - R.eval 0 := by
    have h := sub_dvd_eval_sub (y : ℤ) 0 R
    rwa [sub_zero] at h
  by_cases hRy : R.eval (y : ℤ) = 0
  · -- Then `y ∣ R(0)`, so `y` is bounded.
    left
    rw [hRy, zero_sub, dvd_neg] at hsub
    exact hyd.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hG0 (Int.natCast_dvd.1 hsub)) d)
  right
  set N : ℤ := (y : ℤ) ^ j + R.eval (y : ℤ) with hNdef
  have hNpos : 0 < N := by
    have hpos : (0 : ℤ) < (d : ℤ) ^ d * n ! := by
      have : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
      positivity
    rw [← hfac] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)
  set A0 := y ^ j with hA0def
  set B0 := (R.eval (y : ℤ)).natAbs with hB0def
  set N0 := N.natAbs with hN0def
  have hA0 : 0 < A0 := by positivity
  have hB0 : 0 < B0 := Int.natAbs_pos.2 hRy
  have hN0pos : 0 < N0 := Int.natAbs_pos.2 hNpos.ne'
  have hN0 : (N0 : ℤ) = N := Int.natAbs_of_nonneg hNpos.le
  -- `N` divides `d^d n!`.
  have hN0dvd : N0 ∣ d ^ d * n ! := by
    have h := congrArg Int.natAbs hfac
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow] at h
    simp only [Int.natAbs_natCast] at h
    exact Dvd.intro_left _ h
  -- The common factor `g` of `y^j` and `R(y)` is bounded.
  set g := Nat.gcd A0 B0 with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hA0
  have hgG : g ≤ G := by
    have hh : 0 < Nat.gcd B0 y := Nat.gcd_pos_of_pos_left _ hB0
    have hgh : g ∣ Nat.gcd B0 y ^ j := by rw [hgdef, Nat.gcd_comm]; exact gcd_pow_dvd y B0 j
    have hhG : Nat.gcd B0 y ∣ G0 := by
      have h1 : ((Nat.gcd B0 y : ℕ) : ℤ) ∣ (y : ℤ) :=
        Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)
      have h2 : ((Nat.gcd B0 y : ℕ) : ℤ) ∣ R.eval (y : ℤ) :=
        Int.natCast_dvd.2 (Nat.gcd_dvd_left _ _)
      have h3 := dvd_sub h2 (h1.trans hsub)
      rw [sub_sub_cancel] at h3
      exact Int.natCast_dvd.1 h3
    calc g ≤ Nat.gcd B0 y ^ j := Nat.le_of_dvd (pow_pos hh j) hgh
      _ ≤ G0 ^ j := Nat.pow_le_pow_left (Nat.le_of_dvd hG0 hhG) j
      _ ≤ G0 ^ d := Nat.pow_le_pow_right hG0 (by omega)
  have hdvdA : g ∣ A0 := Nat.gcd_dvd_left _ _
  have hdvdB : g ∣ B0 := Nat.gcd_dvd_right _ _
  have hdvdN : g ∣ N0 := by
    have h1 : (g : ℤ) ∣ (y : ℤ) ^ j := by exact_mod_cast hdvdA
    have h2 : (g : ℤ) ∣ R.eval (y : ℤ) := Int.natCast_dvd.2 hdvdB
    exact Int.natCast_dvd.1 (dvd_add h1 h2)
  set a1 := A0 / g with ha1def
  set b1 := B0 / g with hb1def
  set c1 := N0 / g with hc1def
  have hcop : Nat.Coprime a1 b1 := Nat.coprime_div_gcd_div_gcd hg
  have ha1 : a1 * g = A0 := Nat.div_mul_cancel hdvdA
  have hb1 : b1 * g = B0 := Nat.div_mul_cancel hdvdB
  have hc1 : c1 * g = N0 := Nat.div_mul_cancel hdvdN
  have ha1pos : 0 < a1 := Nat.div_pos (Nat.le_of_dvd hA0 hdvdA) hg
  have hb1pos : 0 < b1 := Nat.div_pos (Nat.le_of_dvd hB0 hdvdB) hg
  have hc1pos : 0 < c1 := Nat.div_pos (Nat.le_of_dvd hN0pos hdvdN) hg
  -- Apply abc to `a1 + b1 = c1` or `c1 + b1 = a1`, depending on the sign of `R(y)`.
  obtain ⟨W, haW, hWd⟩ : ∃ W : ℕ, a1 ≤ W ∧
      (W ≤ cmax ∨ (W : ℝ) ≤ (radical (a1 * b1 * c1) : ℝ) ^ (1 + ε)) := by
    rcases lt_or_gt_of_ne hRy with hneg | hpos
    · have hB0' : (B0 : ℤ) = -R.eval (y : ℤ) := Int.ofNat_natAbs_of_nonpos hneg.le
      have hrel : N0 + B0 = A0 := by
        have : (N0 : ℤ) + B0 = A0 := by rw [hN0, hB0', hNdef, hA0def]; push_cast; ring
        exact_mod_cast this
      have hsum : c1 + b1 = a1 :=
        Nat.eq_of_mul_eq_mul_right hg (by rw [add_mul, hc1, hb1, ha1, hrel])
      have hcop' : Nat.Coprime c1 b1 := by
        have h := hcop
        rw [← hsum] at h
        exact Nat.coprime_add_self_left.1 h
      refine ⟨a1, le_rfl, ?_⟩
      rcases hcmax c1 b1 a1 hc1pos hb1pos hcop' hsum with h | h
      · exact Or.inl h
      · right
        rwa [show c1 * b1 * a1 = a1 * b1 * c1 by ring] at h
    · have hB0' : (B0 : ℤ) = R.eval (y : ℤ) := Int.natAbs_of_nonneg hpos.le
      have hrel : A0 + B0 = N0 := by
        have : (A0 : ℤ) + B0 = N0 := by rw [hN0, hB0', hNdef, hA0def]; push_cast; ring
        exact_mod_cast this
      have hsum : a1 + b1 = c1 :=
        Nat.eq_of_mul_eq_mul_right hg (by rw [add_mul, hc1, hb1, ha1, hrel])
      exact ⟨c1, by omega, hcmax a1 b1 c1 ha1pos hb1pos hcop hsum⟩
  have hA0le : A0 ≤ G * W :=
    calc A0 = a1 * g := ha1.symm
      _ ≤ W * G := Nat.mul_le_mul haW hgG
      _ = G * W := mul_comm _ _
  have hyA : y ≤ A0 := Nat.le_self_pow (by omega) y
  rcases hWd with hW | hW
  · -- An exceptional triple: `y` is bounded.
    left
    exact hyd.trans (Nat.pow_le_pow_left (hyA.trans (hA0le.trans (Nat.mul_le_mul_left G hW))) d)
  right
  -- The radical is at most `y · |R(y)| · rad(d^d n!) ≤ CR · d · 4^n · y^(j-1)`.
  set Rb := y * (CR * y ^ (j - 2)) * (d * 4 ^ n) with hRbdef
  have hrad : radical (a1 * b1 * c1) ≤ Rb := by
    have hra : radical a1 ≤ y := by
      refine (radical_le_of_dvd (Nat.div_dvd_of_dvd hdvdA) hA0.ne').trans ?_
      rw [hA0def, radical_pow y (by omega)]
      exact radical_le_self hy0
    have hrb : radical b1 ≤ CR * y ^ (j - 2) :=
      (radical_le_self hb1pos.ne').trans ((Nat.div_le_self _ _).trans ((natAbs_eval_le R hy).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hy (by omega)))))
    have hrc : radical c1 ≤ d * 4 ^ n := by
      refine (radical_le_of_dvd (Nat.div_dvd_of_dvd hdvdN) hN0pos.ne').trans ?_
      refine (radical_le_of_dvd hN0dvd (by positivity)).trans ?_
      refine (radical_mul_le _ _).trans (Nat.mul_le_mul ?_ (radical_factorial_le n))
      rw [radical_pow d hd0]
      exact radical_le_self hd0
    calc radical (a1 * b1 * c1) ≤ radical (a1 * b1) * radical c1 := radical_mul_le _ _
      _ ≤ radical a1 * radical b1 * radical c1 := Nat.mul_le_mul_right _ (radical_mul_le _ _)
      _ ≤ Rb := Nat.mul_le_mul (Nat.mul_le_mul hra hrb) hrc
  -- Raise `W ≤ Rb^(1+ε)` to the power `2d`.
  have hW2 : W ^ (2 * d) ≤ Rb ^ (2 * d + 1) := by
    have h1 : (W : ℝ) ≤ (Rb : ℝ) ^ (1 + ε) :=
      hW.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hrad) (by positivity))
    have h2 : (W : ℝ) ^ (2 * d) ≤ ((Rb : ℝ) ^ (1 + ε)) ^ (2 * d) :=
      pow_le_pow_left₀ (by positivity) h1 _
    rw [← Real.rpow_natCast ((Rb : ℝ) ^ (1 + ε)), ← Real.rpow_mul (by positivity)] at h2
    have h3 : (1 + ε) * ((2 * d : ℕ) : ℝ) = ((2 * d + 1 : ℕ) : ℝ) := by
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
      rw [hεdef]
      push_cast
      field_simp
    rw [h3, Real.rpow_natCast] at h2
    exact_mod_cast h2
  have key : y ^ (j * (2 * d)) ≤ G ^ (2 * d) * Rb ^ (2 * d + 1) :=
    calc y ^ (j * (2 * d)) = A0 ^ (2 * d) := by rw [hA0def, pow_mul]
      _ ≤ (G * W) ^ (2 * d) := Nat.pow_le_pow_left hA0le _
      _ = G ^ (2 * d) * W ^ (2 * d) := mul_pow _ _ _
      _ ≤ G ^ (2 * d) * Rb ^ (2 * d + 1) := Nat.mul_le_mul_left _ hW2
  have hRb : Rb = CR * d * 4 ^ n * y ^ (j - 1) := by
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    rw [hRbdef, hj', show j' + 2 - 2 = j' by omega, show j' + 2 - 1 = j' + 1 by omega]
    ring
  have hexp : (d + 1) + (j - 1) * (2 * d + 1) ≤ j * (2 * d) := by
    obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hjd : j' + 1 ≤ d := by omega
    rw [hj', show j' + 1 - 1 = j' by omega,
      show d + 1 + j' * (2 * d + 1) = j' * (2 * d) + (j' + d + 1) by ring,
      show (j' + 1) * (2 * d) = j' * (2 * d) + 2 * d by ring]
    exact Nat.add_le_add_left (by omega) _
  have hY : 0 < y ^ ((j - 1) * (2 * d + 1)) := by positivity
  have hmain : y ^ (d + 1) * y ^ ((j - 1) * (2 * d + 1)) ≤
      (K3 * (4 ^ (2 * d + 1)) ^ n) * y ^ ((j - 1) * (2 * d + 1)) :=
    calc y ^ (d + 1) * y ^ ((j - 1) * (2 * d + 1))
        = y ^ ((d + 1) + (j - 1) * (2 * d + 1)) := (pow_add _ _ _).symm
      _ ≤ y ^ (j * (2 * d)) := Nat.pow_le_pow_right hy hexp
      _ ≤ G ^ (2 * d) * Rb ^ (2 * d + 1) := key
      _ = (K3 * (4 ^ (2 * d + 1)) ^ n) * y ^ ((j - 1) * (2 * d + 1)) := by
        rw [hRb, hK3]; ring
  calc n ! ≤ y ^ d := hyd
    _ ≤ y ^ (d + 1) := Nat.pow_le_pow_right hy (by omega)
    _ ≤ K3 * (4 ^ (2 * d + 1)) ^ n := Nat.le_of_mul_le_mul_right hmain hY

/-! ### From a shape to the polynomial identity -/

/-- For a shape `T ∋ 0` with a nonzero element, `y = d·a + ∑ T` satisfies
`y^d + y^k R(y) = d^d ∏_{i ∈ T} (a + i)`, with `R(0) ≠ 0` and `k + deg R ≤ d − 2`. -/
lemma poly_shape (T : Finset ℕ) (h0 : 0 ∈ T) {m : ℕ} (hm : m ∈ T) (hm0 : m ≠ 0) :
    ∃ (k : ℕ) (R : ℤ[X]), R.eval 0 ≠ 0 ∧ k + R.natDegree + 2 ≤ T.card ∧ ∀ a : ℕ,
      ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) ^ T.card +
        ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) ^ k * R.eval ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) =
      (T.card : ℤ) ^ T.card * ((∏ i ∈ T, (a + i) : ℕ) : ℤ) := by
  have hd2 : 2 ≤ T.card := Finset.one_lt_card.2 ⟨0, h0, m, hm, fun h ↦ hm0 h.symm⟩
  set d := T.card with hd
  set e : ℤ := ((∑ i ∈ T, i : ℕ) : ℤ) with he
  set P : ℤ[X] := ∏ i ∈ T, (X - C (e - d * (i : ℤ))) with hP
  have hmon : ∀ i ∈ T, (X - C (e - d * (i : ℤ))).Monic := fun i _ ↦ monic_X_sub_C _
  have hPmonic : P.Monic := monic_prod_of_monic _ _ hmon
  have hPdeg : P.natDegree = d := by
    rw [hP, natDegree_prod_of_monic _ _ hmon]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, hd]
  have hsum : ∑ i ∈ T, (e - d * (i : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, he, hd]
    push_cast
    ring
  have hnext : P.coeff (d - 1) = 0 := by
    have h : P.nextCoeff = -∑ i ∈ T, (e - d * (i : ℤ)) := prod_X_sub_C_nextCoeff _
    rw [nextCoeff_of_natDegree_pos (by rw [hPdeg]; omega), hPdeg, hsum, neg_zero] at h
    exact h
  set Q : ℤ[X] := P - X ^ d with hQ
  have hQdeg : Q.natDegree ≤ d - 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hQ, coeff_sub, coeff_X_pow]
    rcases (show N = d - 1 ∨ N = d ∨ d < N by omega) with rfl | rfl | hlt
    · rw [ite_eq_right (by omega), hnext, sub_zero]
    · rw [ite_eq_left rfl, ← hPdeg, hPmonic.coeff_natDegree, sub_self]
    · rw [ite_eq_right (by omega), coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact hlt),
        sub_zero]
  have hQ0 : Q ≠ 0 := by
    intro hQz
    have hPX : P = X ^ d := sub_eq_zero.1 hQz
    have hev : P.eval e = 0 := by
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero h0 (by simp)
    rw [hPX, eval_pow, eval_X] at hev
    have he0 : e = 0 := (pow_eq_zero_iff (by omega)).1 hev
    have hme : (m : ℤ) ≤ e := by
      rw [he]
      exact_mod_cast Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hm
    omega
  obtain ⟨R, hQR, hRX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ0 0
  rw [map_zero, sub_zero] at hQR hRX
  have hR0 : R.eval 0 ≠ 0 := by rwa [X_dvd_iff, coeff_zero_eq_eval_zero] at hRX
  have hRne : R ≠ 0 := by
    rintro rfl
    exact hR0 (eval_zero)
  have hQdeg' : Q.natDegree = Q.rootMultiplicity 0 + R.natDegree := by
    conv_lhs => rw [hQR]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hRne, natDegree_X_pow]
  refine ⟨Q.rootMultiplicity 0, R, hR0, by omega, fun a ↦ ?_⟩
  set y : ℤ := ((d * a + ∑ i ∈ T, i : ℕ) : ℤ) with hy
  have hPy : P.eval y = (d : ℤ) ^ d * ((∏ i ∈ T, (a + i) : ℕ) : ℤ) := by
    rw [hP, eval_prod]
    calc ∏ i ∈ T, eval y (X - C (e - d * (i : ℤ))) = ∏ i ∈ T, ((d : ℤ) * ((a + i : ℕ) : ℤ)) :=
          Finset.prod_congr rfl fun i _ ↦ by
            rw [eval_sub, eval_X, eval_C, hy, he]
            push_cast
            ring
      _ = (d : ℤ) ^ d * ((∏ i ∈ T, (a + i) : ℕ) : ℤ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← hd]
        push_cast
        rfl
  have hQy : Q.eval y = y ^ Q.rootMultiplicity 0 * R.eval y := by
    conv_lhs => rw [hQR]
    rw [eval_mul, eval_pow, eval_X]
  have hQP : Q.eval y = P.eval y - y ^ d := by rw [hQ, eval_sub, eval_pow, eval_X]
  rw [← hPy]
  linear_combination hQP - hQy

/-- One shape `T` gives `n!` at most an exponential in `n`. -/
lemma shape_bound (habc : AbcHyp)
    (T : Finset ℕ) (h0 : 0 ∈ T) {m : ℕ} (hm : m ∈ T) (hm0 : m ≠ 0) :
    ∃ K X : ℕ, ∀ a n : ℕ, ∏ i ∈ T, (a + i) = n ! → n ! ≤ K * X ^ n := by
  obtain ⟨k, R, hR0, hdeg, hid⟩ := poly_shape T h0 hm hm0
  obtain ⟨K, X, hKX⟩ := core habc T.card k R hR0 hdeg
  have hpos : 0 < T.card := Finset.card_pos.2 ⟨m, hm⟩
  refine ⟨K, X, fun a n h ↦ hKX (T.card * a + ∑ i ∈ T, i) n ?_ ?_ ?_⟩
  · have : m ≤ ∑ i ∈ T, i := Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hm
    omega
  · rw [← h]
    exact Finset.prod_le_pow_card _ _ _ fun i hi ↦
      Nat.add_le_add (Nat.le_mul_of_pos_left a hpos)
        (Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hi)
  · have := hid a
    rw [h] at this
    exact_mod_cast this

end Erdos393Proof

namespace Erdos393

open ABC in
/--
Luca [Lu02] proved that the $abc$ conjecture implies that, for every $P \in \mathbb{Z}[x]$ of
degree at least $2$, the equation $P(x) = n!$ has only finitely many solutions. As remarked on
erdosproblems.com, this implies that $f(n) \to \infty$, conditional on the $abc$ conjecture
(`ABC.abc`).
-/
theorem erdos_393.variants.luca (habc : ∀ (ε : ℝ) (hε : 0 < ε),
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite) : Tendsto f atTop atTop := by
  have habc : Erdos393Proof.AbcHyp := fun ε hε ↦ habc ε hε
  rw [tendsto_atTop]
  intro M
  have key : ∀ T ∈ (Finset.range M).powerset, ∀ᶠ n in atTop,
      0 ∈ T → ∀ m ∈ T, m ≠ 0 → ∀ a, ∏ i ∈ T, (a + i) ≠ n ! := by
    intro T _
    by_cases hT : 0 ∈ T ∧ ∃ m ∈ T, m ≠ 0
    · obtain ⟨h0, m, hm, hm0⟩ := hT
      obtain ⟨K, X, hKX⟩ := Erdos393Proof.shape_bound habc T h0 hm hm0
      filter_upwards [Erdos393Proof.eventually_mul_pow_lt_factorial K X] with n hn
      intro _ _ _ _ a ha
      exact absurd (hKX a n ha) (not_le.2 hn)
    · exact Filter.Eventually.of_forall fun n h0 m hm hm0 ↦ absurd ⟨h0, m, hm, hm0⟩ hT
  filter_upwards [(Filter.eventually_all_finset _).2 key, eventually_ge_atTop 2] with n hn hn2
  by_contra hlt
  rw [not_le] at hlt
  have hne : {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !}.Nonempty := by
    refine ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_,
      Finset.prod_Ico_id_eq_factorial n⟩
    · intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hi
      exact Finset.mem_Icc.2 ⟨h1, by omega⟩
    · exact Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    · exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  obtain ⟨hm1, a, s, hs, has, hams, hprod⟩ : f n ∈ {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ,
      ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧ ∏ i ∈ s, i = n !} := Nat.sInf_mem hne
  have hsa : ∀ x ∈ s, a ≤ x ∧ x ≤ a + f n := fun x hx ↦ Finset.mem_Icc.1 (hs hx)
  have hT : s.image (fun x ↦ x - a) ∈ (Finset.range M).powerset := by
    rw [Finset.mem_powerset]
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    have := hsa x hx
    rw [Finset.mem_range]
    omega
  refine hn _ hT (Finset.mem_image.2 ⟨a, has, Nat.sub_self a⟩) (f n)
    (Finset.mem_image.2 ⟨a + f n, hams, by omega⟩) (by omega) a ?_
  rw [Finset.prod_image fun x hx y hy hxy ↦ by
    have := hsa x hx
    have := hsa y hy
    omega]
  rw [← hprod]
  exact Finset.prod_congr rfl fun x hx ↦ by
    have := hsa x hx
    omega

end Erdos393
