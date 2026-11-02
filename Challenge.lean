module

public import Mathlib

/-!
# Erdős Problem 393: `f(n) → ∞` assuming the abc conjecture

A solved statement about Erdős Problem 393
([erdosproblems.com/393](https://www.erdosproblems.com/393)). The definitions `ABC.radical` and
`Erdos393.f` and the theorem statement are copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (Apache-2.0), files
`FormalConjectures/Wikipedia/ABC.lean` and `FormalConjectures/ErdosProblems/393.lean` at commit
`a64e959c32c270df4dd0d96d2027481f15750534`, with the same names. The one change: formal-conjectures
writes the hypothesis as `type_of% ABC.abc`, the type of its statement `ABC.abc` of the abc
conjecture. This project cannot import formal-conjectures, so here that type is written out,
copied verbatim from `ABC.abc`, with `open ABC in` so that `radical` resolves.

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
  sorry

end Erdos393
