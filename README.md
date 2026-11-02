# Erdős Problem 393: f(n) → ∞, assuming the abc conjecture

[![CI](https://github.com/veljjanoski/erdos393-palomar/actions/workflows/ci.yml/badge.svg)](https://github.com/veljjanoski/erdos393-palomar/actions/workflows/ci.yml)

A Lean 4 proof of a solved statement about
[Erdős Problem 393](https://www.erdosproblems.com/393), prepared for the
[Palomar](https://palomar-registry.org/) registry (submission form:
<https://submit.palomar-registry.org/>).

Let $f(n)$ be the least $m \geq 1$ such that $n! = a_1 \cdots a_t$ with
$a_1 < \cdots < a_t = a_1 + m$.

- `Erdos393.erdos_393.variants.luca`: assuming the abc conjecture, $f(n) \to \infty$.

The definitions `ABC.radical` and `Erdos393.f` and the statement in `Challenge.lean` are copied
verbatim from [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/ABC.lean` and `FormalConjectures/ErdosProblems/393.lean` at commit
`a64e959c32c270df4dd0d96d2027481f15750534`), where the statement is stated with `sorry`. There
the hypothesis is written `type_of% ABC.abc`; this project cannot import formal-conjectures, so
the hypothesis is the statement of `ABC.abc` written out, copied verbatim.

The proof in `Solution.lean` follows Luca's proof of Proposition 1 in *The Diophantine equation
$P(x)=n!$ and a result of M. Overholt*, Glas. Mat. Ser. III 37 (2002), 269-273
([PDF](https://web.math.pmf.unizg.hr/glasnik/37.2/37(2)-04.pdf)): the abc conjecture implies
that $P(x) = n!$ has only finitely many solutions for every integer polynomial $P$ of degree at
least 2. The proof does not assume Luca's theorem: it formalizes Luca's proof for the polynomials
$\prod_{i \in T}(x+i)$, from the abc conjecture; only the final reduction from $f(n)$ to these
polynomials is specific to Problem 393.

If $f(n) \not\to \infty$, then $f(n) < M$ for some $M$ and infinitely many $n$, so one set of
offsets $T \subseteq \{0, \ldots, M-1\}$ gives $\prod_{i \in T} (a + i) = n!$ for infinitely many
$n$. With $d = |T|$ and $y = d a + \sum_{i \in T} i$ this is $y^d + y^k R(y) = d^d n!$ with
$k + \deg R \leq d - 2$ and $R(0) \neq 0$. The common factor of the two summands divides a power
of $R(0)$. The abc conjecture, with $\operatorname{rad}(n!) \leq 4^n$, then bounds $y$ by an
exponential in $n$, while $y^d \geq n!$.

Not formalized: Luca's theorem for general polynomials $P$, any unconditional statement about
$f(n)$, and the much stronger conditional bound $f(n) \geq n - O(\log n)$ discussed on the
[erdosproblems.com forum](https://www.erdosproblems.com/forum/thread/393) for Problem 393.

## Repository map

- `Challenge.lean`: the statement (with `sorry`) a reader audits.
- `Solution.lean`: the same declaration with a proof.
- `comparator.json`: the declarations `lake comparator` checks.
- `formalization.yaml`: provenance, authorship, automation and review metadata.
- `scripts/`, `test/`, `Gemfile*` and `.github/workflows/ci.yml` come from
  [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate).

Build with `lake exe cache get && lake build`; check with `scripts/verify-comparator.sh` (Linux,
needs `bwrap`).

## Licence

Apache License 2.0, see `LICENSE`. The definitions and statement copied from formal-conjectures
are also under Apache-2.0.
