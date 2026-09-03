import Mathlib

/-!
# Smale's mean value conjecture (K = 1): disproof

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Mean_value_problem)

Smale (1981) proved that for every complex polynomial `p` of degree `d ≥ 2` and every `z ∈ ℂ`
there is a critical point `c` of `p` with `|p(z) − p(c)|/|z − c| ≤ 4 |p'(z)|`, and conjectured
that the constant `4` can be replaced by `1` (or even by `(d−1)/d`, which is attained by `z^d −
dz`). The constant has been lowered to `4 − O(1/d)` (Beardon–Minda–Ng, Fujikawa–Sugawa and
others), the conjecture is known for small degrees and for polynomials whose roots are all real or
all of the same modulus (Tischler), and it is one of Smale's problems for the 21st century.

The conjecture with `K = 1` is **false**: there is a polynomial `p` with `p(0) = 0`, `p'(0) = 1`
and `|p(c)/c| > 1` at every critical point `c`, so at `z = 0` no critical point satisfies the
inequality. Formally, the theorem proved is the negation of the Formal Conjectures statement
`MeanValueProblem.mean_value_problem`. The witness has very large, unspecified degree and violates
the bound by a small margin, which is consistent with Smale's `K = 4` theorem, with the low-degree
verifications, and with the known asymptotics of the best constant.

This file is the small statement surface a reader should audit: the theorem
`MeanValueProblem.mean_value_problem.disproof` below is the compared declaration, and the
conjecture is refuted (its negation is proved) in `Solution.lean` and the module it imports. Only
the theorem's `sorry` is filled in there.

The definitions and the statement inside this file are copied verbatim from
`FormalConjectures/Wikipedia/MeanValueProblem.lean` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (Google DeepMind, Apache-2.0) at commit
`9cbe1d3c12998c786b7c2cd99ce28a21b6631f66`, which is the statement the AI system was given (isolated statement file
`apn/data/wikipedia/Isolated/MeanValueProblem.mean_value_problem.lean` on the `wikipedia-dataset` branch of [LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems) at commit
`0ef96d7b12cfa96a93761b4bba1c635f4546c5ca`).
-/
namespace MeanValueProblem

/--
**Disproof of Smale's mean value conjecture with constant 1.** The bracketed statement is the conjecture
`mean_value_problem` exactly as formalized in Formal Conjectures: given a complex polynomial $p$ of degree
$d ≥ 2$ and a complex number $z$, there is a critical point $c$ of $p$ such that
$|p(z)-p(c)|/|z-c| ≤ |p'(z)|$ (the parameter `K` is unused there). This theorem says that is false: some
polynomial $p$ and point $z$ violate the inequality at every critical point.
-/
theorem mean_value_problem.disproof : ¬ (∀ (p : Polynomial ℂ), 2 ≤ p.degree → ∀ (z : ℂ) (K : ℝ),
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ ‖p.derivative.eval z‖) := by
  sorry

end MeanValueProblem
