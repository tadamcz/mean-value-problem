> **Note.** This entire repository was machine-written by AI assistants at the direction of Tom Adamczewski. The Lean proof itself was written by GPT-6 Astra, as described below.

# Smale's mean value conjecture (K = 1): disproof

[![CI](https://github.com/tadamcz/mean-value-problem/actions/workflows/ci.yml/badge.svg)](https://github.com/tadamcz/mean-value-problem/actions/workflows/ci.yml)

Machine-checked disproof of the [Smale's mean value conjecture (K = 1)](https://en.wikipedia.org/wiki/Mean_value_problem) in Lean 4 with Mathlib, found autonomously by a
pre-release version of **GPT-6 Astra** (OpenAI) in an evaluation run by Epoch AI over the open problems of Formal Conjectures'
Wikipedia collection. In this repository, `Challenge.lean` is the small statement a reader audits, `Solution.lean` proves it, and
[Comparator](https://github.com/leanprover/comparator) checks that the two statements coincide and that only the standard axioms
are used.

## The result

Smale (1981) proved that for every complex polynomial `p` of degree `d ≥ 2` and every `z ∈ ℂ` there is a critical point
`c` of `p` with `|p(z) − p(c)|/|z − c| ≤ 4 |p'(z)|`, and conjectured that the constant `4` can be replaced by `1` (or
even by `(d−1)/d`, which is attained by `z^d − dz`). The constant has been lowered to `4 − O(1/d)` (Beardon–Minda–Ng,
Fujikawa–Sugawa and others), the conjecture is known for small degrees and for polynomials whose roots are all real or
all of the same modulus (Tischler), and it is one of Smale's problems for the 21st century.

The conjecture with `K = 1` is **false**: there is a polynomial `p` with `p(0) = 0`, `p'(0) = 1` and `|p(c)/c| > 1` at
every critical point `c`, so at `z = 0` no critical point satisfies the inequality. Formally, the theorem proved is the
negation of the Formal Conjectures statement `MeanValueProblem.mean_value_problem`. The witness has very large,
unspecified degree and violates the bound by a small margin, which is consistent with Smale's `K = 4` theorem, with the
low-degree verifications, and with the known asymptotics of the best constant.

The compared declaration, from `Challenge.lean`:

```lean
theorem mean_value_problem.disproof : ¬ (∀ (p : Polynomial ℂ), 2 ≤ p.degree → ∀ (z : ℂ) (K : ℝ),
    ∃ c : ℂ, p.derivative.eval c = 0 ∧
      ‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ ‖p.derivative.eval z‖) := by
  sorry
```

The benchmark file states the conjecture and its negation `….disproof`, both with `sorry`, and the model fills in exactly one.
Here the compared theorem is the negation, written out explicitly instead of via `type_of%` (see *Edits* below).

**Fidelity.** The compared theorem is exactly the negation of the Formal Conjectures statement, restated explicitly: for every `p :
Polynomial ℂ` with `2 ≤ p.degree`, every `z : ℂ` and every `K : ℝ`, there is `c` with `p.derivative.eval c = 0` and
`‖p.eval z - p.eval c‖ / ‖z - c‖ ≤ ‖p.derivative.eval z‖`. The parameter `K` is unused in the Formal Conjectures
statement (the constant is fixed at 1). Lean's convention `x / 0 = 0` makes the case `p'(z) = 0` hold trivially with `c
= z`, so the formal conjecture is if anything weaker than the informal one; the counterexample uses `z = 0` with `p'(0)
= 1`, so it refutes the informal conjecture as stated in the literature.

## Provenance

**Run.** The proof was produced in the evaluation run `wikipedia-vega-1000usd` of Epoch AI's LeanOpenProblems harness (2026-09), in which a pre-release version of GPT-6 Astra attempted, autonomously and once each, all 222 research-open statements of the `Wikipedia` collection of Formal Conjectures under a budget of $1,000 and 96 hours of working time per statement. The agent works in a
network-isolated Docker container with a Lean 4 toolchain (v4.27.0) and Mathlib, SageMath and Python; its final `Spec.lean` is
checked in a separate pristine container by Comparator against the trusted statement, permitting only `propext`, `Quot.sound` and
`Classical.choice`. The harness is public at [epoch-research/LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems); the dataset used here lives on its
`wikipedia-dataset` branch. No human saw or steered the proof search.

**Cost and time.** The attempt used 0.05 million input, 2.2 million output, 68 million cache-read and 7.1 million cache-write tokens, which
cost $265 at GPT-6 Astra's standard rates as provided by OpenAI on 3 September 2026 ($10 / $50 / $1 / $12.50 per million
input / output / cache-read / cache-write tokens); the harness metered it at stand-in GPT-5.6 Sol prices. The agent's
working time (harness working_time, excluding waits on API retries and rate limits) was 15.0 hours.

**Statement.** The definitions and the statement come verbatim from [`FormalConjectures/Wikipedia/MeanValueProblem.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9cbe1d3c12998c786b7c2cd99ce28a21b6631f66/FormalConjectures/Wikipedia/MeanValueProblem.lean) in
Google DeepMind's Formal Conjectures at commit `9cbe1d3c1299`, where the problem is stated with `sorry` as open. The harness isolated the
statement into [`apn/data/wikipedia/Isolated/MeanValueProblem.mean_value_problem.lean`](https://github.com/epoch-research/LeanOpenProblems/blob/0ef96d7b12cfa96a93761b4bba1c635f4546c5ca/apn/data/wikipedia/Isolated/MeanValueProblem.mean_value_problem.lean) (with a `.disproof` negation added), and that file
is exactly what the model received.

## Proof account

The following account was machine-generated from the Lean proof (it refers to the actual declarations) and has not been checked
by a human mathematician; Comparator establishes only that the compared theorem is proved.

Let `q(z) = (z^4 + 64i)/√4097` and `K = {|q| ≤ 1}`, a compact non-convex set (four petals joined at a narrow hub) with
an explicit conformal map `W : K → 𝔻`, `W^4 = (1+64i) z^4 / (1 + 64i z^4)`, and inverse `Φ`. The base point `z_0 = 33/32
+ 2i` is interior to `K` but lies on the outward normal to `∂K` at the boundary point `1`, so `J(w) = (Φ(w) −
z_0)/Φ'(w)` has `J(1) = −1/32 < 0` and `Re J'(1) > 0`. For a Blaschke factor `B_r`, `r = 1 − t^2`, the model `F(z) = (z
− z_0) B_r(W z) / B_r(W z_0)` has `F(z_0) = 0`, `F'(z_0) = 1`, `|F(z)/(z − z_0)| > 1` on `∂K`, and no critical point in
`K` (`disk_exclusion`: the two critical points near `1` are pushed just outside the disk). Power-series approximation
gives a polynomial `g` with the same properties for `(X − z_0) g` (`exists_base_polynomial`); adding the primitive of
`q^{2n}` vanishing at `z_0` forces all `8n` critical points into a thin collar around `∂K` where `|g| > 1 + δ`, while
the primitive contributes only `O(1/n)` (`eventually_allBadWitness_perturbation`). Translating `z_0` to `0` and
normalising `p'(0) = 1` yields `exists_allBadWitness`; `weak_mean_value_false` derives the negation.

## Repository layout

- `Challenge.lean` — the statement surface: definitions copied verbatim from the benchmark statement and the compared theorem with `sorry`.
- `Solution.lean` — imports the proof module, in whose environment the compared theorem is proved.
- `MeanValueProblem.lean`, `MeanValueProblem/Resolutions/MeanValueProblem.lean` — the AI-written proof module (the model's final `Spec.lean`, edited as listed below).
- `comparator.json` — Comparator configuration naming `MeanValueProblem.mean_value_problem.disproof`.
- `formalization.yaml` — structured metadata (provenance, sources, classification, automation, review) in the mathlib-initiative v0.4 format.
- `provenance/` — SHA-256 of the run's output file and the unified diff from it to the module here.
- `scripts/verify-comparator.sh` runs the pinned Comparator, lean4export, NanoDa and Landrun locally (Linux); `scripts/validate-formalization.rb` checks the metadata file.
- `.github/workflows/ci.yml` — builds the project and runs Comparator.

## Edits relative to the run's output

The proof module is the model's final `Spec.lean`, verified in the harness, with only the following mechanical changes (exact diff in
`provenance/`; SHA-256 of the original: `78e412449a61946b56fa1c5965bf9d00bea93c5dc18ae3831566b09cc947e5eb`). The toolchain was moved from Lean v4.27.0 / Mathlib (via Formal Conjectures at commit
`9cbe1d3c`) to Lean v4.28.0 / Mathlib v4.28.0.

- line 1: `import FormalConjecturesUtil` → `import Mathlib`
- removed the sorry'd stub of the original conjecture `mean_value_problem` (lines 27–33 of the original) together with its docstring
- restated `MeanValueProblem.mean_value_problem.disproof` explicitly (the original used `¬ (type_of% @MeanValueProblem.mean_value_problem)`, which referenced the removed stub) and added a docstring

## Verification

```sh
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # Linux: Comparator + NanoDa under Landrun
```

CI runs the same checks. The compared theorem depends on no `sorry` and on no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`.

## Licence and attribution

This repository snapshot is licensed under the Apache License 2.0 (see `LICENSE`). The benchmark statement it reproduces is
from Formal Conjectures, © The Formal Conjectures Authors, Apache-2.0 (see `NOTICE`). Cited papers, Wikipedia and Mathlib retain
their own licences.
