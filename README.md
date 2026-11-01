# Low-degree lower bounds for tensor decomposition

For independent uniform sign vectors $v_j\in\{\pm1\}^n$, observe
$T=\tau v_1^{\otimes k}+\sum_{j=2}^m v_j^{\otimes k}$, with fixed $\tau>1$
and $k\in\{3,4\}$. There is a constant $C_\tau>0$ such that, whenever
$n\ge4$, $m\ge2$, $\ell\ge1$, and

$$
\ell^3\le n,\qquad m\ge C_\tau n^{k/2}\ell^{k/2-1},
$$

estimation of $x_A=\prod_{i\in A}v_1(i)$ by real polynomials of degree at
most $\ell$ in the full tensor entries satisfies

$$
\mathrm{Corr}_{\le\ell}(x_A;T)^2\le n^{-|A|/2},\qquad
\mathrm{MMSE}_{\le\ell}(x_A;T)\ge1-n^{-|A|/2}.
$$

The targets are singletons for $k=3$, and pairs or quartets for $k=4$.
The rank thresholds are thus $C_\tau n^{3/2}\sqrt{\ell}$ and
$C_\tau n^2\ell$, respectively.

The manuscript ([LaTeX](tensor_low_degree_k3_k4.tex),
[PDF](tensor_low_degree_k3_k4.pdf)) gives the mathematical proof.
The Lean theorem is `TensorLBSpec.main`: its reference statement is in
[`Challenge.lean`](lean/Challenge.lean), and its proof is in
[`Solution.lean`](lean/Solution.lean) and the `TensorLB` library. The solution
builds without `sorry`; its axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`. The challenge's `sorry` is an intentional reference placeholder.

## Verify with Comparator (without sandboxing)

With [Elan](https://github.com/leanprover/elan) installed, run from the repository
root. The project pins Lean 4.35.0 and its Mathlib dependencies.

```sh
cd lean
lake exe cache get
lake build TensorLB Solution
lake comparator --config=config.json --inadvisably-no-sandbox
```

Comparator checks that the solution proves the reference statement, is accepted
by Lean's kernel, and uses only the three axioms allowed in
[`config.json`](lean/config.json). Exit code `0` means accepted. The flag disables
Comparator's `bwrap` sandbox, allowing local verification on macOS as well as
Linux; use it with a trusted checkout.

To also run the bundled external proof checkers:

```sh
lake comparator --config=config.json --paranoid --inadvisably-no-sandbox
```

See the [Lean guide](lean/README.md) for the proof dependency map and sandboxed
Linux verification instructions.
