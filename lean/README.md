# Lean setup

**Status: the main theorem is proved.** `lake build TensorLB Solution` passes,
and `#print axioms TensorLBSpec.main` reports only `propext`, `Classical.choice`,
and `Quot.sound`. The proof library contains no `sorry` or added axioms.
`Challenge.lean` remains unchanged. Strict Comparator and whole-project
verification remain to be run on Linux: both sandboxed commands exit with code
2 on the macOS development host because `bwrap` requires Linux namespaces.

This project follows the independent Challenge/Solution organization of
[`project-k-median/bound-184`](https://github.com/epfl-thl2/project-k-median/tree/main/bound-184),
using the verification tools bundled with Lean 4.35.0.

## Files and trust boundary

| File | Purpose |
| --- | --- |
| `Challenge.lean` | Reference definitions and manuscript theorem; imports only Mathlib |
| `TensorLB/Definitions.lean` | Independent definitions used by the proof library |
| `TensorLB/Expectation.lean` | Finite-expectation algebra, positivity, Cauchy–Schwarz, and target second moment |
| `TensorLB/Estimation.lean` | Nonempty optimization sets, required boundedness, and correlation/MMSE bounds in `[0, 1]` |
| `TensorLB/WitnessBound.lean` | Moment matching and a second-moment bound imply both estimation conclusions |
| `TensorLB/Parity.lean` | Odd-multiplicity supports and cancellation of repeated sign coordinates |
| `TensorLB/PolynomialSubstitution.lean` | Total-degree bounds for polynomial substitution |
| `TensorLB/Observations.lean` | Tensor-to-parity reduction without increasing degree, and transfer of witness bounds |
| `TensorLB/Fourier.lean` | Boolean character means and orthogonality, including the full sample space |
| `TensorLB/ExpectationSum.lean` | Finite expectation sums and exact second moments of orthogonal combinations |
| `TensorLB/LiftCounting.lean` | Labelled placements and their repeated-label permutation multiplicities |
| `TensorLB/LiftSupport.lean` | Recovering placements from Fourier supports and unaveraged orthogonality |
| `TensorLB/LiftIndex.lean` | Multiset occurrence slots, degree, and factorial multiplicity |
| `TensorLB/OrderedLift.lean` | Averaging over embeddings into distinct background components |
| `TensorLB/Lift.lean` | Multiset witnesses `U_R`, orthogonality, and exact second moments |
| `TensorLB/PolynomialLift.lean` | Linear polynomial lift, its mean, and exact coefficient second-moment formula |
| `TensorLB/SymmetricTensor.lean` | Ordered-tuple counting, canonical symmetric representation, exact energy/norm normalization, and the bound for nonsymmetric tensors |
| `TensorLB/ProductExpectation.lean` | Independence identities for finite product averages and embedded coordinates |
| `TensorLB/GeneratingFunction.lean` | Exact real exponential-moment identities for targets, monomial witnesses, and polynomial lifts |
| `TensorLB/MomentMatching.lean` | Recover all mixed moments from moments of arbitrary linear forms |
| `TensorLB/ExponentialMatching.lean` | Extract moment matching from directional exponential Taylor coefficients |
| `TensorLB/ConnectedSubstitution.lean` | Explicit cubic/quartic connected polynomials, evaluation identity, and hidden-degree bounds |
| `TensorLB/TensorContraction.lean`, `IndexedTensor.lean`, `BlockSubstitution.lean`, `TensorSubstitution.lean` | Orthogonal tensor contraction, arbitrary slot indexing, and summation over substitution blocks |
| `TensorLB/SparseTensor.lean`, `ConnectedTensors.lean`, `SubstitutionBound.lean` | Concrete sparse columns and the proved `5^d` substitution bound, implying the manuscript's `6^d` bound |
| `TensorLB/ComplexCoordinates.lean`, `ComplexConnected.lean`, `LocalResponse.lean` | Complex tilted moments, identity derivative, local analytic inverse, and response germ |
| `TensorLB/MultilinearPolynomial.lean`, `TaylorTruncation.lean`, `RealResponse.lean` | Real homogeneous Taylor polynomials and preservation of finite jets under composition |
| `TensorLB/ResponseJets.lean` | Actual response Taylor identity and unconditional moment matching |
| `TensorLB/SignSymmetry.lean`, `ResponseParity.lean` | Sign equivariance, coefficient incidence parity, and vanishing even-degree cubic terms |
| `TensorLB/LocalNorm.lean` | Incident-weight norm, intersection estimate, and equivalent complete normed parameter space |
| `TensorLB/InverseMajorant.lean`, `SeriesMajorant.lean` | Explicit inverse radius `1 / (16 r²)`, inverse displacement bound, and forward-series bounds |
| `TensorLB/ConnectedSeries.lean` | Connected and inverse germs in the local norm; statement of `UniformConnectedTaylorBound` |
| `TensorLB/MomentReconstruction.lean`, `UniformResponse.lean` | Reconstruct target moments and prove the bounded analytic response from the connected Taylor bound |
| `TensorLB/TreeMajorant.lean`, `RootedTree.lean`, `InteractionTree.lean`, `RootedGraph.lean`, `WeightedCumulant.lean` | Injective tree orientation, leaf summation, weighted cumulant estimate, and absolute exponential bound after dividing by the Taylor factorial |
| `TensorLB/CumulantRelabel.lean`, `RootedOutput.lean` | Relabel occurrence indices, choose an incident output root, and sum over output supports |
| `TensorLB/ConnectedCumulantSeries.lean` | Explicit cumulant multilinear coefficients and their uniform local operator-norm bound |
| `TensorLB/CumulantExtension.lean`, `TiltedObservable.lean`, `TiltedCumulant.lean`, `TiltedDerivatives.lean` | Partition insertion, tilted covariance derivative, and the exact character-cumulant formula for derivatives of every order |
| `TensorLB/SmallCumulants.lean`, `MarkedCumulant.lean`, `CumulantTaylor.lean` | Connected coordinates as marked-spin cumulants and the proved connected-cumulant Taylor expansion |
| `TensorLB/BrokenCircuitCancellation.lean`, `GraphTreeCancellation.lean` | Sign-reversing involution and the bound of the alternating connected-edge sum by tree survivors |
| `TensorLB/CumulantMoments.lean` | Partition cumulants and exact character-moment factorization for disjoint coordinate supports |
| `TensorLB/PartitionRelations.lean`, `OrderedCumulant.lean`, `OrderedPartitionBridge.lean`, `PartitionMobius.lean` | Ordered/ordinary partition equivalence, signed-factorial cancellation, and graph coarsening coefficients |
| `TensorLB/ConnectedPartition.lean`, `CharacterRefinement.lean`, `QuotientCumulant.lean` | Exact cumulant grouping by connected refinement and quotient-graph coefficients |
| `TensorLB/GraphCoefficientBound.lean`, `GraphQuotientTrees.lean`, `TreePartitionCounting.lean`, `CumulantTreeBound.lean` | Spanning-tree coefficient bound, quotient-tree lifting, and the full character-cumulant dependency-tree estimate |
| `TensorLB/Polarization.lean`, `CoefficientGeometry.lean`, `CauchyResponse.lean` | Exact Boolean coefficient extraction, incidence-scaled corners, and Cauchy bounds from a bounded analytic extension |
| `TensorLB/IncidenceEnergy.lean` | Convert coefficient energy to the weighted ordered-tuple sum |
| `TensorLB/ObservationPadding.lean`, `SlotCounting.lean` | Inject observations into equally sized slot blocks and group assignments by multiplicity |
| `TensorLB/MultiplicityEncoding.lean`, `ExcessCounting.lean`, `CoverBound.lean`, `CoefficientArithmetic.lean` | Support/excess encoding, weighted even-cover count, factorial ratios, and uniform rank-scale estimate |
| `TensorLB/ResponseWitness.lean` | Truncated-response polynomial and lift; moment matching conditional on the response Taylor identity |
| `TensorLB/WitnessNorm.lean` | Finite second-moment norms and triangle inequalities |
| `TensorLB/LiftWeights.lean` | Falling-factorial bounds, decreasing lift weights, and exponential correction absorption |
| `TensorLB/RankScale.lean` | Uniform constant and conversion from total rank to background rank |
| `TensorLB/WitnessAssembly.lean` | Geometric summation and both estimation bounds, conditional on witness terms |
| `TensorLB/FinalReduction.lean` | The full challenge conclusion conditional on the explicit `UniformWitnessEstimates` obligation |
| `TensorLB/WitnessEstimate.lean` | Combine coefficient energy and substitution bounds into the required bound on each witness term |
| `TensorLB/CoefficientReduction.lean` | Full challenge conclusion conditional only on `UniformResponseEnergy` for the constructed response |
| `TensorLB/AnalyticReduction.lean` | Full challenge conclusion conditional only on `UniformBoundedResponse` |
| `TensorLB/Main.lean` | Combines the cumulant Taylor theorem and all reductions to prove the full challenge statement |
| `TensorLB.lean` | Proof library entry point |
| `Solution.lean` | Repeats the reference definitions and connects the theorem to the library |
| `config.json` | Comparator target and standard axiom allowlist |
| `ComparatorTest.lean` | Makes `lake test` invoke bundled Comparator with `--paranoid` |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Pinned toolchain and dependencies |

Neither `Solution.lean` nor the proof library imports `Challenge.lean`. The
challenge's `sorry` is an intentional reference placeholder. The library and
solution have no proof placeholders.
The challenge is excluded from the default build targets so whole-library
verification audits the solution rather than the reference placeholder.

Treat the challenge, its import closure, toolchain/dependency pins, build
configuration, and Comparator configuration as reviewed inputs. A change to the
specification needs mathematical review; matching two simultaneously changed
copies would not establish fidelity to the manuscript. Comparator checks the
Lean statement and its definitions, not the translation from informal mathematics.

## Statement correspondence

The checked declaration will be `TensorLBSpec.main`, corresponding to
`thm:main` in [`../tensor_low_degree_k3_k4.tex`](../tensor_low_degree_k3_k4.tex).

- `Sample n m` contains one distinguished sign vector and `m - 1` noise vectors.
  Uniform finite averaging models all signs independently and uniformly.
- `tensor` gives every full tensor entry, including repeated coordinate indices.
  `MvPolynomial` and `totalDegree` specify the full observable polynomial space.
- `target` and `admissibleTarget` encode the singleton, pair, and quartet targets.
- `correlation` and `mmse` are the manuscript's supremum and infimum.
  `TensorLB.Estimation` proves nonemptiness, the required boundedness, and
  `0 ≤ correlation ≤ 1` and `0 ≤ mmse ≤ 1`. The exact MMSE/correlation identity
  is not needed for the witness reduction and is not yet formalized.
- One positive real constant is quantified before `n`, `m`, `ℓ`, `k`, and `A`.
  Requiring positivity is harmless: a finite sufficient constant can be enlarged.
- The theorem includes `n ≥ 4`, `m ≥ 2`, `ℓ ≥ 1`, both allowed tensor orders, and
  the degree/rank bounds. Fractional and negative exponents use `Real.rpow`.

## Completed witness reduction

`IsMomentMatchingWitness n m k ℓ τ A W` states that
`E[W * estimator p] = E[target A * estimator p]` for every polynomial `p`
of total degree at most `ℓ`. The witness is an arbitrary function of the
underlying signs; it need not itself be an observable estimator.

`TensorLB.bounds_of_witness` combines this property with `E[W²] ≤ b` to prove
`correlation² ≤ b` and `1 - b ≤ mmse`. Its correlation proof uses
Cauchy–Schwarz and its MMSE proof completes the square, including estimators
with zero second moment. The theorem does not need attainment of either
optimization. All three foundation modules are free of `sorry` and import
neither `Main` nor `Challenge`.

`TensorLB.Observations` now supplies `reducePolynomial`, which replaces every
full tensor variable by the corresponding parity coordinate or the deterministic
empty-support constant. `reducePolynomial_totalDegree_le` and
`reducedEstimator_reducePolynomial` prove that this preserves the estimator
without increasing degree. `bounds_of_reduced_witness` therefore lets the
witness construction work entirely with `Ω_k`. The converse
realization of every `Ω_k` coordinate as a tensor entry is not needed for this
lower-bound direction and has not been formalized.

`TensorLB.Fourier` proves character means and orthogonality on arbitrary finite
Boolean cubes and transports them to `Sample n m` using an explicit equivalence.
The sample characters retain both component and coordinate labels. In
particular, nonempty targets have mean zero and distinct target characters are
orthogonal.

`TensorLB.Lift` constructs the averaged witnesses `U_R` using a finitely
supported multiplicity function `R`. A slot `(B, i)` records each of the `R B`
copies of character `B`; embeddings place these slots into distinct background
components. `expectation_monomialWitness_mul_eq_zero` proves orthogonality for
different multisets, and `expectation_monomialWitness_sq` proves exactly
`E[U_R²] = R! / (m - 1).descFactorial |R|`. The empty multiset gives one.
These identities follow from checked placement counting, including repeated
labels, rather than treating all injection terms as different Fourier monomials.

`TensorLB.PolynomialLift` extends the construction linearly. Its mean is the
constant coefficient, and `expectation_liftPolynomial_sq` proves
`E[Lift(P)²] = ∑ R ∈ P.support, (P.coeff R)² * R! / (m - 1).descFactorial |R|`.
The lift is defined on all nonempty character labels, which include both
auxiliary sets `Λ_3` and `Λ_4`. These labels describe functions of the hidden
signs and do not enlarge the observation model. When `|R| > m - 1`, no embedding
exists and the total definition gives zero; positivity of the second moment is
proved for the manuscript's range `|R| ≤ m - 1`.

`TensorLB.SymmetricTensor` now proves both normalization identities, including
the canonical symmetric representation of every homogeneous polynomial. Its
bound for a nonsymmetric input tensor accounts for collisions by Cauchy–Schwarz;
it does not assume that different tuple orderings are orthogonal.

`TensorLB.GeneratingFunction` proves the real exponential-moment factorizations
for the target and the lifted polynomial. `MomentMatching` and
`ExponentialMatching` prove that equality of Taylor coefficients in every
direction implies moment matching against all polynomials of the required
degree, including constants. These are exact finite-average identities. The dimension-independent analytic
estimates are supplied by the cumulant and response modules below.

`ConnectedSubstitution` defines the cubic and quartic formulas without choosing
an ordering of a coordinate set. It proves `b_k(φ(t)) = K(t)` for the explicit
moment formulas and the hidden-degree bound `h_k D`, with `h_3 = 3`, `h_4 = 2`.
`ResponseWitness` constructs the truncated polynomial and its lift from a supplied
family of response polynomials. `ResponseJets` discharges its Taylor-identity
hypothesis for the actual terms `responseTerm τ A d`. `LocalResponse` constructs
the complex analytic inverse and response near zero; `RealResponse` restricts to
real parameters and constructs homogeneous polynomials from the Taylor maps.
`ResponseParity` proves that a nonzero coefficient has incidence parity exactly
equal to the target, and that cubic singleton responses have no even-degree terms.
The dimension-independent radius is supplied by `CumulantTaylor` and `UniformResponse`.

`SubstitutionBound.witnessNorm_substituteConnected_le_five` proves a `5^d` norm
bound, which implies the required `6^d` estimate. Its sparse columns need not be
symmetric: their squared norm bounds are `1, 4, 4`, and their tuple supports
identify the output coordinate. Tensor contraction, the lift inequality, and
the triangle inequality account for all substitution choices and collisions.

`FinalReduction.main_of_uniformWitnessEstimates` proves the full quantified
challenge statement from the witness estimate

```lean
∀ τ : ℝ, 1 < τ → ∃ B : ℝ, 0 < B ∧ TensorLB.UniformWitnessEstimates τ B
```

The reduction uses `C = max 12 (576 * B)` to account for the challenge's total
rank `m`, as opposed to the background count `m - 1`. `WitnessEstimate` now
uses the proved substitution bound. `CoefficientReduction` constructs the
required witness from `responseTerm` and reduces the challenge to

```lean
∀ τ : ℝ, 1 < τ → ∃ B : ℝ, 0 < B ∧ TensorLB.UniformResponseEnergy τ B
```

This is equation (32), with one constant uniform in dimension, degree, target,
and tensor order. `AnalyticReduction` now proves this estimate from

```lean
∀ τ : ℝ, 1 < τ → ∃ ρ : ℝ, 0 < ρ ∧ TensorLB.UniformBoundedResponse τ ρ
```

`UniformBoundedResponse` asks for a bounded analytic extension on a closed ball
in the local interaction norm, with radius uniform in dimension and target.
The extension agrees with the constructed response near zero. `UniformResponse`
proves this statement from the uniform connected Taylor bound:

```lean
∃ r : ℝ, 1 ≤ r ∧ TensorLB.UniformConnectedTaylorBound r
```

This is the mixed multilinear estimate in equation (16). The explicit response
radius is `min (1 / (32 r²)) (1 / (16 r τ))`. The inverse series has displacement
at most twice the input norm, and the moment reconstruction is bounded by one
on the resulting ball. Equality with the response germ suffices for the Cauchy
argument, so a separate zero-free continuation of the partition function is not
needed for this construction.

The dependency-tree bound in equation (14) is proved for Boolean character
cumulants, including repeated occurrences. The proof groups moments by connected
refinement, identifies the quotient-graph coefficients by Möbius cancellation,
and counts quotient trees by lifting them to spanning trees with connected
blocks. An injective orientation toward a fixed root connects graph trees to
the rooted interaction sums. Their weighted cumulant estimate and scalar
exponential bound after division by the Taylor factorial are proved. The
output supports are summed by an injective rooted enumeration. The explicit
cumulant series now has operator norm at most `(4 * treeTaylorConstant)^d`.
`CumulantTaylor.connectedCumulantExpansion` proves equation (13), identifying
this series as the Taylor series of `localConnected`. Its proof differentiates
tilted cumulants by inserting an interaction observable, iterates this identity,
and evaluates at the uniform Boolean measure. The singleton, pair, triple, and
quartet partition formulas identify the marked-spin cumulants with the explicit
connected coordinates. Analyticity and the positive convergence radius then
identify the series with the map. `Main` combines this theorem with the response,
coefficient, and witness reductions; no mathematical obligation remains.

The coefficient proof uses exact Boolean polarization and one-variable Cauchy
estimates. Padding each observation with an even number of repeated coordinates
reduces the count to `k d` slots without separate size patterns. An injective
support/excess encoding, multinomial weights, and the exponential series prove
the counting bound. A binomial/descending-factorial identity proves the
factorial ratio with constant `16384`; the resulting energy constant is
`ρ⁻² * (16384 * (16 * exp 1)^4) * exp 4`.
The full theorem uses only the standard Lean axioms. See the validation commands below.

## Proof dependency map

Labels below refer to `tensor_low_degree_k3_k4.tex`. Every dependency needed for
the main theorem is proved.

| Modules | Manuscript correspondence | Dependencies and status |
| --- | --- | --- |
| `Expectation`, `Estimation`, `WitnessBound` | `eq:corr`, `eq:mmse`, final Cauchy–Schwarz/completing-square argument | **Proved**, starting from `Definitions` |
| `Parity`, `PolynomialSubstitution`, `Observations` | `eq:observations` and the final tensor-polynomial reduction | **Proved** in the direction needed for the lower bound; witness transfer uses `WitnessBound` |
| `Fourier` | Character orthogonality underlying `eq:orthogonality` | **Proved** for individual sample characters, using `Expectation` |
| `LiftCounting`, `LiftSupport`, `LiftIndex`, `OrderedLift`, `Lift` | `eq:fourier-witnesses`, `eq:orthogonality` | **Proved**; injection counts and repeated-label factorials give the exact second moment |
| `ExpectationSum`, `PolynomialLift` | Definition of `Lift(P)` and its diagonal coefficient norm from `eq:orthogonality` | **Proved**, using the orthogonal `U_R` family |
| `SymmetricTensor` | `eq:tensor-normalization`, `eq:lift-normalization` | **Proved**, including canonical symmetric representation and the nonsymmetric inequality |
| `ProductExpectation`, `GeneratingFunction` | `eq:tilted-witness`, `eq:tilted-target` | **Proved** for real parameters; finite independence and exact factorization |
| `MomentMatching`, `ExponentialMatching` | Taylor coefficient comparison in `eq:moment-matching` | **Proved**; directional jets recover all polynomial moments |
| `ConnectedSubstitution`, `ResponseWitness`, `ResponseJets` | `eq:substitution`, `eq:witness-definition`, `eq:moment-matching` | **Proved** for the constructed response terms |
| `ComplexCoordinates`, `ComplexConnected`, `LocalResponse`, `RealResponse`, `TaylorTruncation` | Local part of `lem:analytic`, `eq:response`, Taylor truncation | **Proved**; local inverse, response germ, real Taylor polynomials, and jets |
| `SignSymmetry`, `ResponseParity` | `eq:parity` and degree parity in the coefficient argument | **Proved** |
| `LocalNorm`, `TreeMajorant`, `RootedTree`, `InteractionTree` | Local norm and tree summation in `eq:tree-bound` | **Proved**; parent-function counting suffices instead of Cayley's exact formula |
| `CumulantTreeBound` and its partition/graph imports | Dependency-cumulant bound used in `eq:tree-bound` | Full character-cumulant tree bound **proved** |
| `CumulantExtension`, `TiltedObservable`, `TiltedCumulant`, `TiltedDerivatives`, `SmallCumulants`, `MarkedCumulant`, `CumulantTaylor` | `eq:multilinear` / equation (13), and identification needed for equation (16) | **Proved**; explicit cumulant coefficients equal the analytic Taylor coefficients |
| `InverseMajorant`, `SeriesMajorant`, `ConnectedSeries`, `MomentReconstruction`, `UniformResponse` | Uniform response part of `lem:analytic` | **Proved**, using the established uniform connected Taylor bound |
| `Polarization`, `CoefficientGeometry`, `CauchyResponse`, `IncidenceEnergy` | `eq:cauchy` and ordered-tuple energy bound | **Proved**, using the constructed bounded analytic extension |
| `ObservationPadding`, `SlotCounting`, `MultiplicityEncoding`, `ExcessCounting`, `CoverBound`, `CoefficientArithmetic` | Weighted even-cover count and `lem:coefficients` | **Proved**; padding, support/excess injection, multinomial weights, factorial ratio, and exponential correction |
| `TensorContraction`, `IndexedTensor`, `BlockSubstitution`, `TensorSubstitution`, `SparseTensor`, `ConnectedTensors`, `SubstitutionBound` | `eq:map-norms`, `eq:lift-bound` in `lem:lift` | **Proved**, with the stronger factor `5^d` |
| `LiftWeights`, `WitnessNorm`, `WitnessEstimate` | `eq:absorbed-bound` and scalar part of the final witness sum | **Proved**; exponential absorption, falling factorials, triangle inequalities, and conversion from coefficient energy |
| `RankScale`, `WitnessAssembly`, `FinalReduction` | `eq:geometric-bound`, final step of `thm:main` | **Proved**, with one constant uniform in both tensor orders and both conclusions |
| `CoefficientReduction`, `AnalyticReduction`, `UniformResponse`, `Main` | `thm:main` | **Proved**; `connectedCumulantConstant` supplies the uniform Taylor bound used to construct the final constant |

The proved degree range is `ℓ³ ≤ n`; stronger degree ranges remain separate
research questions.

## Development build (macOS or Linux)

Install [Elan](https://github.com/leanprover/elan) and the Lean 4 editor extension.
From the repository root:

```sh
cd lean
lake exe cache get
lake build TensorLB Solution Challenge comparator_test
```

The toolchain file selects Lean 4.35.0. Mathlib is pinned to commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` (release `v4.35.0`); the manifest fixes
transitive dependencies. Keep the manifest in version control. Do not run
`lake update` during routine verification: dependency updates are deliberate
changes to the pinned environment.

A build does not replace strict Comparator verification.

The October 29, 2026 development check completed `lake build TensorLB Solution`
(3011 jobs) without warnings. The axiom audit of
`TensorLB.connectedCumulantExpansion`, `TensorLB.main`, and `TensorLBSpec.main`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; none uses
`sorryAx`. The reference and solution definition blocks and theorem statements
were also compared byte for byte and match.

Both strict commands below were attempted and exited with code 2: their
`bwrap` sandbox requires Linux namespaces. No strict verification pass is
claimed. Sandboxing was not disabled. `Challenge.lean`, the Comparator
configuration, toolchain, manifest, and solution statement remain unchanged.
The reference SHA-256 is
`9865588551f3d4c6deb799e1a5ef6cd5b881c6a05bd2648e99fcc4b2e3b9da7e`.

To reproduce the theorem axiom audit, create a scratch Lean file containing:

```lean
import Solution
#print axioms TensorLB.connectedCumulantExpansion
#print axioms TensorLB.main
#print axioms TensorLBSpec.main
```

Run it with `lake env lean /path/to/audit.lean` from `lean/`.

## Comparator without sandboxing (macOS or Linux)

After the development build above, run inside `lean/`:

```sh
lake comparator --config=config.json --inadvisably-no-sandbox
```

This checks `TensorLBSpec.main` against `Challenge.lean`, including statement
agreement, kernel acceptance, and the configured axiom allowlist. Exit code `0`
means accepted. For the bundled external checkers as well, run:

```sh
lake comparator --config=config.json --paranoid --inadvisably-no-sandbox
```

These commands disable Comparator's `bwrap` sandbox and are intended for a
trusted local checkout. The sandboxed Linux procedure is below.

## Strict verification (Linux)

Use a Linux environment with `bubblewrap` (`bwrap` on `PATH`) and working
unprivileged user namespaces. Some distributions may require their AppArmor
profile for bubblewrap. Run inside `lean/`:

```sh
lake comparator --config=config.json --paranoid
lake check --paranoid
```

For trusted local development, `lake test` is a convenience wrapper for the
first command. For an untrusted replacement proof, start from a fresh trusted
checkout and invoke Comparator directly before building project code. Final
strict verification keeps sandboxing enabled; the sandbox is not available on macOS.

The only permitted axioms are `propext`, `Quot.sound`, and `Classical.choice`.
There are no definition holes. `--paranoid` also requires acceptance from the
bundled external checkers. The configured target is the one combined theorem,
so the same constant must establish both the correlation and MMSE conclusions.

Do not allow `sorryAx` or suppress verification failures. Use a fresh checkout
without restoring project build artifacts. A successful Linux verification run
is still needed; preserve its logs with the verified revision.

See the [Lean 4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
and the [proof-validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
for the bundled tools and their trust assumptions.
