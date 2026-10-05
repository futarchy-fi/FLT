# Arbitrary-line degree and an affine section

The W70 modules prove the numerical part of F2 for arbitrary line sheaves
on integral proper curves over a field. They also construct a nonzero section
of a positive tensor power with affine generator open. They do not yet prove
the positive-degree ampleness criterion (Stacks 0B5X).

## Proved contracts

Let `f : X ⟶ Spec k` be proper, let `X` be integral with
`topologicalKrullDim X ≤ 1`, and let `L`, `N` be locally free of rank one.
The degree is the existing `curveSheafDegree`, defined from actual scalar
sheaf cohomology as χ(L) − χ(O).

- `curveEulerCharacteristic_line_tensor` proves
  χ(N ⊗ L) = χ(N) + χ(L) − χ(O).
- `curveSheafDegree_line_tensor` proves deg(N ⊗ L) = deg(N) + deg(L).
- `curveEulerCharacteristic_line_power` proves
  χ(L^n) = n deg(L) + χ(O), including n = 0.
- `curveSheafDegree_line_power` proves deg(L^n) = n deg(L).
- For any nonzero ideal sheaf I, without invertibility of I,
  `curveEulerCharacteristic_ideal_line_power` proves
  χ(I ⊗ L^n) = n deg(L) + χ(I).
- If deg(L) > 0, `exists_nonzero_line_power_affine_section` constructs
  n > 0 and an actual nonzero section s of L^n for which
  `IsAffineOpen (sectionGeneratorOpen (tensorPower L n) s)` holds.

No divisor presentation, numerical additivity hypothesis, global line
trivialization, or record containing the desired conclusion is assumed.

## Construction

`FiniteSchemeLineTwist` trivializes any line on a finite scheme using the
canonical dual tensor inverse and the existing semilocal Picard result.
Twisting any module sheaf by that line then preserves its isomorphism class.
The projection formula transports this to finite closed pushforwards.

`FiniteSupportClosedDescent` constructs an annihilating ideal power for a
coherent finite-support sheaf. The resulting closed subscheme has finitely
many points, so finite type over a field makes it finite. The existing global
closed-descent construction supplies the coefficient sheaf and pushforward
isomorphism. This proves line-twist invariance and positive-cohomology vanishing
for arbitrary coherent finite-support coefficients.

`CurveGenericLineComparison` extends a line trivialization near the generic
point through an actual common ideal power. It constructs a coherent sheaf
with monomorphisms into both O and the line. Both cokernels have finite
support, by the dimension bound. `FiniteSupportEulerCharacteristic` proves
that these errors cancel when computing the change in χ under a line twist.
This gives the arbitrary-line formulas and the nonzero-ideal formula.

For the affine section, choose an affine neighborhood U of the generic point
trivializing L. The ideal of X minus U is nonzero. Its positive-power twists
have unbounded H⁰ by the proved χ formula. Tensoring its inclusion with a line
is injective, so a nonzero twisted section remains nonzero in L^n.
`IdealTwistSectionOpen` shows that this section can only generate off the
ideal's zero locus. Its generator open therefore lies in U, where it is a
principal affine open in a trivialization of L^n.

## Remaining obligations

The affine-section theorem supplies one section. It does not assert that
such generator opens cover X and therefore does not imply `AmpleLineBundle`.
The following proofs are still required, in the assigned order:

1. Finish 0B5X: construct the ideal-twist H¹ transition system for the actual
   nonzero section, prove eventual annihilation of each cohomology class,
   and derive the affine-section-open ampleness criterion from the resulting
   vanishing. Existing open-cohomology comparisons do not themselves provide
   this denominator-clearing result for cohomology classes.
2. Finite-surjective ampleness descent (0B5V), then the component criterion
   (0B5Y). The existing fpqc descent theorem does not cover arbitrary finite
   surjections.
3. F3: apply the criterion to smooth and polygon fibers.
4. L1–L2: arbitrary-base fiber-to-neighborhood ampleness (0D2S), with
   finite-type Z-model approximation and descent. Noetherian-only 0D2N
   does not close this obligation.
5. A7: compatible ample cyclic-level isomorphisms and quotient/presheaf coherence.
6. A8: exact-order rational points, finite étale subgroups, smooth-fiber
   ample level, and prime-to-order generator invariance.

Validation is recorded in the untracked W70 build, per-module lint, complete
originating-declaration audit, and post-merge root-build logs. The full Mazur
removal remains unfinished; these modules do not replace `Mazur_statement`.
