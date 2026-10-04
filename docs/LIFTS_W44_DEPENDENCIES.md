# Lifting gates after the W44 bounded leaves

Proof scope is checked by the named declarations below. The per-module build,
lint and axiom receipts are in the untracked `Scratch/LiftsW44/` handoff directory.
`python3 Scratch/LiftsW44/check.py` verifies those receipts and their source hashes;
it does not rerun Lean. No theorem here removes the admission in `IsHardlyRamified.lifts`.

## Quotient fibre and integral Kummer extraction

`HopfAlgebra.specializedTorsorEquiv` in `HopfTorsorSpecialization`
base-changes the existing canonical Hopf comparison, cancelling the tensor
associators. `HopfAlgebra.pointFiberTorsorEquiv` constructs
F tensor_R F ≃ F tensor_R H, where F = R tensor_B A is the actual point fibre
and H = A/(the extended augmentation ideal). Its second-coordinate coaction
is proved to be induced by the Hopf coaction on A. Finite faithful flatness
comes from the quotient map. These constructions require no supplied comparison.

`HopfFiberPointAction` constructs kernel right translation and the inverse
point difference over every test algebra. `HopfPointFiberPoints` proves that
the tensor-product fibre represents the points lying above the specified
quotient point. `IntegralQuotientFiberTorsor` applies the coordinate comparison
and coaction to W43's actual contracted quotient fibre.

`ConstantCyclicOneFiber` constructs evaluation at one in the canonical constant
cyclic model and specializes the comparison there. This canonical model is over
ZInvTwo. It does not identify the kernel with mu_p, or identify an arbitrary
ordinary quotient over Z_p with the constant model. Those rank-one integral
identifications and coefficient endomorphisms remain the R1a2 gate.

`HopfAlgebra.pointFiber_invariant_iff` in `HopfPointFiberDescent` identifies invariant fibre
functions with scalars by the faithfully flat equalizer. Its unit theorem descends
an invariant unit uniquely to R^*. Its homogeneous-power corollary is conditional
on an already constructed homogeneous unit. It is not the integral Kummer
classification theorem, and it cannot be applied to an arbitrary ordinary
extension until the following leaves are proved:

1. From the actual mu_p coaction, construct the Z/p grading of the fibre algebra.
2. Use the torsor comparison to prove the multiplication maps between graded
   pieces are isomorphisms; in particular prove the degree-one module invertible.
3. Apply the existing local Picard triviality (`CommRing.Pic` in mathlib's
   `RingTheory/PicardGroup.lean`) to construct a generator of that module.
4. Prove that generator is a unit using multiplication with the inverse-degree
   piece, then apply `pointFiber_exists_unit_power` to extract the integral unit.
5. Evaluate the constructed coordinate at a generic fibre point and prove that
   its root-ratio cocycle equals W42's normalized difference cocycle. This is
   R1b3; field Kummer theory alone does not prove the integral assertion.
6. Handle unramified twists and residual coefficient descent (R1c).

The local Picard vanishing API exists. The missing connection is the invertible
homogeneous component derived from this torsor, not a missing theorem saying
that the Picard group of a local ring is trivial. The field Kummer API and
`KummerAlgebra` constructed from an input unit do not supply that connection.

## Representation branch inputs and numerical weights

`OrdinaryFiltrationSplitting` defines splitting by an equivariant linear right
inverse of the actual projection, proves the eigenvector-above-one criterion,
proves equivalence with a zero normalized cocycle for some section, and proves
invariance under simultaneous character twists. This is a representation-level
split test; no weight evaluation is assumed.

The remaining S0a2 leaves are the normalized inertia-character exponents,
niveau-two classification, and the non-peu whole-local cyclotomic branch from
the actual extension class. S0a3 then needs the symmetric-power composition
factors and comparison with the minimum classical weight convention specified
in `LIFTS_NUMERICAL_WEIGHT_CONVENTION.md`. W43's normalized finite table alone
cannot evaluate a representation. No Serre-weight arithmetic evaluation or
arbitrary-prime Raynaud classification has been dispatched.

## Local conditions

`ThreeAdicPlan.flatAt_iff_cofinal_models` in `CofinalFlatModels` proves that actual finite-flat
prolongations on a cofinal family of open coefficient quotients detect
`IsFlatAt`. The proof constructs models on the smaller finite quotients using
the proved coefficient-quotient theorem. Finite residue proartinian coefficients
supply the required finite quotients. This is an integral reduction criterion;
it supplies neither a compatible system of models nor the crystalline
weight-two comparison required by Lp0.

`QuadraticCharacterLift` constructs the fixed sign lift of a residual square-one
field-valued character to any commutative coefficient ring, including continuity
for discrete residual coefficients, reduction, coefficient compatibility and
triviality on every subgroup killed residually. Thus an actual unramified
quadratic residual character gives an unramified quadratic integral character.
Still needed for L20: extract that character from the specified residual
rank-one representation, construct its rank-one `GaloisRep`, and use it in the
framed deformation functor and its local defining ideal. The construction does
not give a quotient map for arbitrary deformations.

`ClosedIdealQuotient` constructs the quotient by any proper closed ideal of a
local proartinian parameter ring with finite residue field. Compactness gives
completeness; images of open ideals give linear topology. `ClosedIdealCondition`
constructs continuous unique factors and proves natural corepresentation of
the maps killing that ideal. This completes the closed-ideal algebraic quotient
leaf of D1a. Identifying the arithmetic local condition with an ideal condition,
and proving its closure/effectivity, remain separate leaves. The admitted
`isCorepresentable_narrowSLiftFunctor` is not used.

The global Selmer dimension, modularity, auxiliary-field, finiteness,
p-nonnilpotence, integral coefficient-order and exact residual-conjugacy gates
remain outside these bounded leaves. The endpoint axiom audit is recorded in
the W44 handoff rather than copied here as a changing status count.
