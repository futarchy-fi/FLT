# Finite coefficient line-sheaf recovery

The first recovery boundary in W86 is closed by
`exists_finite_line_sheaf_descent` in `FLT.Mazur.FiniteLineSheafDescent`.
Its hypotheses are a compact separated scheme `X`, a locally finitely
presented morphism `p : X ⟶ Spec A`, a locally free rank-one sheaf `L`, and
a finite set of coefficients to retain.

The conclusion supplies a finite type integer subalgebra `S ⊆ A`, a scheme
`Y` over `Spec S`, a rank-one sheaf `M` on `Y`, and a morphism `f : X ⟶ Y`.
The square with `p` and `Spec A ⟶ Spec S` is cartesian, and the actual
module-sheaf pullback of `M` along this same `f` is isomorphic to `L`.

## Construction

1. `AffineIntersectionProjectionSections` computes chart inverse images
   and pulls ambient coordinates back to `1 ⊗ₜ x`, also on smaller opens.
2. `AffineIntersectionProjectionCocycle` extends the transition units and
   computes inverse-image transitions on every subopen of every chart.
3. `ModuleUnitCocycleCongr` compares sheaves from equal units on pointwise
   equal open families. `AffineIntersectionProjectionSheaf` uses it with
   `Cocycle.pullbackIso` to identify the scalar-extension model sheaf.
4. `FiniteIntersectionScalarColimitRecovery` identifies the scalar colimit
   with `X`, proves its chart squares commute, and computes chart preimages.
5. `OpenChartSectionPullback` and `FiniteIntersectionScalarRecoverySections`
   compare sections on actual open subschemes with the recovered coordinates.
6. `FiniteIntersectionScalarRecoverySheaf` uses coordinate-unit recovery
   to recover the original cocycle sheaf by actual pullback.
7. `FiniteIntersectionGluedRecoveryComparison` identifies the colimit and
   explicit gluing morphisms. `FiniteIntersectionGluedSheafRecovery` transfers
   the sheaf isomorphism to the explicit model used by scheme recovery.
8. `FiniteLineSheafDescent` applies the construction to the genuine cocycle
   of `L`, retaining the finite set of coefficients.

No conclusion about properness or ampleness of the model is asserted.
The local finite-presentation hypothesis belongs to this bounded descent
result; it must not be added to the proper-only 0D2S target.

## Remaining boundary

The next work is descent of properness and fiber data, followed by an ample
fiber presentation, Noetherian L2 / 0D2N, and transfer through inverse-system
approximation. A7–A8 still need compatible level isomorphisms,
quotient/presheaf coherence, and the exact-order rational-point/subgroup bridge.

These declarations do not replace `Mazur_statement` in the FLT endpoint.
