# Finite presentation of the separated coefficient model

`exists_finite_presentation_separated_line_sheaf_descent` constructs a
separated, quasi-compact, locally finitely presented model over a finite-type
integer subalgebra. It retains the cartesian recovery square and the actual
pullback isomorphism for the descended line sheaf.

Its hypotheses are those of W90's separated descent theorem: the source is
compact and separated, its morphism to `Spec A` is locally finitely
presented, and the sheaf is locally free of rank one. A prescribed finite
set of elements of `A` is included in the coefficient subalgebra.

| Module | Result |
| --- | --- |
| `AffineIntersectionFinitePresentation` | Finite affine gluing is compact and quasi-compact over its base; finitely presented chart algebras give a locally finitely presented structural map. |
| `FinitelyPresentedIntersectionCocycleModel` | The closed-overlap and unit-cocycle construction retains finite presentation of every chart algebra. |
| `FinitelyPresentedLineSheafDescent` | The separated model and line-sheaf recovery include the required finiteness properties. |
| `CoefficientModelFiniteness` | Separatedness, quasi-compactness, and local finite presentation persist at every coefficient enlargement; each finite-type stage model is Noetherian. |

The previous cocycle-model statement hid the chart presentation evidence
inside its proof. The strengthened construction exposes that evidence
before forming the gluing. Compactness follows from the finite affine open
cover, and local finite presentation is checked on those same charts.

The coefficient inverse system from W91 can therefore start with a model
that has all three hypotheses required for eventual properness. Its existing
cartesian and line-sheaf recovery results apply at every enlarged stage.
`coefficientModel_isProper_iff` identifies universal closedness as the
remaining condition for a separated finite-type stage.

## Remaining foundation

For the resulting `q : Y ⟶ Spec S₀`, with `S₀` finite type over the integers,
the missing implication is still:

```text
IsProper (Y ×[Spec S₀] Spec A → Spec A)
  → ∃ Sᵢ ⊇ S₀, Sᵢ finite type over ℤ and
      UniversallyClosed (Y ×[Spec S₀] Spec Sᵢ → Spec Sᵢ).
```

The new finiteness lemmas do not prove this implication. The available
inverse-limit API provides eventual affineness and section/morphism descent.
The affine-proper descent result also does not apply to general source
charts: an affine open subset of a proper scheme need not be proper.

After this foundation, the ordered work is properness with fiber-data
descent, approximation for the proper-only 0D2S target, ample-fiber descent
and Noetherian L2 / 0D2N, then A7–A8 coherence and the exact-order bridge.
Local finite presentation must not be added to the proper-only target.
