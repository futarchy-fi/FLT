# Coefficient inverse systems and sheaf recovery

The finite coefficient enlargements of a finite-type integer subalgebra
`S₀ ⊆ A` form a filtered poset. Their rings have colimit `A`, and their
spectra have inverse limit `Spec A`.

For any scheme `Y` over `Spec S₀`, `coefficientModelIsLimit` identifies
`Y ×[Spec S₀] Spec A` as the inverse limit of the base changes of `Y` to
all these coefficient stages. This construction does not require `Y` to
be affine. Its transition maps are affine, and each recovery square is
cartesian.

## Construction

| Module | Result |
| --- | --- |
| `CoefficientStageDiagram` | Directed finite-type enlargements, their inclusion diagram, and a cocone to `A`. |
| `CoefficientStageColimit` | The cocone is colimiting in commutative rings. |
| `CoefficientSpectrumLimit` | The canonical cone from `Spec A` is limiting in schemes. |
| `SchemeBaseChangeLimit` | Base change of a fixed scheme commutes with connected limits; transition and recovery squares are cartesian. |
| `CoefficientModelLimit` | The inverse system and limit of the actual coefficient base changes of a model. |
| `CoefficientModelRecovery` | An existing cartesian recovery map and line-sheaf identification survive every enlargement. |

`coefficientModelRecovery_isPullback` starts with any cartesian square
recovering `X` from `Y` over `A`. It constructs a recovery square at each
finite coefficient stage. `coefficientModelSheafRecoveryIso` uses this same
map to identify the pullback of the enlarged model sheaf with the original
sheaf on `X`. Rank one persists by `coefficientModelSheaf_rankOne`.
These results apply to the model and sheaf produced by W90.

## Missing eventual-property theorem

For a separated, quasi-compact, locally finitely presented
`q : Y ⟶ Spec S₀`, set

```text
b  : Spec A ⟶ Spec S₀       := Spec.map (S₀ ↪ A)
bᵢ : Spec Sᵢ ⟶ Spec S₀     := Spec.map (S₀ ↪ Sᵢ)
qA := pullback.snd q b
qᵢ := pullback.snd q bᵢ
```

The needed implication is `IsProper qA → ∃ i, UniversallyClosed qᵢ`.
The inverse-system and recovery constructions above do not prove it.
The available affine-transition limit APIs descend sections and morphisms
and detect eventual affineness; they do not supply this eventual
universal-closedness theorem. The affine-proper descent theorem cannot
replace it, because affine open subsets of a proper source need not be
proper over the base.

After proving this implication, establish the finiteness hypotheses for
the glued model and combine it with the enlargement recovery results.
Fiber-data descent and approximation for the proper-only 0D2S statement
remain separate obligations; do not add local finite presentation to that
target. The subsequent ordered work is ample-fiber descent, Noetherian
L2 / 0D2N and transfer through approximation, then A7–A8 coherence and the
exact-order rational-point/subgroup bridge.

This increment does not remove `Mazur_statement` from the Fermat endpoint.
