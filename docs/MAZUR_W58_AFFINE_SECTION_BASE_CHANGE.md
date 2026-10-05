# G1-A6: affine sheaf section base change

This supplies the affine sheaf comparison required by D2a–D2b of
`MAZUR_W57_FPQC_DESCENT_SPLIT.md`, together with its section-restriction
formula. It does not prove fpqc ampleness descent or non-affine flat base
change of global sections.

## The canonical map

For any morphism `p : Y ⟶ X`, module sheaf `M`, and open `U` of `X`,
`ModuleSectionBaseChange.comparison p M U` is the scalar-extension transpose
of the actual sheaf pullback adjunction unit. Its pure-tensor formula is

```text
b ⊗ m ↦ b • ((pullbackPushforwardAdjunction p).unit.app M).app U m.
```

The target is the sections of the actual sheaf `(pullback p).obj M` on
`p ⁻¹ᵁ U`. No presheaf pullback or replacement sheaf occurs in this definition.

For affine `X,Y` and quasi-coherent `M`, the comparison at `⊤` is an
isomorphism. There is no flatness, finite-presentation, reducedness,
Noetherian, line-bundle or trivialization hypothesis.

## Proof and capped modules

| Module under `FLT.Mazur` | Role |
| --- | --- |
| `AffineModulePullbackSections` | On spectra, identify the two left adjoints using the natural identification of pushforward sections with restriction of scalars; prove the unit and pure-tensor formulas |
| `AffineModuleGlobalSections` | Transport tilde to an arbitrary affine scheme; prove its actual global-section adjunction, invertible unit, and invertible counit for quasi-coherent sheaves |
| `AffineQuasiCoherentBaseChange` | Construct the affine sheaf and section isomorphisms over the actual global-section rings; prove the adjunction-unit formula |
| `ModuleSectionBaseChange` | Define the canonical map for all schemes and opens; identify the affine map with the isomorphism; prove module naturality and restriction compatibility |
| `PushoutModuleScalars` | Cancel a ring pushout in module scalar extension, retaining the structural maps in the tensor formula |
| `AffineCartesianSectionScalars` | Apply the ring pushout to an actual affine cartesian square, then use the sheaf comparison; prove the pure-tensor and restriction formulas |

Each module must remain at most 240 lines, including headers. Recheck with
`wc -l FLT/Mazur/MODULE.lean`, `LEAN_NUM_THREADS=2 lake build FLT.Mazur.MODULE`,
and `lake exe runLinter FLT.Mazur.MODULE`, one module at a time.

The proof uses Mathlib's existing quasi-coherent reconstruction theorem,
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`. It does not add a
reconstruction or base-change conclusion as an assumption.

## Cartesian scalars

For an actual cartesian square

```text
P --p--> X
|        |
q        f
|        |
v        v
T --g--> S
```

with `X,T,S` affine, `AffineCartesianSectionScalars.sectionsIso h M` has type

```text
Γ(T,O) ⊗[Γ(S,O)] Γ(X,M) ≅ Γ(P,p* M),
```

as modules over `Γ(T,O)`. Affineness of `P` is derived from the square.
The source action is through `f.appTop`; the target action is through
`q.appTop`. The formula sends `b ⊗ m` to `q.appTop b • pullback(m)`.
`sectionsIso_restrict` identifies its restriction over `p ⁻¹ᵁ U` with
`ModuleSectionBaseChange.comparison p M U` applied to the restricted factors.

## Remaining bridge to the finite equalizer

`ModuleSectionBaseChange.comparison_restrict` proves the restriction square
on pure tensors for every pair of opens and any scheme morphism. It is not
yet the whole D2c chart interface needed by D2d:

1. For an affine open `U` of a non-affine `X`, transport the cartesian
   comparison for the scheme `U.toScheme` to the original sheaf sections
   `Γ(X,M)(U)` and `Γ(P,p* M)(p ⁻¹ᵁ U)`. Prove compatibility with the
   **actual** `modulePullbackOpenIso` and its adjunction-unit sections.
   Transporting abstract isomorphisms without this formula is insufficient.
2. Do this for chart intersections, using separatedness over the affine
   base to retain affineness. Identify the resulting maps with the
   restrictions used by `FlatSectionEqualizer.tensorSectionDifference`.
3. Combine the local comparisons with a finite affine cover and
   `FlatSectionEqualizer.flatSectionEqualizer`. This must prove the actual
   global map is invertible for quasi-compact separated `X` and a flat base
   change. None of the present modules assert that non-affine theorem.

Then D3–D5 still require evaluation base change, faithful-flat stalk
reflection, the full graded section-algebra Proj map and ample criterion,
and descent of the open immersion. The arbitrary-base fibre criterion
and A7–A8 remain separate mathematical obligations.

The target remains removal of `Mazur_statement` from
`PNat.pow_add_pow_ne_pow`. These local comparison results do not claim that
endpoint change. Timestamped build, lint, axiom and endpoint checks belong
in the untracked W58 handoff and logs, not in a write-once status claim here.
