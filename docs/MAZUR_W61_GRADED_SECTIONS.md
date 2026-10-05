# W61: the full graded section module and its multiplication

The five modules below construct all section degrees, their direct sum,
the actual tensor-product multiplication, and flat affine base change of
the underlying module. They do not yet construct a commutative graded
ring or its canonical Proj morphism. D4a–b and A6 remain incomplete.

## Contracts

| Module | Construction or theorem |
| --- | --- |
| `SectionGradedMultiplication` | Bilinear product of arbitrary sections of actual tensor powers, compatibility with restriction and scalars, product of pure powers |
| `SectionGradedSum` | Direct sum over every natural degree; bilinear multiplication, homogeneous formula, distributivity, uniqueness and restriction compatibility |
| `ScalarExtensionDirectSum` | Scalar extension distributes over arbitrary direct sums along a specified ring map; forward and inverse homogeneous formulas |
| `LinePowerSectionBaseChange` | Flat affine base change in each degree, composed with the actual tensor-power comparison; pure scalar tensor and pure-power formulas |
| `SectionGradedBaseChange` | Flat affine base change of the full direct sum, with a formula on each homogeneous insertion |

Multiplication and restriction work for arbitrary module sheaves and opens.
No local freeness or quasi-coherence assumption is needed for these operations.
The pure-power formula includes degree zero.

For base change, let `X` be quasi-compact and separated, let `S` and `T`
be affine, let `g : T → S` be flat, and take an actual cartesian square
with `f : X → S`, `p : P → X` and `q : P → T`. For a line bundle `L`,
the comparison is an isomorphism of modules over the global functions on `T`:

```
Γ(T) ⊗_{Γ(S)} (⊕ n : ℕ, Γ(X, L^n)) ≅ ⊕ n : ℕ, Γ(P, (p*L)^n).
```

There is no truncation, finite-degree bound, Noetherian assumption, or
reducedness assumption. Surjectivity of `g` is not needed for this comparison.
The result uses the universe-zero global-section base-change infrastructure.
The source `X` need not be affine. Each homogeneous pure tensor is sent to
its scalar multiple of the actual adjunction-unit pullback, transported
by `tensorPowerIso`. No field assumes a descent or ampleness conclusion.

## Mathlib Proj boundary

The pinned Mathlib has:

- `AlgebraicGeometry.Proj.map` in `ProjectiveSpectrum/Functor.lean`:
  a morphism between two Proj schemes from a graded ring homomorphism,
  with the hypothesis that the target irrelevant ideal is contained in
  the image of the source irrelevant ideal.
- `Proj.map_preimage_basicOpen`, `Proj.awayι_comp_map`, and affine
  degree-zero homogeneous-localization charts in `ProjectiveSpectrum/Scheme.lean`.
- `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`
  in `Morphisms/FlatDescent.lean`: fpqc descent of open immersions already exists.

These APIs do not directly supply a morphism from an arbitrary scheme to
Proj of its section ring. Applying `Proj.map` to a finite polynomial ring
would still not construct that canonical map.

## Remaining proof obligations

1. Prove associativity and unit coherence for exponent-addition isomorphisms
   on arbitrary local tensor sections. Prove commutativity for a line bundle,
   then equip the direct sum with a `CommRing` and its actual grading.
2. Prove compatibility of multiplication with `tensorPowerIso` and the
   scalar-extension comparison. The current comparison is a module
   isomorphism; it is not yet an algebra isomorphism.
3. Define the canonical map on section-generator opens by ratios in
   degree-zero homogeneous localizations, prove agreement on overlaps,
   and glue. A generated positive power supplies the required cover.
4. Identify its base-change square, prove the section-ampleness criterion,
   and apply the existing fpqc open-immersion descent instance. Assemble D5.
5. Complete the fibre criterion and A7–A8 as specified in the W60 handoff.

`mul_power` concerns two powers of the same section. It does not establish
associativity or commutativity on arbitrary sections: powers of global
sections are not assumed to span every tensor-power section space.

## Rechecking

Build with `LEAN_NUM_THREADS=2 lake build MODULE` for each listed module;
lint with `lake exe runLinter MODULE`, sequentially. The untracked W61
validation scripts and logs contain the exhaustive originating-declaration
axiom audit, Proj API probe, ring-structure boundary probe, root build,
and the endpoint axiom check. `W61_CHECK_SOURCE.py` reports timestamps and
checks the scope, line caps, successful logs and local commit ancestry.
