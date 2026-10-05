# Affine properness and closed-immersion descent

The new results descend properties of fixed maps between finitely presented
coefficient models. They are ingredients for item 1 of the W87 handoff;
they do not prove properness or fiber descent for the glued line-sheaf model.

## Contracts

Let `P` and `Q` be finite presentations of `A`-algebras `B` and `C`, and
let `A₀` be a finite type integer subalgebra containing their coefficients.
A map `f` between their `A₀`-models must recover a specified `A`-algebra
map `φ : B →ₐ[A] C`. Each descent theorem constructs a larger finite type
integer subalgebra `S`, retaining any prescribed finite coefficient set.
The resulting map is `integerModelTransportHom P Q h f`, rather than a
new map with an unspecified recovery comparison.

- `exists_integer_model_surjective` descends surjectivity of `φ`.
- `exists_integer_model_closedImmersion` descends a closed immersion on spectra.
- `exists_integer_model_monic_lifts` lifts finite families of monic polynomials.
  Only lower coefficients are chosen; the leading coefficient remains one.
- `exists_integer_model_integral_elements` descends integrality of a finite
  family of target model elements over the transported source map.
- `exists_integer_model_finite` descends finiteness of the ring map.
- `exists_integer_model_affine_proper` descends properness on affine spectra,
  using that affine proper morphisms are finite.
- `integerModelTransportHom_property` preserves any property stable under
  base change through further enlargement, using the actual cartesian square.
- `exists_integer_model_finite_closedImmersions` and
  `exists_integer_model_finite_affine_proper` give one stage for a finite
  family of maps, including an empty family.

Surjectivity is proved by lifting generator preimages and killing their
errors. Integrality is proved by lifting monic witnesses and killing their
evaluations. Recovery maps and coefficient inclusions need not be flat,
faithfully flat, or injective on quotient models.

## Remaining boundary

Properness is not local on the source. Affine charts in a proper curve are
generally not proper over the base, so the affine theorem cannot be applied
to those chart structural maps to establish global properness.

The next separatedness ingredient is to descend the closed immersion of
the diagonal on pairs of affine charts, then assemble the chart tests.
`FiniteClosedImmersionIntegerDescent` provides simultaneous descent for
fixed presentations of those maps. Constructing and recovering their tensor
product coordinate models remains necessary.

General properness needs descent of universal closedness through an inverse
system. Fiber conditions, an ample fiber presentation, Noetherian L2 / 0D2N,
and transfer to the proper-only 0D2S target remain open. Do not add a local
finite-presentation assumption to that target. W87's actual scheme square
and line-sheaf pullback isomorphism remain the recovery contract; this
increment does not strengthen `exists_finite_line_sheaf_descent` itself.
A7–A8 and removal of `Mazur_statement` from the FLT endpoint also remain open.
