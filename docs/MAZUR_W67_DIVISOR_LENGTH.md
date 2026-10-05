# W67: divisor length, component support, and the canonical exact sequence

This wave proves foundational parts of F1 in `MAZUR_W52_SPLIT.md`.
It does not prove F1 in full, the A6 ample-degree criterion, the arbitrary-base
fiber-neighborhood theorem, A7–A8, or removal of `Mazur_statement`.

## Implemented contracts

`DivisorStalkLength` defines the length of the actual structure stalk modulo
the actual ideal stalk, with values in ℕ∞. Positive length is equivalent to
membership in the original support. This equivalence survives arbitrary
pullback; the numerical lengths need not be preserved by pullback.
Cartier generators compute this intrinsic length as a principal quotient.

`CartierDivisorMultiplicity` proves that actual ideal stalks commute with
products, Cartier multiplicities add, and powers multiply multiplicities.
On a locally Noetherian scheme at a point of codimension at most one the
length is finite, and its natural-number value is positive exactly on support.
These statements do not require a reduced ambient scheme.

`FiniteSchemeLength` uses actual scalar H⁰ of the structure sheaf. A finite
structure morphism makes this vector space finite-dimensional. Its dimension
agrees with its length as a module over the base field, and is positive
exactly when the scheme has a point. Residue-field degrees are included.
The natural-valued definition alone does not assert finiteness.

`CurveDivisorLengthSupport` applies that definition to the actual closed
subscheme of an ideal and to its pullback along a closed immersion. Finiteness
of the original divisor implies finiteness of the restricted divisor. On a
reduced closed component its length is positive exactly when the component
meets the original support. The final theorem quantifies over the actual
irreducible components of the scheme.

`CartierDivisorComponentRestriction` proves that a Cartier ideal pulls back
to a Cartier ideal on an integral scheme if its generic point avoids support.
For a reduced irreducible closed component the hypothesis is precisely that
the component is not contained in the original support. This uses no flatness
assumption on the component immersion.

`DivisorSectionExact` proves injectivity of the actual canonical map
O → O(D) on Cartier charts and then on every open. It constructs its actual
categorical cokernel and proves the resulting module-sheaf sequence short exact.

`DivisorChartCokernel` identifies the cokernel of the actual map on chart
sections with the quotient by the actual Cartier ideal. This is a linear
equivalence and proves equality of module lengths. It is a chart-module
statement, not yet a global identification of the sheaf cokernel.

`CurveEulerCharacteristic` defines χ = h⁰ − h¹ and degree(L) = χ(L) − χ(O).
Both retain the existing scalar sheaf cohomology. Isomorphisms preserve them.
Finite-dimensional exact-sequence algebra proves additivity when the H¹ map
to the quotient is surjective; vanishing H² of the subobject suffices.
The H² vanishing hypothesis is explicit; no geometric vanishing or
Riemann–Roch theorem is established here.

`DivisorCohomologicalDegree` derives coherence and finite cohomology of the
actual canonical cokernel on a proper scheme over a field. If this cokernel
has vanishing H¹, it proves degree(O(D)) = dim H⁰(cokernel). Vanishing H¹ is
explicitly still a hypothesis, not a theorem of this wave. Proper cohomology
finiteness currently restricts this consumer to `Scheme.{0}`; the other
modules retain their universe parameters.

## Remaining proof obligations, in order

1. Complete F1: identify the canonical sheaf cokernel with the closed
   pushforward of O(D) restricted to D. The chart equivalences must respect
   their transition functions; a global trivialization must not be assumed.
   For finite D, prove H¹ of that pushforward vanishes and its H⁰ has the
   same field dimension as H⁰(O_D), using the rank-one module over the finite
   algebra. This removes the remaining hypothesis of the degree formula and
   identifies its right side with `divisorFieldLength`.
2. Complete the component comparison: show finite support cannot contain a
   one-dimensional component, apply Cartier restriction, and identify the
   pulled-back divisor line with the line of the restricted Cartier ideal
   via the canonical ideal-module comparison. This connects the proved
   component length/support theorem to the degree of the restricted line.
3. F2–F3: prove the proper-curve positive-component-degree ampleness theorem
   (Stacks 0B5Y), compare with the project's ample predicate, and supply the
   smooth and polygon fiber consequences.
4. L1–L2: prove arbitrary-base fiber-to-neighborhood ampleness (0D2S), including
   finite-type Z-model approximation. A Noetherian-only result is insufficient.
5. A7: compatible ample cyclic-level isomorphisms, quotient and presheaf.
   A8: exact-order rational point to finite étale subgroup, smooth-fiber ample
   level, and prime-to-order generator invariance.

Every new Lean module has at most 240 lines. Recheck builds and linters one
module at a time; never run the whole-library linter. The untracked W67
handoff records the checked-at time, exact commands and logs, originating
declaration axiom audit, local commit, main merge, and root-build result.
