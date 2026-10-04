# Section ampleness and closed projective presentations

`RelativeAmple.relativelyAmpleLineBundle` proves the forward comparison
between the project's closed-presentation predicate and ordinary relative
section ampleness, for a locally free rank-one sheaf. The structural map's
properness follows from the presentation; it is not an extra assumption in
this direction.

The proof uses actual global coordinate sections of the cocycle-defined
hyperplane sheaf. `coordinateGlobalSection_generatorOpen` identifies their
generator opens with standard projective charts. Pullback along the closed
embedding makes those opens affine. Transport along the coefficient
isomorphism and the tensor-power restriction isomorphism gives the required
positive-power sections on every affine base open.

The underlying transport results apply over arbitrary commutative rings:

- `moduleHomIsoOpen_pullback` identifies the exact pullback of the
  isomorphism open for a morphism between locally free rank-one sheaves.
- `sectionGeneratorOpen_pullGlobal` specializes this to section opens.
- `AmpleLineBundle.pullback_affine` preserves section ampleness under any
  affine scheme morphism, including closed immersions.
- `tensorPowerSection_generatorOpen` says that raising a section to a
  positive tensor power preserves its generator open.
- `AmpleLineBundle.common_degree_section_cover` raises a finite affine
  section cover to one positive degree. Its degree is the product of the
  original positive degrees; the empty family causes no exception.

These statements do not impose flatness, reducedness, or Noetherian
hypotheses. All tensor powers and pullbacks are the project's existing
module-sheaf constructions.

## What the converse requires

A finite affine section cover in one positive degree is not yet a projective
immersion. One must extend finitely many generators of the affine chart
algebras to global sections after further tensor powers, construct their
projective morphism, and prove that it is an immersion. Properness then
upgrades that immersion to a closed one.

`ModuleSectionProjectiveGluing` and `ModuleSectionProjectiveOOne` construct a
projective map and its hyperplane coefficient isomorphism from a specified
generating family. They do not extract the needed family or its immersion
property from `AmpleLineBundle`. The existing `ProjectiveSectionExtension`
results start on projective space, which is the presentation the converse
must construct. `IdealPowerExtensionGluing.exists_ideal_power_extension`
requires a Noetherian scheme; that hypothesis cannot be added to the
requested comparison over arbitrary bases.

General relative ampleness locality, arbitrary base change and fppf descent
also require further proofs. The affine-pullback theorem here is an absolute
ampleness statement and does not assert arbitrary relative base change.
These results do not construct the remaining ample-level quotient or
exact-order rational-point subgroups, and do not remove `Mazur_statement`.
