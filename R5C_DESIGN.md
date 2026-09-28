# R5c: integral monogenicity construction

Checked 2026-09-28 against this checkout's mathlib sources.

1. `Mathlib/RingTheory/LocalRing/Etale.lean` proves finite unramified local
   algebras monogenic. It requires `Algebra.FormallyUnramified`; a general
   finite three-adic extension can be ramified, so this cannot prove the target.
2. A direct DVR argument needs no unramified intermediate extension or Hensel
   lifting. Choose a primitive element of the separable residue extension and
   lift its minimal polynomial. For a lift `x` of the element, either `f(x)`
   is a uniformizer, or Taylor expansion shows `f(x + π)` is one. The resulting
   element generates both the residue extension and an element generating the
   maximal ideal. Apply Nakayama over its finite intermediate subalgebra.

Use option 2. The needed APIs exist: residue-field primitive elements,
`Polynomial.exists_mul_sq_add_linear_part_eq_eval_add`, DVR uniformizers,
unit reflection for integral inclusions, Nakayama, and
`IsAdjoinRootMonic.mkOfAdjoinEqTop` / `.powerBasis`.

The intermediate algebra is local because its integral inclusion into the
local target reflects units; its residue map is surjective by construction.
Its maximal ideal maps onto the target maximal ideal since it contains a
uniformizer. Nakayama therefore proves that the inclusion is surjective.

The final specialization must construct a power basis without adding it as
an assumption, then apply `PowerBasis.differentIdeal_eq_annihilator_kaehlerDifferential`.
The Fontaine annihilation/ramification estimate remains outside this leaf.
