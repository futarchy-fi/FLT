/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RootsOfUnityAlgebra
public import FLT.Mazur.MultiplicativeGroupScheme
public import FLT.Mazur.FiniteLocallyFreeDegreeCover
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The finite locally free roots-of-unity subgroup

The spectrum of the character algebra is an actual commutative group scheme.
Its Laurent coordinate map gives a closed subgroup of the multiplicative group,
finite locally free of degree n without inverting n in the base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj
open scoped LaurentPolynomial

namespace FLT.Mazur.RootsOfUnityScheme

universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The diagonalizable group with character group Z/n. -/
abbrev model : Over (Spec (.of R)) :=
  (Spec (.of (RootsOfUnityAlgebra.Coordinate R n))).asOver (Spec (.of R))

instance commGrpObj : CommGrpObj (model R n) := inferInstance

/-- The subgroup map induced by reduction of Laurent exponents modulo n. -/
def inclusion : model R n ⟶ MultiplicativeGroupScheme.gm R :=
  ((bialgSpec (.of R)).map (CommBialgCat.ofHom (RootsOfUnityAlgebra.restriction R n)).op).hom

instance inclusion_isMonHom : IsMonHom (inclusion R n) := by
  unfold inclusion
  infer_instance

/-- The underlying inclusion is the spectrum of the actual Laurent quotient map. -/
theorem inclusion_left :
    (inclusion R n).left =
      Spec.map (CommRingCat.ofHom (RootsOfUnityAlgebra.restriction R n).toAlgHom.toRingHom) := rfl

instance inclusion_closed : IsClosedImmersion (inclusion R n).left :=
  IsClosedImmersion.spec_of_surjective _ (RootsOfUnityAlgebra.restriction_surjective R n)

instance inclusion_mono : Mono (inclusion R n) :=
  Over.mono_of_mono_left _

/-- The subgroup carrier has degree n in every residue characteristic. -/
theorem degree [NeZero n] : FCurve.FiniteLocallyFreeDegree (model R n).hom n :=
  FCurve.finiteLocallyFreeDegree_spec_of_basis R _ n (RootsOfUnityAlgebra.basis R n)

instance finite [NeZero n] : IsFinite (model R n).hom := (degree R n).1

instance flat [NeZero n] : Flat (model R n).hom := (degree R n).2.1

instance locallyOfFinitePresentation [NeZero n] :
    LocallyOfFinitePresentation (model R n).hom := (degree R n).2.2.1

/-- Arbitrary scheme base changes retain the degree, including nonreduced tests. -/
theorem baseChange_degree [NeZero n] {S : Scheme.{u}} (f : S ⟶ Spec (.of R)) :
    FCurve.FiniteLocallyFreeDegree
      (CategoryTheory.Limits.pullback.snd (model R n).hom f) n :=
  (degree R n).baseChange f

end FLT.Mazur.RootsOfUnityScheme
