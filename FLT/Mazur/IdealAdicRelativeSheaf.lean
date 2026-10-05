/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisSheafExtension
public import FLT.Mazur.IdealAdicRelativePresheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sheaves of relative graded algebras

Sheafify the actual affine tensor algebras and their actual coefficient
quotients on the affine site, then extend to the whole scheme. The quotient
is an epimorphism of sheaves. No equality between arbitrary-open sections
and the infinite direct sum of coefficient sections is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Sheafification and extension of commutative rings from the actual affine basis. -/
def affineRingSheafification :
    (X.affineOpensᵒᵖ ⥤ CommRingCat.{u}) ⥤
      Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  presheafToSheaf (AffineBasis.topology X) CommRingCat ⋙
    (AffineBasis.sheafEquivalence X CommRingCat).functor

/-- The relative graded ring sheaf associated to the actual tensor algebras. -/
def relativeRingSheaf :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (affineRingSheafification (X := X)).obj (relativeAffinePresheaf J f)

/-- The coefficient ring sheaf associated to the actual degreewise coefficients. -/
def coefficientRingSheaf :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (affineRingSheafification (X := X)).obj (coefficientAffinePresheaf J f)

/-- The original relative quotient descends to a morphism of ring sheaves. -/
def relativeSheafQuotient : relativeRingSheaf J f ⟶ coefficientRingSheaf J f :=
  (affineRingSheafification (X := X)).map (relativeAffineQuotient J f)

instance relativeAffineQuotient_app_epi (U : X.affineOpensᵒᵖ) :
    Epi ((relativeAffineQuotient J f).app U) :=
  ConcreteCategory.epi_of_surjective _ (relativeAffineQuotient_surjective J f U)

instance relativeAffineQuotient_epi : Epi (relativeAffineQuotient J f) :=
  NatTrans.epi_of_epi_app _

/-- The actual relative quotient remains an epimorphism after gluing. -/
instance relativeSheafQuotient_epi : Epi (relativeSheafQuotient J f) := by
  change Epi ((AffineBasis.sheafEquivalence X CommRingCat).functor.map
    ((presheafToSheaf (AffineBasis.topology X) CommRingCat).map
      (relativeAffineQuotient J f)))
  infer_instance

/-- On the affine site the original quotient is locally surjective. -/
instance relativeAffineQuotient_locallySurjective :
    Presheaf.IsLocallySurjective (AffineBasis.topology X) (relativeAffineQuotient J f) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (relativeAffineQuotient_surjective J f)

/-- Sheafification preserves the local surjectivity of the actual quotient. -/
lemma relativeBasisSheafQuotient_locallySurjective :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf (AffineBasis.topology X) CommRingCat).map
        (relativeAffineQuotient J f)) :=
  (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).mpr inferInstance

end FLT.Mazur.IdealAdicGradedPullback
