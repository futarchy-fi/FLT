/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeCoefficientSectionNaturality
public import FLT.Mazur.IdealAdicCoefficientAffineSheaf

/-!
# The global additive sheaf of the descended coefficient pushforward

The actual pushforward of the descended coherent module recovers the
original coefficient algebra on the affine basis. Cover density extends
this comparison to the actual global closed total additive sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

attribute [local irreducible] relativeDescendedCoefficientSheaf

/-- The actual descended pushforward recovers the original coefficient presheaf on affine opens. -/
def relativeDescendedCoefficientAffineIso :
    (AffineBasis.inclusion X).op ⋙ (relativeDescendedCoefficientPushforward J f).presheaf ≅
      coefficientAffinePresheaf J f ⋙ coefficientForget :=
  NatIso.ofComponents (fun U ↦ relativePushforwardCoefficientSectionsIso J f U.unop) (by
    intro U V i
    exact relativePushforwardCoefficientSectionsIso_naturality J f (homOfLE i.unop.le))

/-- On the affine basis the actual pushforward is the additive coefficient algebra sheaf. -/
def relativeDescendedUnderlyingBasisIso :
    (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (relativeDescendedCoefficientPushforward J f)) ≅
    (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.obj
      ((sheafCompose (Opens.grothendieckTopology X) coefficientForget).obj
        (coefficientRingSheaf J f)) :=
  ObjectProperty.isoMk _ (relativeDescendedCoefficientAffineIso J f ≪≫
    Functor.isoWhiskerRight (asIso (affineRingSheafificationUnit
      (coefficientAffinePresheaf J f))) coefficientForget)

/-- The actual descended pushforward has the global additive sheaf of the coefficient algebra. -/
def relativeDescendedCoefficientUnderlyingIso :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj
        (relativeDescendedCoefficientPushforward J f) ≅
      (sheafCompose (Opens.grothendieckTopology X) coefficientForget).obj
        (coefficientRingSheaf J f) :=
  (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.preimageIso
    (relativeDescendedUnderlyingBasisIso J f)

/-- The global comparison retains its original coefficient comparison on the affine basis. -/
lemma relativeDescendedCoefficientUnderlyingIso_basis :
    (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.map
      (relativeDescendedCoefficientUnderlyingIso J f).hom =
        (relativeDescendedUnderlyingBasisIso J f).hom :=
  Functor.map_preimage _ _

/-- The actual descended pushforward recovers the global closed total additive sheaf. -/
def relativeDescendedClosedTotalIso :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj
        (relativeDescendedCoefficientPushforward J f) ≅ closedTotalSheaf J f :=
  relativeDescendedCoefficientUnderlyingIso J f ≪≫ (closedTotalSheafIso J f).symm

end FLT.Mazur.IdealAdicGradedPullback
