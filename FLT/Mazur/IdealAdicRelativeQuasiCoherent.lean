/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeAffineSheaf
public import FLT.Mazur.QuasiCoherentAffineBasePullback

/-!
# The closed quasi-coherent module underlying the relative ring sheaf

The actual closed pullback is quasi-coherent. The additive sheaf of the
glued relative ring identifies globally with its actual pushforward, using
the proved tensor chart comparisons on the affine basis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.AffineModuleGlobalSections
open FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The actual relative pullback on the closed scheme is quasi-coherent. -/
instance relativeTildeModule_isQuasicoherent : (relativeTildeModule J f).IsQuasicoherent :=
  QuasiCoherentAffineBasePullback.pullback ((J.comap f).subschemeι ≫ f)
    ((affineTilde Y).obj (ModuleCat.of Γ(Y, ⊤) (IdealAdicGradedSections.Sections J ⊤)))

/-- On the affine basis the glued relative ring has the actual closed additive sections. -/
def relativeTildeUnderlyingBasisIso :
    (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.obj
      ((sheafCompose (Opens.grothendieckTopology X) coefficientForget).obj
        (relativeRingSheaf J f)) ≅
    (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeTildePushforward J f)) :=
  ObjectProperty.isoMk _
    ((Functor.isoWhiskerRight
      (asIso (affineRingSheafificationUnit (relativeAffinePresheaf J f)))
        coefficientForget).symm ≪≫ relativeTildeAffineIso J f)

/-- The glued relative additive sheaf is the actual closed quasi-coherent pushforward. -/
def relativeTildeUnderlyingIso :
    (sheafCompose (Opens.grothendieckTopology X) coefficientForget).obj
      (relativeRingSheaf J f) ≅
        (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeTildePushforward J f) :=
  (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.preimageIso
    (relativeTildeUnderlyingBasisIso J f)

omit [IsLocallyNoetherian X] in
/-- The global identification restricts to the original affine tensor comparisons. -/
lemma relativeTildeUnderlyingIso_basis :
    (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.map
      (relativeTildeUnderlyingIso J f).hom = (relativeTildeUnderlyingBasisIso J f).hom := by
  exact Functor.map_preimage _ _

end FLT.Mazur.IdealAdicGradedPullback
