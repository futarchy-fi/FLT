/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeSheafCharts
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The actual closed coefficient sheaf after gluing

The associated sheaf of the direct sum of the actual closed coefficients
identifies with the additive sheaf of the glued coefficient algebra. Both
sheafification and extension from the affine basis preserve the comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry TopologicalSpace
open FLT.Mazur.IdealAdicGradedPullback FLT.Mazur.IdealAdicGradedClosedAction

universe u

namespace FLT.Mazur.IdealAdicGradedClosedAction

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The additive functor used for the actual graded ring coefficients. -/
abbrev coefficientForget : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}

/-- Forgetting the graded ring operations preserves local bijectivity. -/
instance coefficientForget_preservesSheafification :
    (AffineBasis.topology X).PreservesSheafification coefficientForget.{u} where
  le := by
    intro P Q φ hφ
    obtain ⟨hi, hs⟩ := ((AffineBasis.topology X).W_iff_isLocallyBijective φ).mp hφ
    apply ((AffineBasis.topology X).W_iff_isLocallyBijective
      (whiskerRight φ coefficientForget.{u})).mpr
    exact ⟨⟨fun x y h ↦ hi.equalizerSieve_mem x y h⟩, ⟨fun s ↦ hs.imageSieve_mem s⟩⟩

/-- Sheafification of the actual total closed coefficients on the affine basis. -/
def closedBasisSheaf : Sheaf (AffineBasis.topology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (AffineBasis.topology X) AddCommGrpCat).obj
    ((AffineBasis.inclusion X).op ⋙ totalPresheaf (J.comap f))

/-- Sheafification retains the actual closed-to-ambient total comparison. -/
def closedBasisSheafIso : closedBasisSheaf J f ≅
    (sheafCompose (AffineBasis.topology X) coefficientForget).obj
      ((presheafToSheaf (AffineBasis.topology X) CommRingCat).obj
        (coefficientAffinePresheaf J f)) :=
  (presheafToSheaf (AffineBasis.topology X) AddCommGrpCat).mapIso
    (isoWhiskerLeft (AffineBasis.inclusion X).op (totalPresheafIso (J.comap f))) ≪≫
  (sheafComposeNatIso (AffineBasis.topology X) coefficientForget
    (sheafificationAdjunction _ CommRingCat) (sheafificationAdjunction _ AddCommGrpCat)).app
      (coefficientAffinePresheaf J f)

/-- The actual closed total coefficient sheaf, extended from the affine basis. -/
def closedTotalSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (AffineBasis.sheafEquivalence X AddCommGrpCat).functor.obj (closedBasisSheaf J f)

/-- On the basis, the closed coefficients identify with the restriction of the glued algebra. -/
def closedBasisRestrictionIso : closedBasisSheaf J f ≅
    (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.obj
      ((sheafCompose (Opens.grothendieckTopology X) coefficientForget).obj
        (coefficientRingSheaf J f)) :=
  closedBasisSheafIso J f ≪≫
    (sheafCompose (AffineBasis.topology X) coefficientForget).mapIso
      ((AffineBasis.sheafEquivalence X CommRingCat).unitIso.app
        ((presheafToSheaf (AffineBasis.topology X) CommRingCat).obj
          (coefficientAffinePresheaf J f)))

/-- The glued coefficient algebra has exactly the associated actual closed additive sheaf. -/
def closedTotalSheafIso : closedTotalSheaf J f ≅
    (sheafCompose (Opens.grothendieckTopology X) coefficientForget).obj
      (coefficientRingSheaf J f) :=
  (AffineBasis.sheafEquivalence X AddCommGrpCat).functor.mapIso
    (closedBasisRestrictionIso J f) ≪≫
  (AffineBasis.sheafEquivalence X AddCommGrpCat).counitIso.app _

/-- The glued relative module retains the associated actual closed coefficient sheaf. -/
def relativeModuleUnderlyingIso :
    (SheafOfModules.toSheaf (relativeScalarSheaf J f)).obj
      (relativeCoefficientModuleSheaf J f) ≅ closedTotalSheaf J f :=
  (closedTotalSheafIso J f).symm

end FLT.Mazur.IdealAdicGradedClosedAction
