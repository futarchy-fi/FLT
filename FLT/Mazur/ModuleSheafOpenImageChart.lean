/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapImageTransition

/-!
# Coordinates and modules on image opens

An open immersion identifies its source with its image. Modules transported
along this identification retain their ambient pushforwards, and coordinates
of smaller opens commute with inclusion by monicity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenImageChart

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]

/-- The coordinate of a subopen of the image in the original chart. -/
def coordinate (U : X.Opens) (hU : U ≤ i.opensRange) : U.toScheme ⟶ Y :=
  IsOpenImmersion.lift i U.ι (by
    rw [Scheme.Opens.range_ι]
    exact fun x hx ↦ hU hx)

/-- The coordinate map is over the ambient scheme. -/
@[reassoc]
lemma coordinate_comp (U : X.Opens) (hU : U ≤ i.opensRange) :
    coordinate i U hU ≫ i = U.ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- Coordinates restrict along inclusions of opens. -/
lemma coordinate_refine {U V : X.Opens} (h : V ≤ U) (hU : U ≤ i.opensRange) :
    X.homOfLE h ≫ coordinate i U hU = coordinate i V (h.trans hU) := by
  apply (cancel_mono i).mp
  rw [Category.assoc, coordinate_comp, coordinate_comp, Scheme.homOfLE_ι]

/-- The canonical identification of an open immersion with its image. -/
def imageIso : Y ≅ i.opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by rw [Scheme.Opens.range_ι]; rfl)

/-- The image identification preserves the map to the ambient scheme. -/
@[reassoc]
lemma imageIso_hom_ι : (imageIso i).hom ≫ i.opensRange.ι = i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Transport a module from the source onto the actual image open. -/
def imageModule (M : Y.Modules) : i.opensRange.toScheme.Modules :=
  (pushforward (imageIso i).hom).obj M

/-- Transport onto the image does not change the ambient pushforward. -/
def imagePushforwardIso (M : Y.Modules) :
    (pushforward i.opensRange.ι).obj (imageModule i M) ≅ (pushforward i).obj M :=
  (pushforwardComp (imageIso i).hom i.opensRange.ι).app M ≪≫
    (pushforwardCongr (imageIso_hom_ι i)).app M

/-- Restriction to the original chart recovers its module. -/
def imageRestrictionIso (M : Y.Modules) :
    (restrictFunctor (imageIso i).hom).obj (imageModule i M) ≅ M :=
  (restrictFunctorAdjCounitIso (imageIso i).hom).app M

end FLT.Mazur.ModuleSheafOpenImageChart
