/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenImageChart

/-!
# Recovering a module on the original open chart

A restriction isomorphism on the image open transports back to the original
chart, both as a restriction and as an actual module pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenImageChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable (M : Y.Modules) (G : X.Modules)
variable (e : G.restrict i.opensRange.ι ≅ imageModule i M)

/-- Recovery on the image open implies recovery on the original open chart. -/
def restrictionRecovery : G.restrict i ≅ M :=
  (restrictFunctorCongr (imageIso_hom_ι i)).symm.app G ≪≫
    (restrictFunctorComp (imageIso i).hom i.opensRange.ι).app G ≪≫
    (restrictFunctor (imageIso i).hom).mapIso e ≪≫ imageRestrictionIso i M

/-- The original module is also recovered by actual pullback along the chart. -/
def pullbackRecovery : (pullback i).obj G ≅ M :=
  (restrictFunctorIsoPullback i).symm.app G ≪≫ restrictionRecovery i M G e

end FLT.Mazur.ModuleSheafOpenImageChart
