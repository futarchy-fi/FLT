/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyNoetherianUniversalStructureSheaf
public import FLT.Mazur.NoetherianProperStructureSheaf
public import FLT.Mazur.ProperSmoothStructureSheaf
public import FLT.Mazur.PolygonBranchDifferenceSheaf

/-!
# Structure-module comparison for pointed proper families

The established ring-valued comparison identifies the actual module-sheaf
unit, also after arbitrary cartesian base change. The section hypothesis
is retained explicitly throughout, including over nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.PointedStructureModuleComparison
open StructureDirectImage
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- Bijective structural pullback on every open makes the actual module unit invertible. -/
lemma unitMap_isIso_of_app (h : ∀ U : S.Opens, Function.Bijective (f.app U)) :
    IsIso (unitMap f) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact h U

variable [IsProper f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)

include s hs in
/-- The module unit for a pointed flat proper family over a locally Noetherian base. -/
lemma noetherian_unitMap_isIso [IsLocallyNoetherian S] [Flat f]
    [GeometricallyConnected f] [GeometricallyReduced f] : IsIso (unitMap f) := by
  apply unitMap_isIso_of_app f
  intro U
  exact ConcreteCategory.bijective_of_isIso
    (NoetherianProperStructureSheaf.openSectionsIso f s hs U).hom

include s hs in
/-- The same module unit after any base change, with no Noetherian condition on the new base. -/
lemma cartesian_unitMap_isIso [IsLocallyNoetherian S] [Flat f]
    [GeometricallyConnected f] [GeometricallyReduced f]
    {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
    (H : IsPullback p q f g) : IsIso (unitMap q) := by
  apply unitMap_isIso_of_app q
  intro U
  exact ConcreteCategory.bijective_of_isIso
    (LocallyNoetherianUniversalStructureSheaf.openSectionsIso H s hs U).hom

include s hs in
/-- A smooth pointed proper family has the comparison over every original base. -/
lemma smooth_unitMap_isIso [Smooth f] [GeometricallyConnected f] :
    IsIso (unitMap f) := by
  apply unitMap_isIso_of_app f
  intro U
  exact ConcreteCategory.bijective_of_isIso
    (ProperSmoothStructureSheaf.openSectionsIso f s hs U).hom

end FLT.Mazur.PointedStructureModuleComparison
