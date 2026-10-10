/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeReducedRelativeBaseChange
public import FLT.Mazur.StructureDirectImageHZero
public import FLT.Mazur.ModuleOpenCohomologyRestriction

/-!
# The actual relative structure-module and H0 comparison

The componentwise ring comparison makes the original structure-module unit an
isomorphism. Applying actual module cohomology identifies base functions with
H0 of the direct image. This includes every reduced locally Noetherian base
change of a pointed flat proper family with connected reduced geometric fibers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.SchemeReducedRelativeSections
open StructureDirectImage FCurve
variable {X S : Scheme.{0}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
  [IsProper f] [GeometricallyConnected f] [GeometricallyReduced f] [IsReduced X]

include s hs in
/-- The actual structure-module unit is an isomorphism, proved on every open. -/
lemma unitMap_isIso : IsIso (unitMap f) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (f.app U)
  let _ := app_isIso f s hs U
  exact ConcreteCategory.bijective_of_isIso _

/-- The base structure module is the actual direct image of the family structure module. -/
def structureModuleIso : PolygonStructureInclusion.structureModule S ≅ image f := by
  let _ := unitMap_isIso f s hs
  exact asIso (unitMap f)

/-- The module comparison keeps the original unit on the structure sheaf. -/
lemma structureModuleIso_hom : (structureModuleIso f s hs).hom = unitMap f := rfl

/-- Base functions identify with actual degree-zero cohomology of the direct image. -/
def h0Equiv : Γ(S, ⊤) ≃ₗ[Γ(S, ⊤)] ModuleH (image f) 0 :=
  (moduleH0Equiv (PolygonStructureInclusion.structureModule S)).symm.trans
    (moduleHIsoOfIso (structureModuleIso f s hs) 0)

/-- The H0 equivalence is induced by the original structure-sheaf unit. -/
lemma h0Equiv_apply (r : Γ(S, ⊤)) : h0Equiv f s hs r =
    moduleHMap (unitMap f) 0
      ((moduleH0Equiv (PolygonStructureInclusion.structureModule S)).symm r) := rfl

/-- Under the canonical H0-to-sections comparison this is actual structural pullback. -/
lemma h0Equiv_sections (r : Γ(S, ⊤)) :
    moduleH0Equiv (image f) (h0Equiv f s hs r) = f.appTop r := by
  rw [h0Equiv_apply, moduleH0Equiv_naturality, LinearEquiv.apply_symm_apply]
  rfl

end FLT.Mazur.SchemeReducedRelativeSections
