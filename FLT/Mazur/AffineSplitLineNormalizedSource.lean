/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineCanonicalPoint
public import FLT.Mazur.SplitLineImageChart
public import FLT.Mazur.AffineSectionLineSubobjectEquality

/-!
# Recovering the original affine source from a unit coordinate

The recovered linear inclusion constructs a normalized section line with an
actual source isomorphism preserving the original free-sheaf inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open FCurve AffineModuleGlobalSections AffineFreeSheafCoordinates NormalizedSectionLine
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι] {L : X.Modules}
variable (e : L ≅ structureModule X) (s : L ⟶ SheafOfModules.free ι)
variable (r : SheafOfModules.free ι ⟶ L) (hr : s ≫ r = 𝟙 L)
variable (i : ι) (a : Γ(X, ⊤)ˣ) (hi : vector e s i = a)
attribute [local irreducible] affineTilde sourceIso vectorFreeIso

/-- The actual source identifies with the normalized image of its recovered vector. -/
def normalizedSourceIso : L ≅ sectionLineSheaf X i (unitCoordinateLine (vector e s) i a hi) :=
  (sourceIso e).symm ≪≫ (affineTilde X).mapIso
    (SplitLineImageChart.sourceIso (inclusion e s) (retraction e r)
      (retraction_inclusion e s r hr) (LinearEquiv.refl _ _) i a hi).toModuleIso

/-- Normalized source recovery preserves the original ambient inclusion. -/
lemma normalizedSourceIso_inclusion :
    (normalizedSourceIso e s r hr i a hi).hom ≫
      sectionLineInclusion X i (unitCoordinateLine (vector e s) i a hi) = s := by
  dsimp only [normalizedSourceIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    sectionLineInclusion]
  rw [Category.assoc, ← Category.assoc ((affineTilde X).map _), ← Functor.map_comp]
  have h := SplitLineImageChart.sourceIso_subtype (inclusion e s) (retraction e r)
    (retraction_inclusion e s r hr) (LinearEquiv.refl _ _) i a hi
  have hc : (SplitLineImageChart.sourceIso (inclusion e s) (retraction e r)
      (retraction_inclusion e s r hr) (LinearEquiv.refl _ _) i a hi).toModuleIso.hom ≫
        ModuleCat.ofHom (unitCoordinateLine (vector e s) i a hi).val.subtype =
      ModuleCat.ofHom (inclusion e s) := ModuleCat.hom_ext h
  rw [hc, inclusion_reconstruct, Iso.inv_hom_id_assoc]

/-- The recovered source line classifies the original framed reverse point. -/
lemma projectivePoint_normalizedSource :
    projectivePoint e s r hr =
      ProjectiveSpace.affineSectionLinePoint (.id _) i
        (unitCoordinateLine (vector e s) i a hi) :=
  SplitLinePrincipalPoints.morphism_eq_affineGeneratorPoint _ _ _ i a hi

include hi in
/-- Equality of normalized projective points recovers the original ambient subobject. -/
lemma subobject_eq_sectionLine_of_unit [Mono s] (j : ι) (N : Chart Γ(X, ⊤) ι j)
    (hp : projectivePoint e s r hr = ProjectiveSpace.affineSectionLinePoint (.id _) j N) :
    Subobject.mk s = Subobject.mk (sectionLineInclusion X j N) := by
  have hp' := (projectivePoint_normalizedSource e s r hr i a hi).symm.trans hp
  have hv := (ProjectiveSpace.affineSectionLinePoint_eq_iff _ i j _ _).mp hp'
  exact (Subobject.mk_eq_mk_of_comm _ _ (normalizedSourceIso e s r hr i a hi)
    (normalizedSourceIso_inclusion e s r hr i a hi)).trans
      ((sectionLine_subobject_eq_iff X i j _ N).mpr hv)

end FLT.Mazur.AffineSplitLineCoordinates
