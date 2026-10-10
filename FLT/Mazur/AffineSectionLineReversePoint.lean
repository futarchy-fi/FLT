/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineCoordinates
public import FLT.Mazur.SplitLineProjectiveUnitRecovery

/-!
# Recovering the actual point of an affine section line

The original section-line sheaf inclusion has its original normalized
section generator as recovered vector. Its reverse projective morphism is
therefore exactly the affine point that constructed the section line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open AffineModuleGlobalSections AffineFreeSheafCoordinates NormalizedSectionLine FCurve
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι]
variable (i : ι) (L : Chart Γ(X, ⊤) ι i)
attribute [local irreducible] vectorFreeIso

omit [Finite ι] in
/-- The affine source comparison cancels the actual section-line trivialization. -/
lemma sourceIso_sectionLineTrivialization :
    sourceIso (sectionLineTrivialization X i L) =
      (affineTilde X).mapIso (trivialization Γ(X, ⊤) ι i L).symm.toModuleIso := by
  unfold sourceIso sectionLineTrivialization
  rw [← Iso.trans_assoc, Iso.trans_symm, Iso.self_symm_id_assoc]
  rfl

attribute [local irreducible] affineTilde

/-- Coordinate recovery returns the original normalized generator of the section submodule. -/
lemma vector_sectionLineInclusion :
    vector (sectionLineTrivialization X i L) (sectionLineInclusion X i L) =
      generator Γ(X, ⊤) ι i L := by
  unfold vector inclusion
  rw [sourceIso_sectionLineTrivialization]
  dsimp only [sectionLineInclusion, Functor.mapIso_hom]
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Functor.map_comp, Functor.preimage_map]
  rfl

/-- The actual sheaf section-line construction recovers its original affine projective point. -/
lemma projectivePoint_sectionLineInclusion
    (r : SheafOfModules.free ι ⟶ sectionLineSheaf X i L)
    (hr : sectionLineInclusion X i L ≫ r = 𝟙 _) :
    projectivePoint (sectionLineTrivialization X i L) (sectionLineInclusion X i L) r hr =
      ProjectiveSpace.affineSectionLinePoint (.id _) i L := by
  have hv := vector_sectionLineInclusion i L
  have ht : retraction (sectionLineTrivialization X i L) r
      (generator Γ(X, ⊤) ι i L) = 1 := by
    rw [← hv]
    exact vector_retraction _ _ r hr
  have hp := SplitLinePrincipalPoints.morphism_generator_eq_sectionPoint i L
    (retraction (sectionLineTrivialization X i L) r) ht
  simpa only [projectivePoint, hv] using hp

end FLT.Mazur.AffineSplitLineCoordinates
