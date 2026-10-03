/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBranchDifferenceSheaf

/-!
# Sections of structure-sheaf direct images on spectra

The actual unit and restriction maps become their defining ring homomorphisms
under the canonical global-section isomorphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.StructureDirectImage
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S T : CommRingCat.{u}}
/-- Global sections of a spectrum direct image are the source ring additively. -/
def spectrumSections (f : R ⟶ S) :
    (image (Spec.map f)).val.obj (.op ⊤) ≃+ S :=
  (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.toAddEquiv

/-- The structure-module inclusion induces the specified ring homomorphism. -/
theorem spectrumSections_unitMap (f : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    spectrumSections f ((unitMap (Spec.map f)).val.app (.op ⊤) r) =
      f ((Scheme.ΓSpecIso R).hom r) :=
  congrArg (fun k ↦ k.hom r) (Scheme.ΓSpecIso_naturality f)

/-- Restriction to a branch induces its specified ring homomorphism. -/
theorem spectrumSections_restriction (f : R ⟶ S) (a : S ⟶ T) (q : R ⟶ T)
    (w : Spec.map a ≫ Spec.map f = Spec.map q)
    (r : (image (Spec.map f)).val.obj (.op ⊤)) :
    spectrumSections q ((restriction (Spec.map a) (Spec.map f) (Spec.map q) w).val.app
      (.op ⊤) r) = a (spectrumSections f r) := by
  have h (X Y Z : Scheme.{u}) (s : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z)
      (w : s ≫ p = q) (r : (image p).val.obj (.op ⊤)) :
      (restriction s p q w).val.app (.op ⊤) r = s.appTop r := by
    subst q
    rfl
  rw [show (spectrumSections q) _ = (Scheme.ΓSpecIso T).hom
    ((restriction (Spec.map a) (Spec.map f) (Spec.map q) w).val.app (.op ⊤) r) from rfl]
  rw [h]
  exact congrArg (fun k ↦ k.hom r) (Scheme.ΓSpecIso_naturality a)
end FLT.Mazur.StructureDirectImage
