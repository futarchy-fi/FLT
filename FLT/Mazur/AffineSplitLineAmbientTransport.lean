/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineProjectiveLinearTransport
public import FLT.Mazur.AffineSplitLineSectionCoordinates

/-!
# Reverse points respect the original ambient sheaf isomorphism

The actual recovered section vector transforms by the coordinates of the
ambient sheaf isomorphism. The principal-cover transport theorem therefore
identifies the reverse projective points without any unit-coordinate input.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open AffineModuleGlobalSections AffineFreeSheafCoordinates FiniteFreeContragredient
open FCurve ProjectiveSpace
variable {X : Scheme.{u}} [IsAffine X] {ι κ : Type u} [Finite ι] [Finite κ]
variable (a : (SheafOfModules.free ι : X.Modules) ≅ SheafOfModules.free κ)

/-- Ordinary vector realization commutes with the original free-sheaf isomorphism. -/
lemma vectorSectionIso_coordinates (v : ι → Γ(X, ⊤)) :
    (vectorSectionIso X κ).hom (functionCoordinates (coordinates X a) v) =
      (sections X).map a.hom ((vectorSectionIso X ι).hom v) := by
  rw [vectorSectionIso_apply, vectorSectionIso_apply]
  have hv : (Finsupp.linearEquivFunOnFinite Γ(X, ⊤) Γ(X, ⊤) κ).symm
      (functionCoordinates (coordinates X a) v) =
        coordinates X a ((Finsupp.linearEquivFunOnFinite Γ(X, ⊤) Γ(X, ⊤) ι).symm v) := by
    simp only [functionCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [hv]
  exact realize_coordinates X a _

variable {L : X.Modules} (e : L ≅ structureModule X)
variable (s : L ⟶ SheafOfModules.free ι)

/-- Coordinates of an actual ambient change are the recovered vector of its composite. -/
lemma vector_ambientIso :
    vector e (s ≫ a.hom) = functionCoordinates (coordinates X a) (vector e s) := by
  apply (vectorSectionIso X κ).toLinearEquiv.injective
  change (vectorSectionIso X κ).hom _ = (vectorSectionIso X κ).hom _
  rw [vectorSectionIso_vector, vectorSectionIso_coordinates, vectorSectionIso_vector]
  rfl

/-- Any splitting of the transported sheaf inclusion gives the genuine dual image point. -/
lemma projectivePoint_ambientIso
    (r : SheafOfModules.free ι ⟶ L) (hr : s ≫ r = 𝟙 L)
    (q : SheafOfModules.free κ ⟶ L) (hq : (s ≫ a.hom) ≫ q = 𝟙 L) :
    projectivePoint e s r hr ≫ (linearIso (map (coordinates X a))).hom =
      projectivePoint e (s ≫ a.hom) q hq := by
  have hv := vector_ambientIso a e s
  have ht : retraction e q (functionCoordinates (coordinates X a) (vector e s)) = 1 := by
    rw [← hv]
    exact vector_retraction e _ q hq
  have hp := SplitLinePrincipalPoints.morphism_linearTransport (coordinates X a)
    (vector e s) (retraction e r) (vector_retraction e s r hr) (retraction e q) ht
  simpa only [projectivePoint, hv] using hp

omit [IsAffine X] [Finite ι] [Finite κ] in
/-- The original sheaf retraction transports through the inverse ambient map. -/
lemma ambientIso_retraction (r : SheafOfModules.free ι ⟶ L) (hr : s ≫ r = 𝟙 L) :
    (s ≫ a.hom) ≫ (a.inv ≫ r) = 𝟙 L := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hr

end FLT.Mazur.AffineSplitLineCoordinates
