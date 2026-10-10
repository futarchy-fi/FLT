/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineSectionCoordinates
public import FLT.Mazur.AffineSplitLineFrameIndependence

/-!
# Source isomorphisms preserve the original split-line projective point

An actual isomorphism commuting with the ambient inclusions identifies the
recovered vectors in compatible frames. Frame and retraction independence
then remove those choices from the projective comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open FCurve
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι]
variable {L M : X.Modules}

/-- A genuine source isomorphism identifies the actual recovered vectors. -/
lemma vector_sourceIso (a : L ≅ M) (d : M ≅ structureModule X)
    (s : L ⟶ SheafOfModules.free ι) (t : M ⟶ SheafOfModules.free ι)
    (h : a.hom ≫ t = s) : vector (a ≪≫ d) s = vector d t := by
  apply (vectorSectionIso X ι).toLinearEquiv.injective
  change (vectorSectionIso X ι).hom _ = (vectorSectionIso X ι).hom _
  rw [vectorSectionIso_vector, vectorSectionIso_vector]
  have ht : a.inv ≫ s = t := by rw [← h, Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ k.app ⊤ (d.inv.app ⊤ (1 : Γ(X, ⊤)))) ht

/-- Equality of actual recovered vectors suffices, independently of retraction. -/
lemma projectivePoint_of_vector_eq (e : L ≅ structureModule X) (d : M ≅ structureModule X)
    (s : L ⟶ SheafOfModules.free ι) (t : M ⟶ SheafOfModules.free ι)
    (r : SheafOfModules.free ι ⟶ L) (q : SheafOfModules.free ι ⟶ M)
    (hr : s ≫ r = 𝟙 L) (hq : t ≫ q = 𝟙 M) (hv : vector e s = vector d t) :
    projectivePoint e s r hr = projectivePoint d t q hq := by
  have hs : retraction e r (vector d t) = 1 := by
    rw [← hv]
    exact vector_retraction e s r hr
  calc
    _ = SplitLinePrincipalPoints.morphism (vector d t) (retraction e r) hs := by
      unfold projectivePoint
      congr 1
    _ = _ := SplitLinePrincipalPoints.morphism_retraction_eq _ _ _ _ _

/-- Isomorphic original inclusions have identical projective points for arbitrary choices. -/
lemma projectivePoint_sourceIso (a : L ≅ M)
    (e : L ≅ structureModule X) (d : M ≅ structureModule X)
    (s : L ⟶ SheafOfModules.free ι) (t : M ⟶ SheafOfModules.free ι)
    (r : SheafOfModules.free ι ⟶ L) (q : SheafOfModules.free ι ⟶ M)
    (hr : s ≫ r = 𝟙 L) (hq : t ≫ q = 𝟙 M) (h : a.hom ≫ t = s) :
    projectivePoint e s r hr = projectivePoint d t q hq := by
  rw [projectivePoint_frame (a ≪≫ d) e s r hr]
  exact projectivePoint_of_vector_eq _ _ _ _ _ _ _ _ (vector_sourceIso a d s t h)

end FLT.Mazur.AffineSplitLineCoordinates
