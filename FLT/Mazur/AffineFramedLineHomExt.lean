/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineSectionCoordinates

/-!
# Recovered vectors determine actual framed line maps

A morphism from a trivialized affine line to a finite free sheaf is determined
by the recovered vector. Equal vectors therefore construct a commuting
isomorphism between the original source sheaves.
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
variable {L N : X.Modules}

/-- The recovered vector determines the original map on the chosen unit frame. -/
lemma vector_eq_iff_frame_hom (e : L ≅ structureModule X) (d : N ≅ structureModule X)
    (s : L ⟶ SheafOfModules.free ι) (t : N ⟶ SheafOfModules.free ι) :
    vector e s = vector d t ↔ e.inv ≫ s = d.inv ≫ t := by
  constructor
  · intro h
    apply globalSection_hom_ext
    have hv := congrArg ((vectorSectionIso X ι).hom) h
    change (vectorSectionIso X ι).hom (vector e s) =
      (vectorSectionIso X ι).hom (vector d t) at hv
    rw [vectorSectionIso_vector, vectorSectionIso_vector] at hv
    exact hv
  · intro h
    apply (vectorSectionIso X ι).toLinearEquiv.injective
    change (vectorSectionIso X ι).hom _ = (vectorSectionIso X ι).hom _
    rw [vectorSectionIso_vector, vectorSectionIso_vector]
    exact congrArg (fun a ↦ a.app ⊤ (1 : Γ(X, ⊤))) h

/-- Equality of vectors constructs a comparison preserving the original inclusions. -/
lemma frameCompare_inclusion (e : L ≅ structureModule X) (d : N ≅ structureModule X)
    (s : L ⟶ SheafOfModules.free ι) (t : N ⟶ SheafOfModules.free ι)
    (h : vector e s = vector d t) : (e ≪≫ d.symm).hom ≫ t = s := by
  have hv := (vector_eq_iff_frame_hom e d s t).mp h
  change (e.hom ≫ d.inv) ≫ t = s
  rw [Category.assoc, ← hv, Iso.hom_inv_id_assoc]

/-- Maps with the same frame are determined by their recovered vector. -/
lemma vector_injective (e : L ≅ structureModule X) :
    Function.Injective (vector (ι := ι) e) := by
  intro s t h
  have hv := (vector_eq_iff_frame_hom e e s t).mp h
  exact (cancel_epi e.inv).mp hv

end FLT.Mazur.AffineSplitLineCoordinates
