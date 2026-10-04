/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveAmpleSubgroup

/-!
# Properness forced by the closed-presentation ample predicate

The project's relative ample predicate uses closed projective embeddings of
positive powers. It therefore forces properness of the structural morphism.
A comparison with the usual relative ample predicate must retain a properness
hypothesis: the usual ample predicate alone does not force properness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace.VeryAmplePresentation
variable {A : Type} [CommRing A] {X : Scheme} {f : X ⟶ Spec (.of A)} {L : X.Modules}

/-- A closed projective presentation makes the structural morphism proper. -/
theorem isProper (p : VeryAmplePresentation f L) : IsProper f := by
  rw [← p.over]
  infer_instance

end FLT.Mazur.ProjectiveSpace.VeryAmplePresentation
namespace FLT.Mazur.FCurve
variable {X S : Scheme} {f : X ⟶ S} {L : X.Modules}

/-- Closed projective presentations of positive powers on affine base opens
force the entire morphism to be proper. -/
theorem RelativeAmple.isProper (h : RelativeAmple f L) : IsProper f := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (fun U : S.affineOpens ↦ U.1) (iSup_affineOpens_eq_top S)
  intro U
  obtain ⟨m, _, ⟨p⟩⟩ := h U.1 U.2
  let := p.isProper
  exact IsProper.of_comp (f ∣_ U.1) U.2.isoSpec.hom

end FLT.Mazur.FCurve
