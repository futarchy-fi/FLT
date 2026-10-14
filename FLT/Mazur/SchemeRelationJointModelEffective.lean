/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationJointModelGeometry

/-!
# Joint coefficient models over an effective source projection

When the second projection is an effective epimorphism and detects the full
invariant kernel, the constructed joint target is isomorphic to that second
target. Thus adjoining old invariant coefficients does not by itself repair
missing Picard effectivity on an already effective source projection.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationJointModel
open SchemeEffectiveEpiSections
variable {E A : Scheme.{u}} (p q : E ⟶ A)
  {C D : Type u} [CommRing C] [CommRing D]
  (c : C →+* compatibleFunctions p q) (d : D →+* compatibleFunctions p q)
attribute [local irreducible] coefficientProjection
local notation "πD" => coefficientProjection p q d
local notation "j" => projection p q c d
local notation "r" => toRight p q c d
/-- Effective descent constructs the inverse comparison from the actual effective projection. -/
theorem toRight_isIso_of_effective [EffectiveEpi (coefficientProjection p q d)]
    (hd : ∀ {Z : Scheme.{u}} (x y : Z ⟶ A),
      x ≫ coefficientProjection p q d = y ≫ coefficientProjection p q d ↔
        x ≫ SchemeRelationInvariantSpectrum.projection p q =
          y ≫ SchemeRelationInvariantSpectrum.projection p q) : IsIso (toRight p q c d) := by
  have hi := (hd (pullback.fst πD πD) (pullback.snd πD πD)).mp
    (pullback.condition (f := πD) (g := πD))
  have hh : pullback.fst πD πD ≫ j = pullback.snd πD πD ≫ j :=
    congrArg (fun z ↦ z ≫ fromInvariants p q c d) hi
  let H := IsPullback.of_hasPullback πD πD
  let L := isColimitCoforkOfEffectiveEpi πD H.cone H.isLimit
  let s : Spec (.of D) ⟶ target p q c d := L.desc (Cofork.ofπ j hh)
  have hs : πD ≫ s = j := Cofork.IsColimit.π_desc L
  let e : target p q c d ≅ Spec (.of D) :=
    { hom := r
      inv := s
      hom_inv_id := by
        apply affine_hom_ext p q c d
        rw [← Category.assoc, projection_toRight, hs, Category.comp_id]
      inv_hom_id := by
        apply (cancel_epi πD).mp
        rw [← Category.assoc, hs, projection_toRight, Category.comp_id] }
  exact e.isIso_hom

end FLT.Mazur.SchemeRelationJointModel
