/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationQuotientSheaf
public import FLT.Mazur.RelativeRelationInvariantSections

/-!
# Actual locally ringed quotient sections in source coordinates

Every compatible source regular function comes from a unique section of the
actual quotient structure sheaf. This strengthens the invariant-sheaf description
to the existing locally ringed quotient, without claiming local affineness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))

/-- The structure-sheaf comparison is a ring equivalence on every orbit open. -/
def quotientSectionRingEquiv : (invariantSheaf e).obj.obj (op W) ≃+*
    (quotientOrbitSheaf e).obj.obj (op W) :=
  (((TopCat.Sheaf.forget _ _).mapIso (invariantSheafIsoQuotient e)).app
    (op W)).commRingCatIsoToRingEquiv

/-- The ring equivalence preserves the actual source regular function. -/
theorem quotientSectionRingEquiv_source (t : (invariantSheaf e).obj.obj (op W)) :
    (quotientOrbitSource e).hom.app (op W) (quotientSectionRingEquiv e W t) =
      (invariantInclusion e).hom.app (op W) t :=
  congrArg (fun k ↦ k.hom.app (op W) t) (invariantSheafIsoQuotient_source e)

/-- Compatible source regular functions descend uniquely to the actual quotient sheaf. -/
theorem quotientSection_existsUnique (s : (sourceSheaf e).obj.obj (op W))
    (hs : (firstRestriction e).hom.app (op W) s =
      (secondRestriction e).hom.app (op W) s) :
    ∃! t : (quotientOrbitSheaf e).obj.obj (op W),
      (quotientOrbitSource e).hom.app (op W) t = s := by
  obtain ⟨t, ht, hu⟩ := invariantSection_existsUnique e W s hs
  refine ⟨quotientSectionRingEquiv e W t,
    (quotientSectionRingEquiv_source e W t).trans ht, ?_⟩
  intro z hz
  obtain ⟨y, rfl⟩ := (quotientSectionRingEquiv e W).surjective z
  exact congrArg (quotientSectionRingEquiv e W)
    (hu y ((quotientSectionRingEquiv_source e W y).symm.trans hz))

/-- Actual quotient sections satisfy the original relation's regular-function equation. -/
theorem quotientSection_condition (t : (quotientOrbitSheaf e).obj.obj (op W)) :
    (firstRestriction e).hom.app (op W) ((quotientOrbitSource e).hom.app (op W) t) =
      (secondRestriction e).hom.app (op W) ((quotientOrbitSource e).hom.app (op W) t) := by
  obtain ⟨z, rfl⟩ := (quotientSectionRingEquiv e W).surjective t
  rw [quotientSectionRingEquiv_source]
  exact invariantSection_condition e W z

/-- The quotient's sections are precisely original functions invariant under the relation. -/
theorem quotientSection_iff (s : Γ(U.left, (pullOpen e W).val)) :
    (∃! t : (quotientOrbitSheaf e).obj.obj (op W),
      (quotientOrbitSource e).hom.app (op W) t = s) ↔
        p.left.app (pullOpen e W).val s =
          A.left.presheaf.map
            (eqToHom (congrArg op (pullOpen_preimage_eq e W).symm))
              (q.left.app (pullOpen e W).val s) := by
  constructor
  · rintro ⟨t, rfl, _⟩
    have h := quotientSection_condition e W t
    rw [firstRestriction_app, secondRestriction_app] at h
    exact h
  · intro hs
    apply quotientSection_existsUnique
    rw [firstRestriction_app, secondRestriction_app]
    exact hs

end FLT.Mazur.RelativeRelationOrbit
