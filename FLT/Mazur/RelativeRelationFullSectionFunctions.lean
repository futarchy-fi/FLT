/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantRestriction

/-!
# Original invariant sections in full relation coordinates

The abstract section comparison packages the invariant source domain before
specializing to geometric relation constructions. The full double restriction
retains every original endpoint equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (B : TopologicalSpace.Opens (Orbit e))

/-- The original source open above the chosen quotient open. -/
@[irreducible]
def fullSectionSourceOpen : U.left.Opens := (pullOpen e B).val

/-- The packaged domain is exactly the original invariant inverse image. -/
theorem fullSectionSourceOpen_eq : fullSectionSourceOpen e B = (pullOpen e B).val := by
  unfold fullSectionSourceOpen
  rfl

/-- Membership in the source open is detected by the original orbit projection. -/
theorem mem_fullSectionSourceOpen (x : U.left) :
    x ∈ fullSectionSourceOpen e B ↔ projection e x ∈ B := by
  rw [fullSectionSourceOpen_eq]
  rfl

/-- Original invariant sections agree with the full compatible functions on their source open. -/
def fullSectionFunctionEquiv : (invariantSheaf e).obj.obj (op B) ≃+*
    compatibleFunctions
      (SchemeRelationRestriction.fst p.left q.left (fullSectionSourceOpen e B).ι)
      (SchemeRelationRestriction.snd p.left q.left (fullSectionSourceOpen e B).ι) := by
  unfold fullSectionSourceOpen
  exact ((invariantSectionRingEquiv e B).trans
    (originalInvariantGlobalEquiv (pullOpen e B).val (pullOpen_preimage_eq e B))).trans
      (SchemeRelationRestriction.invariantFunctionEquiv p.left q.left
        (pullOpen e B).val (pullOpen_preimage_eq e B))

/-- The section comparison retains the original inclusion with its explicit domain transport. -/
theorem fullSectionFunctionEquiv_val (t : (invariantSheaf e).obj.obj (op B)) :
    (fullSectionFunctionEquiv e B t).val = (fullSectionSourceOpen e B).topIso.inv
      (U.left.presheaf.map (eqToHom (congrArg op (fullSectionSourceOpen_eq e B).symm))
        ((invariantInclusion e).hom.app (op B) t)) := by
  unfold fullSectionFunctionEquiv fullSectionSourceOpen
  simp only [eqToHom_refl]
  rw [U.left.presheaf.map_id]
  rfl

end FLT.Mazur.RelativeRelationOrbit
