/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantMapSections
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed restriction in original invariant-section coordinates

On any quotient open whose source inverse image is affine, a closed source
inclusion lifts every source function. Lifting an invariant function to the
quotient additionally requires the original relation equation. The kernel is
exactly the invariant functions that vanish on the closed source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
local notation "m" => invariantMap e e' g r hp hq
variable (O : TopologicalSpace.Opens (Orbit e))

/-- The full closed source domain is exactly the inverse image of the original domain. -/
theorem invariantMap_sourceOpen_eq :
    (pullOpen e' ((TopologicalSpace.Opens.map (m).base).obj O)).val = g ⁻¹ᵁ (pullOpen e O).val := by
  ext x
  change (m).base (projection e' x) ∈ O ↔ projection e (g x) ∈ O
  rw [invariantMap_projection_apply]

/-- Closed restriction of original source functions on the exact quotient domains. -/
def closedSourceRestriction : (sourceSheaf e).obj.obj (op O) →+*
    (sourceSheaf e').obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj O)) :=
  (g.appLE _ _ (invariantMap_sourceOpen_le e e' g r hp hq O)).hom

/-- Closed immersion and affine source domain supply actual lifts of all source sections. -/
theorem closedSourceRestriction_surjective [IsClosedImmersion g]
    (hO : IsAffineOpen (pullOpen e O).val) :
    Function.Surjective (closedSourceRestriction e e' g r hp hq O) := by
  suffices h : ∀ (V : U'.left.Opens) (hV : V = g ⁻¹ᵁ (pullOpen e O).val),
      Function.Surjective (g.appLE _ V hV.le) from
    h _ (invariantMap_sourceOpen_eq e e' g r hp hq O)
  intro V hV
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using g.app_surjective (pullOpen e O).val hO

/-- The difference of the two original relation pullbacks. -/
def relationDifference : (sourceSheaf e).obj.obj (op O) →+
    (relationSheaf e).obj.obj (op O) :=
  ((firstRestriction e).hom.app (op O)).hom.toAddMonoidHom -
    ((secondRestriction e).hom.app (op O)).hom.toAddMonoidHom

/-- Zero difference is precisely the original relation equation, including open transport. -/
theorem relationDifference_eq_zero (a : (sourceSheaf e).obj.obj (op O)) :
    relationDifference e O a = 0 ↔
      (firstRestriction e).hom.app (op O) a = (secondRestriction e).hom.app (op O) a :=
  sub_eq_zero

/-- A closed invariant section lifts exactly when a source lift satisfies the whole relation. -/
theorem invariantMap_section_lift_iff
    (t : (invariantSheaf e').obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj O))) :
    (∃ s : (invariantSheaf e).obj.obj (op O), (m).c.app (op O) s = t) ↔
      ∃ a : (sourceSheaf e).obj.obj (op O),
        closedSourceRestriction e e' g r hp hq O a =
          (invariantInclusion e').hom.app
            (op ((TopologicalSpace.Opens.map (m).base).obj O)) t ∧
          relationDifference e O a = 0 := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨(invariantInclusion e).hom.app (op O) s, ?_, ?_⟩
    · exact (invariantMap_source_apply e e' g r hp hq O s).symm
    · exact (relationDifference_eq_zero e O _).mpr (invariantSection_condition e O s)
  · rintro ⟨a, ha, hδ⟩
    obtain ⟨s, hs, _⟩ := invariantSection_existsUnique e O a
      ((relationDifference_eq_zero e O a).mp hδ)
    refine ⟨s, invariantSection_ext e' ((TopologicalSpace.Opens.map (m).base).obj O) ?_⟩
    rw [invariantMap_source_apply]
    change closedSourceRestriction e e' g r hp hq O
      ((invariantInclusion e).hom.app (op O) s) = _
    rw [hs, ha]

/-- The quotient restriction kills exactly the invariant functions vanishing on the source. -/
theorem invariantMap_section_eq_zero_iff (s : (invariantSheaf e).obj.obj (op O)) :
    (m).c.app (op O) s = 0 ↔
      closedSourceRestriction e e' g r hp hq O
        ((invariantInclusion e).hom.app (op O) s) = 0 := by
  have hh := invariantMap_source_apply e e' g r hp hq O s
  change (invariantInclusion e').hom.app _ ((m).c.app (op O) s) =
    closedSourceRestriction e e' g r hp hq O
      ((invariantInclusion e).hom.app (op O) s) at hh
  constructor
  · intro h
    exact hh.symm.trans (h ▸ map_zero _)
  · intro h
    apply invariantSection_ext e' ((TopologicalSpace.Opens.map (m).base).obj O)
    exact (hh.trans h).trans (map_zero _).symm

end FLT.Mazur.RelativeRelationOrbit
