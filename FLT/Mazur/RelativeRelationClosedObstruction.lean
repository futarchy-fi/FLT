/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantSectionObstruction
public import FLT.Mazur.RelativeRelationClosedSections

/-!
# An exact obstruction for the closed quotient's structure sheaf

Closed source restriction is surjective on affine source neighborhoods. Its
additive obstruction, restricted to closed invariant functions, has kernel
exactly the image of the actual map of invariant structure sheaves. This
separates ordinary closed lifting from the additional descent equation.
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
variable (O : TopologicalSpace.Opens (Orbit e)) [IsClosedImmersion g]
  (hO : IsAffineOpen (pullOpen e O).val)
local notation "ρ" => closedSourceRestriction e e' g r hp hq O
local notation "δ" => relationDifference e O

/-- The obstruction group uses all original relation functions and all kernel corrections. -/
abbrev closedSectionObstructionGroup :=
  (relationSheaf e).obj.obj (op O) ⧸
    InvariantSectionObstruction.corrections (ρ).toAddMonoidHom δ

/-- The computed obstruction of a closed invariant section. -/
def closedSectionObstruction :
    (invariantSheaf e').obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj O)) →+
      closedSectionObstructionGroup e e' g r hp hq O :=
  (InvariantSectionObstruction.obstruction (ρ).toAddMonoidHom δ
    (closedSourceRestriction_surjective e e' g r hp hq O hO)).comp
      ((invariantInclusion e').hom.app _).hom.toAddMonoidHom

/-- Vanishing is equivalent to lifting through the actual structure-sheaf morphism. -/
theorem closedSectionObstruction_eq_zero_iff
    (t : (invariantSheaf e').obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj O))) :
    closedSectionObstruction e e' g r hp hq O hO t = 0 ↔
      ∃ s : (invariantSheaf e).obj.obj (op O), (m).c.app (op O) s = t := by
  exact (InvariantSectionObstruction.obstruction_eq_zero_iff (ρ).toAddMonoidHom δ
    (closedSourceRestriction_surjective e e' g r hp hq O hO)
    ((invariantInclusion e').hom.app _ t)).trans
      (invariantMap_section_lift_iff e e' g r hp hq O t).symm

/-- Any chosen source lift computes the same obstruction of the closed invariant section. -/
theorem closedSectionObstruction_of_lift
    (t : (invariantSheaf e').obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj O)))
    (a : (sourceSheaf e).obj.obj (op O))
    (ha : ρ a = (invariantInclusion e').hom.app _ t) :
    closedSectionObstruction e e' g r hp hq O hO t =
      InvariantSectionObstruction.defect (ρ).toAddMonoidHom δ a := by
  dsimp only [closedSectionObstruction, AddMonoidHom.comp_apply]
  exact (congrArg (InvariantSectionObstruction.obstruction (ρ).toAddMonoidHom δ
    (closedSourceRestriction_surjective e e' g r hp hq O hO)) ha.symm).trans
      (InvariantSectionObstruction.obstruction_restrict (ρ).toAddMonoidHom δ
        (closedSourceRestriction_surjective e e' g r hp hq O hO) a)

/-- The sheaf comparison is onto on this open exactly when every computed obstruction vanishes. -/
theorem invariantMap_section_surjective_iff :
    Function.Surjective ((m).c.app (op O)) ↔
      closedSectionObstruction e e' g r hp hq O hO = 0 := by
  constructor
  · intro h
    ext t
    exact (closedSectionObstruction_eq_zero_iff e e' g r hp hq O hO t).mpr (h t)
  · intro h t
    apply (closedSectionObstruction_eq_zero_iff e e' g r hp hq O hO t).mp
    exact DFunLike.congr_fun h t

/-- The actual structure-sheaf image is the kernel of the obstruction homomorphism. -/
theorem invariantMap_section_range :
    ((m).c.app (op O)).hom.toAddMonoidHom.range =
      (closedSectionObstruction e e' g r hp hq O hO).ker := by
  ext t
  exact (closedSectionObstruction_eq_zero_iff e e' g r hp hq O hO t).symm

end FLT.Mazur.RelativeRelationOrbit
