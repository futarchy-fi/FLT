/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveDegreeFieldBaseChange
public import FLT.Mazur.CurvePicardDegree
public import FLT.Mazur.SchemePicardPullback

/-!
# Field base change preserves degree on actual Picard classes

Sheaf-level degree invariance descends to actual isomorphism classes of line
sheaves. In particular, pullback preserves and reflects degree zero. No Picard
representability assertion is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SchemePicard
open FCurve
variable {k K : Type} [Field k] [Field K] {P X : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ Spec (CommRingCat.of K)}
  {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
  {g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
  (h : IsPullback p q f g)

include h

/-- Pullback of an actual Picard class along field base change preserves degree. -/
theorem degree_field_baseChange (a : Pic X) : degree q (pullback p a) = degree f a := by
  induction a using inductionOn with | h M hM =>
    let _ : M.IsFinitePresentation := hM.isFinitePresentation
    exact curveSheafDegree_field_baseChange h M

/-- Field extension preserves and reflects degree zero for actual Picard classes. -/
theorem degree_zero_field_baseChange_iff (a : Pic X) :
    degree q (pullback p a) = 0 ↔ degree f a = 0 := by
  rw [degree_field_baseChange h]

/-- For integral curves, the degree-zero subgroup is detected after field extension. -/
theorem mem_degreeZeroSubgroup_field_baseChange_iff
    [IsIntegral X] [IsIntegral P] [IsProper q]
    (hdX : topologicalKrullDim X ≤ 1) (hdP : topologicalKrullDim P ≤ 1) (a : Pic X) :
    pullback p a ∈ degreeZeroSubgroup q hdP ↔ a ∈ degreeZeroSubgroup f hdX := by
  rw [mem_degreeZeroSubgroup, mem_degreeZeroSubgroup, degree_field_baseChange h]

end FLT.Mazur.SchemePicard
