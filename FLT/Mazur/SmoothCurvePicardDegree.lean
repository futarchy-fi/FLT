/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReducedCurvePicardDegree
public import FLT.Mazur.SmoothGeometricallyReduced
public import FLT.Mazur.SmoothDimensionBound

/-!
# Degree on arbitrary smooth proper curves

Smoothness supplies reducedness and the curve dimension bound. The resulting
degree homomorphism therefore requires neither connectedness nor integrality.
Its degree is the original H0 minus H1 difference on actual line sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]

/-- Tensor degree is additive on every smooth proper relative-dimension-one curve. -/
theorem curveSheafDegree_smooth_line_tensor {L N : X.Modules}
    (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N) :
    curveSheafDegree f (ModuleSheafTensor.tensor N L) =
      curveSheafDegree f N + curveSheafDegree f L := by
  have := SmoothOfRelativeDimension.smooth 1 f
  have := Approximation.isReduced_of_smooth_field f
  exact curveSheafDegree_reduced_line_tensor f (topologicalKrullDim_le_one_of_smooth f) hL hN

end FLT.Mazur.FCurve

namespace FLT.Mazur.SchemePicard

open FCurve

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]

/-- Degree is additive on actual Picard classes of any smooth proper curve. -/
theorem smooth_degree_mul (a b : Pic X) : degree f (a * b) = degree f a + degree f b := by
  induction a using inductionOn with | h M hM =>
    induction b using inductionOn with | h N hN =>
      exact curveSheafDegree_smooth_line_tensor f hN hM

/-- The degree homomorphism derived solely from smooth proper curve hypotheses. -/
def smoothDegreeHom : Pic X →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (degree f a)
  map_one' := degree_one f
  map_mul' := smooth_degree_mul f

/-- The degree-zero subgroup of a smooth proper curve's actual Picard group. -/
def smoothDegreeZeroSubgroup : Subgroup (Pic X) := (smoothDegreeHom f).ker

/-- Membership is exactly zero cohomological degree. -/
@[simp]
lemma mem_smoothDegreeZeroSubgroup (a : Pic X) :
    a ∈ smoothDegreeZeroSubgroup f ↔ degree f a = 0 := Iff.rfl

/-- Field extension preserves and detects degree zero on smooth proper curves. -/
theorem mem_smoothDegreeZeroSubgroup_field_baseChange_iff
    {K : Type} [Field K] {P : Scheme}
    {p : P ⟶ X} {q : P ⟶ Spec (CommRingCat.of K)}
    [IsProper q] [SmoothOfRelativeDimension 1 q]
    {g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
    (h : IsPullback p q f g) (a : Pic X) :
    pullback p a ∈ smoothDegreeZeroSubgroup q ↔ a ∈ smoothDegreeZeroSubgroup f := by
  rw [mem_smoothDegreeZeroSubgroup, mem_smoothDegreeZeroSubgroup, degree_field_baseChange h]

end FLT.Mazur.SchemePicard
