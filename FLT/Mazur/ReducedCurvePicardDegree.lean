/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReducedCurveLineTensorDegree
public import FLT.Mazur.PicardDegreeFieldBaseChange

/-!
# Degree homomorphisms on reduced proper curves

Tensor additivity defines the degree homomorphism and its degree-zero subgroup
without an integral or connected hypothesis. Field base change preserves and
reflects membership whenever both curves are reduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemePicard

open FCurve

variable {k : Type} [Field k] {X : Scheme} [IsReduced X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hd : topologicalKrullDim X ≤ 1)

include hd in
/-- Degree is additive for actual Picard products on a reduced proper curve. -/
lemma reduced_degree_mul (a b : Pic X) : degree f (a * b) = degree f a + degree f b := by
  induction a using inductionOn with | h M hM =>
    induction b using inductionOn with | h N hN =>
      exact curveSheafDegree_reduced_line_tensor f hd hN hM

/-- The actual cohomological degree homomorphism of a reduced proper curve. -/
def reducedDegreeHom : Pic X →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (degree f a)
  map_one' := degree_one f
  map_mul' := reduced_degree_mul f hd

include hd in
/-- Duality negates degree on a reduced proper curve. -/
lemma reduced_degree_inv (a : Pic X) : degree f a⁻¹ = -degree f a :=
  congrArg Multiplicative.toAdd ((reducedDegreeHom f hd).map_inv a)

include hd in
/-- Integral powers scale degree on a reduced proper curve. -/
lemma reduced_degree_zpow (a : Pic X) (n : ℤ) : degree f (a ^ n) = n * degree f a := by
  have h := congrArg Multiplicative.toAdd ((reducedDegreeHom f hd).map_zpow a n)
  change degree f (a ^ n) = n • degree f a at h
  simpa only [zsmul_eq_mul, Int.cast_id] using h

/-- Degree-zero classes form an actual subgroup, including on disconnected reduced curves. -/
def reducedDegreeZeroSubgroup : Subgroup (Pic X) := (reducedDegreeHom f hd).ker

/-- Membership in the subgroup is exactly vanishing of cohomological degree. -/
@[simp]
lemma mem_reducedDegreeZeroSubgroup (a : Pic X) :
    a ∈ reducedDegreeZeroSubgroup f hd ↔ degree f a = 0 := Iff.rfl

/-- Field extension detects degree-zero membership for reduced proper curves. -/
theorem mem_reducedDegreeZeroSubgroup_field_baseChange_iff
    {K : Type} [Field K] {P : Scheme} [IsReduced P]
    {p : P ⟶ X} {q : P ⟶ Spec (CommRingCat.of K)} [IsProper q]
    {g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
    (h : IsPullback p q f g) (hdP : topologicalKrullDim P ≤ 1) (a : Pic X) :
    pullback p a ∈ reducedDegreeZeroSubgroup q hdP ↔ a ∈ reducedDegreeZeroSubgroup f hd := by
  rw [mem_reducedDegreeZeroSubgroup, mem_reducedDegreeZeroSubgroup, degree_field_baseChange h]

end FLT.Mazur.SchemePicard
