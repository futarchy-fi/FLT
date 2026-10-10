/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveLineTensorDegree
public import FLT.Mazur.SchemePicardGroup

/-!
# Degree on actual Picard classes

The Euler-characteristic degree descends through sheaf isomorphisms. On an
integral proper curve the tensor formula makes it a group homomorphism to the
integers. Its kernel is a subgroup of actual Picard classes, not a Picard scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemePicard
open FCurve
variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- Degree of a Picard class, computed from the cohomology of an actual representative. -/
def degree : Pic X → ℤ :=
  Quotient.lift (fun M : LineBundle X ↦ curveSheafDegree f M.val)
    (fun _ _ ⟨e⟩ ↦ curveSheafDegree_iso f e)

/-- The class degree retains the original sheaf-cohomology definition. -/
@[simp]
lemma degree_mk (M : X.Modules) (hM : LocallyFreeRankOne M) :
    degree f (mk M hM) = curveSheafDegree f M := rfl

/-- The trivial Picard class has degree zero. -/
@[simp]
lemma degree_one : degree f 1 = 0 := by
  change curveEulerCharacteristic f (structureModule X) -
    curveEulerCharacteristic f (structureModule X) = 0
  exact sub_self _

variable [IsIntegral X] [IsProper f] (hd : topologicalKrullDim X ≤ 1)

include hd in
/-- The degree of a product of actual Picard classes is the sum of their degrees. -/
lemma degree_mul (a b : Pic X) : degree f (a * b) = degree f a + degree f b := by
  induction a using inductionOn with | h M hM =>
    induction b using inductionOn with | h N hN =>
      exact curveSheafDegree_line_tensor f hd hN hM

/-- The degree homomorphism on the actual Picard group of an integral proper curve. -/
def degreeHom : Pic X →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (degree f a)
  map_one' := degree_one f
  map_mul' := degree_mul f hd

include hd in
/-- Duality negates degree on actual Picard classes. -/
@[simp]
lemma degree_inv (a : Pic X) : degree f a⁻¹ = -degree f a :=
  congrArg Multiplicative.toAdd ((degreeHom f hd).map_inv a)

include hd in
/-- Integral tensor powers multiply the degree by their exponent. -/
lemma degree_zpow (a : Pic X) (n : ℤ) : degree f (a ^ n) = n * degree f a := by
  have h := congrArg Multiplicative.toAdd ((degreeHom f hd).map_zpow a n)
  change degree f (a ^ n) = n • degree f a at h
  simpa only [zsmul_eq_mul, Int.cast_id] using h

/-- The degree-zero subgroup of actual line-bundle classes. -/
def degreeZeroSubgroup : Subgroup (Pic X) := (degreeHom f hd).ker

/-- Membership in the degree-zero subgroup uses the cohomological degree. -/
@[simp]
lemma mem_degreeZeroSubgroup (a : Pic X) : a ∈ degreeZeroSubgroup f hd ↔ degree f a = 0 :=
  Iff.rfl

end FLT.Mazur.SchemePicard
