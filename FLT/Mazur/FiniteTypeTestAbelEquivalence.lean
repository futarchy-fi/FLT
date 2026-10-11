/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeTestClassDivisorNaturality

/-!
# The intrinsic Abel equivalence on every test scheme

For a proper flat geometrically integral family over a finite-type integer
ring, the acyclic full relative divisors correspond to the geometric acyclic
relative Picard classes on every test. The classes allow all line bundles on
the test total space; no supplied line model or Noetherian test is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)

/-- The actual Abel class of an acyclic divisor belongs to the geometric subfunctor. -/
def finiteTypeTestAbel (D : AcyclicRankOneRelativeDivisor f) :
    {c : RelativePic f // RelativeGeometricAcyclicRankOne f c} :=
  ⟨abel f D.val, divisorLineBundle D.val.val D.val.property,
    D.val.property.divisorLineBundle_locallyFreeRankOne, rfl,
    (finiteTypeTest_geometricAcyclicRankOne_iff_actual h _
      D.val.property.divisorLineBundle_locallyFreeRankOne).mpr D.property.2⟩

/-- The full-divisor inverse recovers each independently specified relative class. -/
lemma finiteTypeTestAbel_right_inv
    (c : {c : RelativePic f // RelativeGeometricAcyclicRankOne f c}) :
    finiteTypeTestAbel h (finiteTypeTestClassDivisor h c.val c.property) = c :=
  Subtype.ext (finiteTypeTestClassDivisor_class h c.val c.property)

/-- The inverse recovers the original full divisor, including its nonreduced ideal. -/
lemma finiteTypeTestAbel_left_inv (D : AcyclicRankOneRelativeDivisor f) :
    finiteTypeTestClassDivisor h (finiteTypeTestAbel h D).val
      (finiteTypeTestAbel h D).property = D := by
  apply Subtype.ext
  exact (finiteTypeTestClassDivisor_unique h _ _ D.val D.property.1 rfl).symm

/-- The intrinsic Abel correspondence on unrestricted tests and independently varying lines. -/
def finiteTypeTestAbelEquiv : AcyclicRankOneRelativeDivisor f ≃
    {c : RelativePic f // RelativeGeometricAcyclicRankOne f c} where
  toFun := finiteTypeTestAbel h
  invFun c := finiteTypeTestClassDivisor h c.val c.property
  left_inv := finiteTypeTestAbel_left_inv h
  right_inv := finiteTypeTestAbel_right_inv h

end FLT.Mazur.CartierAbel
