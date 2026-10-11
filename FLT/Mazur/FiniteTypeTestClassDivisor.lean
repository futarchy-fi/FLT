/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicPointedAbelEquivalence
public import FLT.Mazur.FiniteTypeTestLineDivisor

/-!
# The full Abel inverse for all acyclic classes on all test schemes

For a proper flat geometrically integral family over a finite-type integer
ring, every geometric acyclic rank-one class on every test scheme determines
a unique full relative Cartier divisor. Both the test and its line are arbitrary.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X Y S : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ S}
  {q : Y ⟶ Spec (.of R)} {g : S ⟶ Spec (.of R)}
  [IsProper q] [Flat q] [GeometricallyIntegral q] (h : IsPullback a f q g)
  (c : RelativePic f) (hc : RelativeGeometricAcyclicRankOne f c)

include h hc in
/-- Every intrinsic acyclic class on the arbitrary test has an actual full relative divisor. -/
theorem finiteTypeTestClass_divisor_exists :
    ∃ D : AcyclicRankOneRelativeDivisor f, abel f D.val = c := by
  obtain ⟨L, hL, hLc, hA⟩ := hc
  let D := finiteTypeTestLineDivisor h L hL hA
  have hN := (finiteTypeTest_geometricAcyclicRankOne_iff_actual h L hL).mp hA
  have hD : AcyclicRankOne f (divisorLineBundle D.val.val.val D.val.val.property) :=
    (acyclicRankOne_relativeClass_iff f hL
      D.val.val.property.divisorLineBundle_locallyFreeRankOne D.val.property.symm).mp hN
  exact ⟨⟨D.val.val, D.property, hD⟩, D.val.property.trans hLc⟩

/-- The inverse divisor of an arbitrary acyclic relative class on an unrestricted test. -/
def finiteTypeTestClassDivisor : AcyclicRankOneRelativeDivisor f :=
  (finiteTypeTestClass_divisor_exists h c hc).choose

/-- The constructed full divisor has the independently specified test class. -/
theorem finiteTypeTestClassDivisor_class : abel f (finiteTypeTestClassDivisor h c hc).val = c :=
  (finiteTypeTestClass_divisor_exists h c hc).choose_spec

/-- Every full relative Cartier competitor equals the constructed divisor. -/
theorem finiteTypeTestClassDivisor_unique (D : Divisor X) (hD : Flat (D.val.subschemeι ≫ f))
    (hDc : abel f D = c) : D = (finiteTypeTestClassDivisor h c hc).val := by
  let E := finiteTypeTestClassDivisor h c hc
  let M := divisorLineBundle E.val.val E.val.property
  have hM := E.val.property.divisorLineBundle_locallyFreeRankOne
  let d : RelativeFiber f M hM :=
    ⟨⟨D, hDc.trans (finiteTypeTestClassDivisor_class h c hc).symm⟩, hD⟩
  let e : RelativeFiber f M hM := ⟨⟨E.val, rfl⟩, E.property.1⟩
  let _ : Surjective f := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton f M hM E.property.2.2
  exact congrArg (fun z : RelativeFiber f M hM ↦ z.val.val) (Subsingleton.elim d e)

include h hc in
/-- All acyclic classes, including independently varying lines, have a unique full Abel inverse. -/
theorem finiteTypeTestClassDivisor_existsUnique :
    ∃! D : Divisor X, Flat (D.val.subschemeι ≫ f) ∧ abel f D = c :=
  ⟨(finiteTypeTestClassDivisor h c hc).val,
    ⟨(finiteTypeTestClassDivisor h c hc).property.1, finiteTypeTestClassDivisor_class h c hc⟩,
    fun D hD ↦ finiteTypeTestClassDivisor_unique h c hc D hD.1 hD.2⟩

end FLT.Mazur.CartierAbel
