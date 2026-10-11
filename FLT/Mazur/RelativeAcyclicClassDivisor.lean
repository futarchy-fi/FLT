/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeAcyclicPicardOpen
public import FLT.Mazur.AcyclicPointedAbelEquivalence

/-!
# Full divisors from relative-class acyclic tests

An arbitrary relative class on a locally Noetherian proper flat geometrically
integral family has a unique full divisor on each test where its geometric
acyclic rank-one condition holds. The original class need not be acyclic
on the whole original base, and the test base is unrestricted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (c : RelativePic f)
  (hc : RelativeGeometricAcyclicRankOne q (relativeMap q f p g h.w.symm c))

omit [GeometricallyIntegral f] in
include hc in
/-- Every representative of a geometrically acyclic relative-class test has the actual condition. -/
theorem relativeClass_test_actual (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hLc : relativeClass f (mk L hL) = c) :
    AcyclicRankOne q ((Scheme.Modules.pullback p).obj L) := by
  apply (geometricAcyclicRankOne_iff_actual f h L hL).mp
  apply (relativeGeometricAcyclicRankOne_mk q _ (hL.pullback p)).mp
  simpa only [← hLc, relativeMap_class, pullback_mk] using hc

include hc in
/-- An actual acyclic divisor with the prescribed relative class exists on the unrestricted test. -/
theorem relativeClass_test_divisor_exists :
    ∃ D : AcyclicRankOneRelativeDivisor q, abel q D.val = relativeMap q f p g h.w.symm c := by
  obtain ⟨L, hLc⟩ := relativePic_exists_line f c
  have hA := relativeClass_test_actual h c hc L.val L.property hLc
  let D := acyclicRankOneFamilyDivisor h L.val L.property hA.1 hA.2
  have hD : AcyclicRankOne q (divisorLineBundle D.val.val.val D.val.val.property) :=
    (acyclicRankOne_relativeClass_iff q (L.property.pullback p)
      D.val.val.property.divisorLineBundle_locallyFreeRankOne D.val.property.symm).mp hA
  refine ⟨⟨D.val.val, D.property, hD⟩, ?_⟩
  exact D.val.property.trans (congrArg (relativeMap q f p g h.w.symm) hLc)

/-- The full divisor of a relative-class test; no divisor is assumed in the test predicate. -/
def relativeClassTestDivisor : AcyclicRankOneRelativeDivisor q :=
  (relativeClass_test_divisor_exists h c hc).choose

/-- The constructed divisor has exactly the original pulled-back relative Picard class. -/
theorem relativeClassTestDivisor_class :
    abel q (relativeClassTestDivisor h c hc).val = relativeMap q f p g h.w.symm c :=
  (relativeClass_test_divisor_exists h c hc).choose_spec

/-- Uniqueness compares every full relative divisor, without acyclicity on the competitor. -/
theorem relativeClassTestDivisor_unique (D : Divisor P)
    (hD : Flat (D.val.subschemeι ≫ q))
    (hDc : abel q D = relativeMap q f p g h.w.symm c) :
    D = (relativeClassTestDivisor h c hc).val := by
  let E := relativeClassTestDivisor h c hc
  let L := divisorLineBundle E.val.val E.val.property
  have hL := E.val.property.divisorLineBundle_locallyFreeRankOne
  let a : RelativeFiber q L hL :=
    ⟨⟨D, hDc.trans (relativeClassTestDivisor_class h c hc).symm⟩, hD⟩
  let b : RelativeFiber q L hL := ⟨⟨E.val, rfl⟩, E.property.1⟩
  let _ : Surjective q := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton q L hL E.property.2.2
  exact congrArg (fun x : RelativeFiber q L hL ↦ x.val.val) (Subsingleton.elim a b)

include hc in
/-- The acyclic relative-class test determines a unique full relative Cartier divisor. -/
theorem relativeClassTestDivisor_existsUnique :
    ∃! D : Divisor P, Flat (D.val.subschemeι ≫ q) ∧
      abel q D = relativeMap q f p g h.w.symm c :=
  ⟨(relativeClassTestDivisor h c hc).val,
    ⟨(relativeClassTestDivisor h c hc).property.1, relativeClassTestDivisor_class h c hc⟩,
    fun D hD ↦ relativeClassTestDivisor_unique h c hc D hD.1 hD.2⟩

end FLT.Mazur.CartierAbel
