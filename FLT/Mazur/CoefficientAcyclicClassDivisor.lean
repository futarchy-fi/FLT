/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientAcyclicLineDivisor

/-!
# The full Abel inverse for all acyclic classes on coefficient tests

Every relative class on the test is allowed, with no requirement that it
be pulled back from the original model. Approximation supplies the full
Cartier ideal, and rank-one uniqueness removes all model and representative choices.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CommRing A] (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
  {X Y : Scheme.{0}} {a : X ⟶ Y} {f : X ⟶ Spec (.of A)}
  {q : Y ⟶ Spec (.of R)} [IsProper q] [Flat q] [GeometricallyIntegral q]
  (h : IsPullback a f q (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
  (c : RelativePic f) (hc : RelativeGeometricAcyclicRankOne f c)

include h hc in
/-- Every intrinsic acyclic class on the arbitrary test has an actual full relative divisor. -/
theorem coefficientClass_divisor_exists :
    ∃ D : AcyclicRankOneRelativeDivisor f, abel f D.val = c := by
  obtain ⟨L, hL, hLc, hA⟩ := hc
  let D := coefficientLineDivisor R h L hL hA
  have hN := (coefficientLine_geometricAcyclicRankOne_iff_actual R h L hL).mp hA
  have hD : AcyclicRankOne f (divisorLineBundle D.val.val.val D.val.val.property) :=
    (acyclicRankOne_relativeClass_iff f hL
      D.val.val.property.divisorLineBundle_locallyFreeRankOne D.val.property.symm).mp hN
  exact ⟨⟨D.val.val, D.property, hD⟩, D.val.property.trans hLc⟩

/-- The inverse divisor of an arbitrary acyclic relative class on a coefficient test. -/
def coefficientClassDivisor : AcyclicRankOneRelativeDivisor f :=
  (coefficientClass_divisor_exists R h c hc).choose

/-- The constructed full divisor has the independently specified test class. -/
theorem coefficientClassDivisor_class : abel f (coefficientClassDivisor R h c hc).val = c :=
  (coefficientClass_divisor_exists R h c hc).choose_spec

/-- Every full relative Cartier competitor equals the constructed divisor. -/
theorem coefficientClassDivisor_unique (D : Divisor X) (hD : Flat (D.val.subschemeι ≫ f))
    (hDc : abel f D = c) : D = (coefficientClassDivisor R h c hc).val := by
  let E := coefficientClassDivisor R h c hc
  let M := divisorLineBundle E.val.val E.val.property
  have hM := E.val.property.divisorLineBundle_locallyFreeRankOne
  let d : RelativeFiber f M hM :=
    ⟨⟨D, hDc.trans (coefficientClassDivisor_class R h c hc).symm⟩, hD⟩
  let e : RelativeFiber f M hM := ⟨⟨E.val, rfl⟩, E.property.1⟩
  let _ : Surjective f := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton f M hM E.property.2.2
  exact congrArg (fun z : RelativeFiber f M hM ↦ z.val.val) (Subsingleton.elim d e)

include h hc in
/-- All acyclic classes, including independently varying lines, have a unique full Abel inverse. -/
theorem coefficientClassDivisor_existsUnique :
    ∃! D : Divisor X, Flat (D.val.subschemeι ≫ f) ∧ abel f D = c :=
  ⟨(coefficientClassDivisor R h c hc).val,
    ⟨(coefficientClassDivisor R h c hc).property.1, coefficientClassDivisor_class R h c hc⟩,
    fun D hD ↦ coefficientClassDivisor_unique R h c hc D hD.1 hD.2⟩

end FLT.Mazur.CartierAbel
