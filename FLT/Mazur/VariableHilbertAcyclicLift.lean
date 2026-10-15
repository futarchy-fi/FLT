/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSourceIntersection

/-!
# Constructing original Hilbert maps from acyclic translated classes

An actual acyclic degree-d divisor class constructs the Hilbert parameter
map on the unchanged test. Pairing it with the chosen translation coordinate
constructs a map into the original variable chart, with exactly the desired
Picard class. No source map or equal-class witness is supplied in advance.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {T : Over (Spec (.of R))} (s : (relativeFppfSheaf f).obj.obj (op T)) (v : T ⟶ V)
  (hs : s * (relativeFppfSheaf f).obj.map v.op c ∈
    (acyclicDegreePicardSubfunctor f d).obj (op T))

/-- The original degree chart provides the actual parameter of the translated divisor class. -/
def acyclicTranslationParameter : T ⟶ acyclicHilbertTest f d :=
  (((acyclicHilbertPicardIso f d hL).app (op T)).toEquiv.symm
    ⟨s * (relativeFppfSheaf f).obj.map v.op c, hs⟩).down

/-- The constructed Hilbert parameter has the specified untranslated original divisor class. -/
theorem acyclicTranslationParameter_class :
    acyclicHilbertPicardPoint f d hL T (acyclicTranslationParameter f hL d V c s v hs) =
      s * (relativeFppfSheaf f).obj.map v.op c := by
  exact congrArg Subtype.val
    (((acyclicHilbertPicardIso f d hL).app (op T)).toEquiv.apply_symm_apply _)

/-- The independent translation coordinate and constructed parameter form an original chart map. -/
def acyclicTranslationLift : T ⟶ variableHilbertTest f d V :=
  variableHilbertLift f d V v (acyclicTranslationParameter f hL d V c s v hs)

/-- The lift keeps the supplied translation coordinate exactly. -/
@[reassoc]
theorem acyclicTranslationLift_base :
    acyclicTranslationLift f hL d V c s v hs ≫ variableHilbertBase f d V = v :=
  prod.lift_fst _ _

/-- The constructed lift has the desired original Picard class on the entire test. -/
theorem acyclicTranslationLift_class :
    (relativeFppfSheaf f).obj.map (acyclicTranslationLift f hL d V c s v hs).op
      (variableChartSection f hL d V c) = s := by
  rw [variableChartSection_map, acyclicTranslationLift, variableHilbertPoint_lift,
    acyclicTranslationParameter_class, mul_div_cancel_right]

/-- Every actual original chart map is recovered from its class and its translation coordinate. -/
theorem acyclicTranslationLift_unique (a : T ⟶ variableHilbertTest f d V)
    (hv : a ≫ variableHilbertBase f d V = v)
    (ha : (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) = s) :
    a = acyclicTranslationLift f hL d V c s v hs := by
  apply variableHilbertPoint_injective_over f d hL V c
  · exact hv.trans (acyclicTranslationLift_base f hL d V c s v hs).symm
  · rw [← variableChartSection_map, ← variableChartSection_map, ha,
      acyclicTranslationLift_class]

end FLT.Mazur.HilbertChart
