/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonReflectionMarking
public import FLT.Mazur.PolygonSinglePointLineNormalization
public import FLT.Mazur.DivisorLineSectionCompatibility

/-!
# The marked line under full polygon reflection

The canonical line comparison lies over the actual reflection of the complete
polygon. It preserves the original canonical section, including at the nodes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonReflection divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Reflection has the canonical invertible comparison on the actual marking ideal. -/
theorem reflectionIdealComparison_isIso (a : Kˣ) (i : Fin n) :
    IsIso (idealModulePullbackHom (sectionMap K n p a⁻¹ (reflectIndex i)).ker
      (polygonReflection K hn p q h).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (section_cartier K n p hn q h a⁻¹ (reflectIndex i)).1
  rw [section_reflection_ideal]
  exact (section_cartier K n p hn q h a i).1

/-- The positive line of the reflected marking pulls back to the original marked line. -/
irreducible_def reflectionLineIso (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (polygonReflection K hn p q h).left).obj
      (pointLine K n hn p q h a⁻¹ (reflectIndex i)) ≅ pointLine K n hn p q h a i := by
  let _ := reflectionIdealComparison_isIso K n hn p q h a i
  exact divisorLinePullbackIsoOfEq _
    (section_cartier K n p hn q h a⁻¹ (reflectIndex i)).1
    (section_cartier K n p hn q h a i).1 (section_reflection_ideal K n hn p q h a i)

/-- The full-curve reflection comparison preserves the original vanishing section. -/
theorem reflectionLineIso_section (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (polygonReflection K hn p q h).left
      (section_cartier K n p hn q h a⁻¹ (reflectIndex i)).1
      (section_cartier K n p hn q h a i).1 (reflectionLineIso K n hn p q h a i) := by
  let _ := reflectionIdealComparison_isIso K n hn p q h a i
  rw [reflectionLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonMarkedSections
