/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonReflectionMarkingLine
public import FLT.Mazur.DivisorLineSectionIdealTransport
public import FLT.Mazur.DivisorLineSectionIdentity
public import FLT.Mazur.DivisorLineSectionTriangle

/-!
# Involutivity on the original polygon marking line

Two full-curve reflections give the original pullback unitor on the marked
line, with the actual ideal reindexing and composite-map transport retained.
The same equation holds on all marking-line tensor powers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonReflection tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Double reflection retains the original marked Cartier ideal exactly. -/
theorem twiceReflectedIdeal_eq (a : Kˣ) (i : Fin n) :
    (sectionMap K n p a i).ker =
      (sectionMap K n p (a⁻¹)⁻¹ (reflectIndex (reflectIndex i))).ker := by
  rw [inv_inv, reflectIndex_reflectIndex]

/-- The second reflection comparison with its original source marking retained. -/
irreducible_def reflectionSecondLineIso (a : Kˣ) (i : Fin n) :
    (Scheme.Modules.pullback (polygonReflection K hn p q h).left).obj
      (pointLine K n hn p q h a i) ≅ pointLine K n hn p q h a⁻¹ (reflectIndex i) :=
  (Scheme.Modules.pullback _).mapIso
    (divisorLineBundleEqIso (twiceReflectedIdeal_eq K n p a i)
      (section_cartier K n p hn q h a i).1
      (section_cartier K n p hn q h (a⁻¹)⁻¹ (reflectIndex (reflectIndex i))).1) ≪≫
    reflectionLineIso K n hn p q h a⁻¹ (reflectIndex i)

/-- The second reflected comparison preserves the original canonical section. -/
theorem reflectionSecondLineIso_section (a : Kˣ) (i : Fin n) :
    DivisorLineSectionCompatible (polygonReflection K hn p q h).left
      (section_cartier K n p hn q h a i).1
      (section_cartier K n p hn q h a⁻¹ (reflectIndex i)).1
      (reflectionSecondLineIso K n hn p q h a i) := by
  rw [reflectionSecondLineIso_def]
  exact (reflectionLineIso_section K n hn p q h a⁻¹ (reflectIndex i)).sourceIdealEq
    (twiceReflectedIdeal_eq K n p a i)

/-- Double reflection is the identity on the complete original underlying scheme. -/
theorem reflection_involutive_left :
    (polygonReflection K hn p q h).left ≫ (polygonReflection K hn p q h).left =
      𝟙 C.left :=
  congrArg Over.Hom.left (polygonReflection_involutive K hn p q h)

/-- Double reflection is the actual pullback unitor on the original marked line. -/
theorem reflectionLineIso_involutive (a : Kˣ) (i : Fin n) :
    LinePullbackTriangle (polygonReflection K hn p q h).left
      (polygonReflection K hn p q h).left (𝟙 C.left)
      (reflection_involutive_left K n hn p q h)
      (reflectionSecondLineIso K n hn p q h a i)
      (reflectionLineIso K n hn p q h a i)
      ((Scheme.Modules.pullbackId C.left).app (pointLine K n hn p q h a i)) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (reflectionSecondLineIso_section K n hn p q h a i)
    (reflectionLineIso_section K n hn p q h a i)
    (divisorLineSectionCompatible_id (section_cartier K n p hn q h a i).1)

/-- Involutivity retains every tensor degree of the original marking line. -/
theorem reflectionLineIso_involutive_power (a : Kˣ) (i : Fin n) (d : ℕ) :
    LinePullbackTriangle (polygonReflection K hn p q h).left
      (polygonReflection K hn p q h).left (𝟙 C.left)
      (reflection_involutive_left K n hn p q h)
      (tensorPowerPullbackComparison _ (reflectionSecondLineIso K n hn p q h a i) d)
      (tensorPowerPullbackComparison _ (reflectionLineIso K n hn p q h a i) d)
      (tensorPowerPullbackComparison _
        ((Scheme.Modules.pullbackId C.left).app (pointLine K n hn p q h a i)) d) :=
  (reflectionLineIso_involutive K n hn p q h a i).tensorPower d

end FLT.Mazur.PolygonMarkedSections
