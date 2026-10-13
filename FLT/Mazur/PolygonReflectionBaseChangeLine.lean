/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingBaseChange
public import FLT.Mazur.PolygonReflectionMarkingLine
public import FLT.Mazur.RelativeCartierMorphismBaseChange

/-!
# Reflection of the original marking line after arbitrary base change

Reflection on the original base-changed polygon preserves the actual marked
ideal and canonical section. Its line comparison commutes with base change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkingBaseChange
open PolygonPinching PolygonMarkedSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonReflection
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (a : Kˣ) (i : Fin n)

/-- The complete family reflection preserves the full original marked ideal. -/
theorem reflection_ideal :
    (markingIdeal K n p g a⁻¹ (reflectIndex i)).comap
        ((Over.pullback g).map (polygonReflection K hn p q h)).left =
      markingIdeal K n p g a i :=
  relativeCartierMorphismBaseChange_ideal _ g _ _
    (section_reflection_ideal K n hn p q h a i)

/-- The family reflection compares the actual positive marking lines. -/
irreducible_def reflectionLineIso :
    (Scheme.Modules.pullback
      ((Over.pullback g).map (polygonReflection K hn p q h)).left).obj
        (markingLine K n hn p q h g a⁻¹ (reflectIndex i)) ≅
      markingLine K n hn p q h g a i :=
  relativeCartierMorphismBaseChangeIso _ g _ _
    (section_cartier K n p hn q h a⁻¹ (reflectIndex i))
    (section_cartier K n p hn q h a i) (section_reflection_ideal K n hn p q h a i)

/-- Reflection preserves the original family marking's canonical section. -/
theorem reflectionLineIso_section :
    DivisorLineSectionCompatible
      ((Over.pullback g).map (polygonReflection K hn p q h)).left
      (markingIdeal_cartier K n hn p q h g a⁻¹ (reflectIndex i)).1
      (markingIdeal_cartier K n hn p q h g a i).1
      (reflectionLineIso K n hn p q h g a i) := by
  rw [reflectionLineIso_def]
  exact relativeCartierMorphismBaseChangeIso_section _ _ _ _ _ _ _

/-- Original reflection and arbitrary base change commute on the actual positive lines. -/
theorem reflectionLineIso_square :
    LinePullbackSquare
      ((Over.pullback g).map (polygonReflection K hn p q h)).left
      (pullback.fst C.hom g) (pullback.fst C.hom g)
      (polygonReflection K hn p q h).left
      (OverPullbackLocalPushout.map_isPullback g
        (polygonReflection K hn p q h)).w
      (markingLineIso K n hn p q h g a⁻¹ (reflectIndex i))
      (reflectionLineIso K n hn p q h g a i)
      (PolygonMarkedSections.reflectionLineIso K n hn p q h a i)
      (markingLineIso K n hn p q h g a i) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (markingLineIso_section K n hn p q h g a⁻¹ (reflectIndex i))
    (reflectionLineIso_section K n hn p q h g a i)
    (PolygonMarkedSections.reflectionLineIso_section K n hn p q h a i)
    (markingLineIso_section K n hn p q h g a i)

end FLT.Mazur.PolygonMarkingBaseChange
