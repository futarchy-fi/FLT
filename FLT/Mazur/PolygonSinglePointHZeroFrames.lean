/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointHZeroCoordinates

/-!
# Canonical frames for single-point H0 coordinates

The component H0 coordinates agree with the actual coefficient comparisons on
sections. The original canonical divisor section becomes the marked canonical
section on its own component and the unit on every other component.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.PolygonSinglePointHZeroFrames

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonNormalizationLinearSections PolygonSinglePointHZeroCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K]

/-- Unit-coefficient H0 on P1 is its actual scalar section in the canonical frame. -/
theorem unit_sections (x : ModuleScalarH (ProjectiveLine.toBase K)
    (structureModule (ProjectiveLine.scheme K)) 0) :
    moduleScalarH0Equiv (ProjectiveLine.toBase K) _ x =
      structureScalarMap (ProjectiveLine.toBase K)
        (ProjectiveLineConstantSections.h0Equiv K
          (moduleScalarHUnitEquiv (ProjectiveLine.toBase K) 0 x)) := by
  have he := congrArg (scalarH0Equiv (ProjectiveLine.toBase K))
    ((scalarH0ConstantsEquiv (ProjectiveLine.toBase K)
      (ProjectiveLineConstantSections.constant_sections K)).apply_symm_apply
        (moduleScalarHUnitEquiv (ProjectiveLine.toBase K) 0 x))
  change scalarH0Equiv (ProjectiveLine.toBase K) (scalarH0Constants _ _) = _ at he
  rw [scalarH0Equiv_constants] at he
  exact he.symm

variable (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- The marked cohomology coordinate is exactly transport through the original line comparison. -/
theorem own_sections (x : ModuleScalarH (component K).hom
    (componentLine K n p (pointPower K n hn p q h a j m) j) 0) :
    moduleScalarH0Equiv (component K).hom _ (ownEquiv K n hn p q h a j m x) =
      (ownComponentPowerIso K n hn p q h a j m).hom.app ⊤
        (moduleScalarH0Equiv (component K).hom _ x) :=
  moduleScalarH0Equiv_naturality (component K).hom _ x

/-- An unmarked component section is its scalar coordinate in the original unit frame. -/
theorem other_sections (i : {i : Fin n // i ≠ j})
    (x : ModuleScalarH (component K).hom
      (componentLine K n p (pointPower K n hn p q h a j m) i.val) 0) :
    (otherComponentPowerIso K n hn p q h a i.property m).hom.app ⊤
        (moduleScalarH0Equiv (component K).hom _ x) =
      structureScalarMap (ProjectiveLine.toBase K) (otherEquiv K n hn p q h a j m i x) := by
  rw [← moduleScalarH0Equiv_naturality]
  exact unit_sections K _

/-- The marked comparison carries the original canonical section to the marked P1 section. -/
theorem own_canonical :
    (ownComponentPowerIso K n hn p q h a j m).hom.app ⊤
        (pullGlobal (componentι K n j ≫ p).left _
          (divisorSection ((PolygonMarkedSections.section_cartier K n p hn q h a j).1.pow m)
            ⊤)) =
      divisorSection ((ProjectiveLineMarkedCharts.relativeCartier K a).1.pow m) ⊤ :=
  pullGlobal_section_map _ _ _ _ (ownComponentPowerIso_section K n hn p q h a j m)

/-- The canonical section is the unit under every unmarked comparison. -/
theorem other_canonical (i : {i : Fin n // i ≠ j}) :
    (otherComponentPowerIso K n hn p q h a i.property m).hom.app ⊤
        (pullGlobal (componentι K n i.val ≫ p).left _
          (divisorSection ((PolygonMarkedSections.section_cartier K n p hn q h a j).1.pow m)
            ⊤)) = (1 : Γ(ProjectiveLine.scheme K, ⊤)) := by
  apply pullGlobal_section_map _ _ (𝟙 (structureModule (ProjectiveLine.scheme K)))
  simpa only [Category.comp_id] using
    otherComponentPowerIso_section K n hn p q h a i.property m

end FLT.Mazur.PolygonSinglePointHZeroFrames
