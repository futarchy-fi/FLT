/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationLinearSections
public import FLT.Mazur.LineRestrictionHZero
public import FLT.Mazur.PolygonLineHZero

/-!
# Actual component H0 endpoint maps

The linear normalization coordinates retain both original node branches.
Each endpoint lands in the actual common node coefficient, so no choice of
node frame or polynomial coordinates is required here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.PolygonComponentHZeroEndpoints

open FCurve PolygonPinching LinePullbackRestriction PolygonNormalizationLinearSections

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type u) [Field K] (n : ℕ) (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (L : C.left.Modules)

/-- The actual pullback coefficient at one original node. -/
abbrev nodeLine (i : Fin n) :=
  (Scheme.Modules.pullback (nodeι K n i ≫ q).left).obj L

/-- Restriction from component i to its zero endpoint in the common node line. -/
def zeroMap (i : Fin n) :
    ModuleScalarH (component K).hom (componentLine K n p L i) 0 →ₗ[K]
      ModuleScalarH (point K).hom (nodeLine K n q L i) 0 :=
  h0Along (ProjectiveLine.zeroSection K) (componentι K n i ≫ p) (nodeι K n i ≫ q)
    (PolygonNodeIncidence.zero_node K n hn p q h i) L

/-- Restriction from the adjacent component to its infinity endpoint at the same node. -/
def infinityMap (i : Fin n) :
    ModuleScalarH (component K).hom (componentLine K n p L (next hn i)) 0 →ₗ[K]
      ModuleScalarH (point K).hom (nodeLine K n q L i) 0 :=
  h0Along (ProjectiveLine.infinitySection K) (componentι K n (next hn i) ≫ p)
    (nodeι K n i ≫ q) (PolygonNodeIncidence.infinity_node K n hn p q h i) L

variable (hL : LocallyFreeRankOne L)

/-- The linear zero endpoint recovers the original normalization branch section. -/
theorem zeroMap_component (i : Fin n)
    (x : ModuleScalarH C.hom
      ((pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L)) 0) :
    moduleScalarH0Equiv (point K).hom (nodeLine K n q L i)
        (zeroMap K n hn p q h L i (componentEquiv K n p L x i)) =
      (sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L).app ⊤
        ((PolygonLineNormalization.branch K n hn p q h L hL false).app ⊤
          (moduleScalarH0Equiv C.hom _ x)) := by
  rw [zeroMap, h0Along_sections, componentEquiv_apply, componentMap_sections]
  exact (congrArg (fun f ↦ f.app ⊤ (moduleScalarH0Equiv C.hom _ x))
    (PolygonLineNodeRestriction.zero_branch K n hn p q h L hL i)).symm

/-- The linear infinity endpoint recovers the other original normalization branch. -/
theorem infinityMap_component (i : Fin n)
    (x : ModuleScalarH C.hom
      ((pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L)) 0) :
    moduleScalarH0Equiv (point K).hom (nodeLine K n q L i)
        (infinityMap K n hn p q h L i (componentEquiv K n p L x (next hn i))) =
      (sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L).app ⊤
        ((PolygonLineNormalization.branch K n hn p q h L hL true).app ⊤
          (moduleScalarH0Equiv C.hom _ x)) := by
  rw [infinityMap, h0Along_sections, componentEquiv_apply, componentMap_sections]
  exact (congrArg (fun f ↦ f.app ⊤ (moduleScalarH0Equiv C.hom _ x))
    (PolygonLineNodeRestriction.infinity_branch K n hn p q h L hL i)).symm

end FLT.Mazur.PolygonComponentHZeroEndpoints
