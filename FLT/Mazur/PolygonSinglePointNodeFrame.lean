/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointEndpointScalars

/-!
# Cancellation in every single-point node frame

The original canonical divisor section is nonzero at every polygon node.
This is proved by its actual marked or unmarked component comparison, and
lets the node matching equations be read as equations of base-field scalars.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.PolygonSinglePointNodeFrame

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonSinglePointHZeroFrames PolygonSinglePointEndpointScalars LinePullbackRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K]

/-- The pulled-back unit section cancels scalars at an arbitrary component endpoint. -/
theorem unit_cancel (s : point K ⟶ component K) :
    Function.Injective (fun r : Γ(Spec (.of K), ⊤) ↦ r •
      pullGlobal s.left (structureModule (ProjectiveLine.scheme K))
        (1 : Γ(ProjectiveLine.scheme K, ⊤))) := by
  have hu : (modulePullbackUnitIso s.left).hom.app ⊤
      (pullGlobal s.left (structureModule (ProjectiveLine.scheme K))
        (1 : Γ(ProjectiveLine.scheme K, ⊤))) = (1 : Γ(Spec (.of K), ⊤)) := by
    exact (modulePullbackUnitIso_unit s.left ⊤ 1).trans (map_one (s.left.app ⊤).hom)
  intro r t he
  have hh := congrArg ((modulePullbackUnitIso s.left).hom.app ⊤) he
  simpa only [Hom.app_smul, hu, smul_eq_mul, mul_one] using hh

variable (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- The original canonical node section cancels actual section-ring scalars. -/
theorem canonical_cancel (i : Fin n) :
    Function.Injective (fun r : Γ(Spec (.of K), ⊤) ↦ r •
      pullGlobal (nodeι K n i ≫ q).left _ (canonicalSection K n hn p q h a j m)) := by
  by_cases hi : i = j
  · subst i
    apply h0Along_canonical_cancel (ProjectiveLine.zeroSection K)
      (componentι K n j ≫ p) (nodeι K n j ≫ q)
      (PolygonNodeIncidence.zero_node K n hn p q h j)
      (ownComponentPowerIso K n hn p q h a j m) _ _
      (own_canonical K n hn p q h a j m)
    exact ProjectiveLineMarkedEndpointSections.chart_canonical_cancel K a m
      (ProjectiveLine.left K) a (Units.ne_zero a) (ProjectiveLineMarkedCharts.left_ideal K a)
  · apply h0Along_canonical_cancel (ProjectiveLine.zeroSection K)
      (componentι K n i ≫ p) (nodeι K n i ≫ q)
      (PolygonNodeIncidence.zero_node K n hn p q h i)
      (otherComponentPowerIso K n hn p q h a hi m) _ _
      (other_canonical K n hn p q h a j m ⟨i, hi⟩)
    exact unit_cancel K (ProjectiveLine.zeroSection K)

/-- The original node frame also cancels base-field scalars without choosing a new basis. -/
theorem scalar_cancel (i : Fin n) :
    Function.Injective (fun r : K ↦ (Scheme.ΓSpecIso (.of K)).inv r •
      pullGlobal (nodeι K n i ≫ q).left _ (canonicalSection K n hn p q h a j m)) :=
  (canonical_cancel K n hn p q h a j m i).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).injective

end FLT.Mazur.PolygonSinglePointNodeFrame
