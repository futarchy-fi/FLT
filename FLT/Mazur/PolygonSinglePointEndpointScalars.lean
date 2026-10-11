/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSinglePointHZeroFrames
public import FLT.Mazur.LineRestrictionHZeroFrames
public import FLT.Mazur.PolygonHZeroIncidence

/-!
# Endpoint scalars of the original single-point powers

The marked component has the canonical P1 polynomial endpoint scalars.
Every unmarked component has the same scalar at both endpoints. All formulas
land in the original target coefficient through its incidence triangle.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

namespace FLT.Mazur.PolygonSinglePointEndpointScalars

open FCurve PolygonPinching PolygonSinglePointLineNormalization
open PolygonNormalizationLinearSections PolygonSinglePointHZeroCoordinates
open PolygonSinglePointHZeroFrames LinePullbackRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K]

/-- A pulled-back scalar section is that scalar times the pulled-back unit. -/
theorem unit_endpoint (s : point K ⟶ component K) (c : K) :
    pullGlobal s.left (structureModule (ProjectiveLine.scheme K))
        (structureScalarMap (ProjectiveLine.toBase K) c) =
      (Scheme.ΓSpecIso (.of K)).inv c •
        pullGlobal s.left (structureModule (ProjectiveLine.scheme K))
          (1 : Γ(ProjectiveLine.scheme K, ⊤)) := by
  have he := (pullGlobal s.left (structureModule (ProjectiveLine.scheme K))).map_smulₛₗ
    (structureScalarMap (ProjectiveLine.toBase K) c) (1 : Γ(ProjectiveLine.scheme K, ⊤))
  simpa only [smul_eq_mul, mul_one, PolygonCohomologyIncidence.section_scalar] using he

variable (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (j : Fin n) (m : ℕ)

/-- The original single-point divisor section, used as a frame at all nodes. -/
abbrev canonicalSection : Γ(pointPower K n hn p q h a j m, ⊤) :=
  divisorSection ((PolygonMarkedSections.section_cartier K n p hn q h a j).1.pow m) ⊤

/-- The marked zero endpoint has its normalized polynomial constant coefficient. -/
theorem own_zero (t : point K ⟶ C)
    (w : ProjectiveLine.zeroSection K ≫ (componentι K n j ≫ p) = t)
    (x : ModuleScalarH (component K).hom
      (componentLine K n p (pointPower K n hn p q h a j m) j) 0) :
    moduleScalarH0Equiv (point K).hom _
        (h0Along (ProjectiveLine.zeroSection K) (componentι K n j ≫ p) t w _ x) =
      (Scheme.ΓSpecIso (.of K)).inv
        ((ProjectiveLineMarkedHZero.polynomialEquiv K a m
          (ownEquiv K n hn p q h a j m x)).val.eval 0 / (-(a : K)) ^ m) •
        pullGlobal t.left _ (canonicalSection K n hn p q h a j m) := by
  apply h0Along_value _ _ _ _ (ownComponentPowerIso K n hn p q h a j m) _ _
    (own_canonical K n hn p q h a j m)
  rw [← own_sections]
  exact ProjectiveLineMarkedEndpointSections.zero_h0 K a m _

/-- The marked infinity endpoint has its leading polynomial coefficient. -/
theorem own_infinity (t : point K ⟶ C)
    (w : ProjectiveLine.infinitySection K ≫ (componentι K n j ≫ p) = t)
    (x : ModuleScalarH (component K).hom
      (componentLine K n p (pointPower K n hn p q h a j m) j) 0) :
    moduleScalarH0Equiv (point K).hom _
        (h0Along (ProjectiveLine.infinitySection K) (componentι K n j ≫ p) t w _ x) =
      (Scheme.ΓSpecIso (.of K)).inv
        ((ProjectiveLineMarkedHZero.polynomialEquiv K a m
          (ownEquiv K n hn p q h a j m x)).val.coeff m) •
        pullGlobal t.left _ (canonicalSection K n hn p q h a j m) := by
  apply h0Along_value _ _ _ _ (ownComponentPowerIso K n hn p q h a j m) _ _
    (own_canonical K n hn p q h a j m)
  rw [← own_sections]
  exact ProjectiveLineMarkedEndpointSections.infinity_h0 K a m _

/-- At either endpoint an unmarked component contributes its unique scalar coordinate. -/
theorem other_endpoint (i : {i : Fin n // i ≠ j})
    (s : point K ⟶ component K) (t : point K ⟶ C)
    (w : s ≫ (componentι K n i.val ≫ p) = t)
    (x : ModuleScalarH (component K).hom
      (componentLine K n p (pointPower K n hn p q h a j m) i.val) 0) :
    moduleScalarH0Equiv (point K).hom _ (h0Along s (componentι K n i.val ≫ p) t w _ x) =
      (Scheme.ΓSpecIso (.of K)).inv (otherEquiv K n hn p q h a j m i x) •
        pullGlobal t.left _ (canonicalSection K n hn p q h a j m) := by
  apply h0Along_value _ _ _ _ (otherComponentPowerIso K n hn p q h a i.property m) _ _
    (other_canonical K n hn p q h a j m i)
  rw [other_sections]
  exact unit_endpoint K s _

end FLT.Mazur.PolygonSinglePointEndpointScalars
