/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonDirectPowerComparison
public import FLT.Mazur.LineEndpointTransport
public import FLT.Mazur.ProjectiveLineMarkedEndpointSections
/-!
# Divisor-power endpoint values in the actual common node line

Use the direct component comparison to transport the P1 H0 endpoint formulas.
Zero on component i and infinity on next(i) land in the same node pullback.
The canonical node section cancels scalars, so matching is an exact scalar
relation. This includes every positive polygon size.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.PolygonPowerNodeEndpoints
open FCurve PolygonPinching ProjectiveLineMarkedHZero
open ProjectiveLineMarkedCharts ProjectiveLineMarkedSectionTransition
open PolygonDivisorNormalizationPullback ProjectiveLineMarkedEndpointSections
private lemma zeroCanonical_injective (K : Type u) [Field K] (a : Kˣ) (m : ℕ) :
    Function.Injective (fun r : Γ(Spec (.of K), ⊤) ↦ r •
      pullGlobal (ProjectiveLine.zero K) (line K a m)
        (divisorSection ((relativeCartier K a).1.pow m) ⊤)) :=
  chart_canonical_cancel K a m (ProjectiveLine.left K) a (Units.ne_zero a) (left_ideal K a)

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (m : ℕ)

/-- The actual polygon divisor-power line. -/
abbrev polygonLine := divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a ^ m)
  ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m)

/-- The pullback of the polygon line to one specified node. -/
abbrev nodeLine (i : Fin n) :=
  (Scheme.Modules.pullback (nodeι K n i ≫ q).left).obj (polygonLine K n hn p q h a m)

/-- The canonical divisor-power section in the node line. -/
def canonical (i : Fin n) : Γ(nodeLine K n hn p q h a m i, ⊤) :=
  pullGlobal (nodeι K n i ≫ q).left _
    (divisorSection ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m) ⊤)

/-- Identify the zero endpoint line with the actual node line. -/
def zeroIso (i : Fin n) :
    (Scheme.Modules.pullback (ProjectiveLine.zero K)).obj (line K (a i) m) ≅
      nodeLine K n hn p q h a m i :=
  LineEndpointTransport.iso (componentι K n i ≫ p).left (ProjectiveLine.zero K)
    (nodeι K n i ≫ q).left
    (congrArg Over.Hom.left (PolygonNodeIncidence.zero_node K n hn p q h i))
    (PolygonDirectPowerComparison.lineIso K n hn p q h a i m)

/-- Identify the next component infinity line with the same node line. -/
def infinityIso (i : Fin n) :
    (Scheme.Modules.pullback (ProjectiveLine.infinity K)).obj (line K (a (next hn i)) m) ≅
      nodeLine K n hn p q h a m i :=
  LineEndpointTransport.iso (componentι K n (next hn i) ≫ p).left (ProjectiveLine.infinity K)
    (nodeι K n i ≫ q).left
    (congrArg Over.Hom.left (PolygonNodeIncidence.infinity_node K n hn p q h i))
    (PolygonDirectPowerComparison.lineIso K n hn p q h a (next hn i) m)

/-- The actual zero value of a component H0 class, transported to its node. -/
def zeroValue (i : Fin n) (x : H0 K (a i) m) : Γ(nodeLine K n hn p q h a m i, ⊤) :=
  (zeroIso K n hn p q h a m i).hom.app ⊤
    (pullGlobal (ProjectiveLine.zero K) _
      (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K (a i) m) x))

/-- The adjacent infinity value, transported to the same node. -/
def infinityValue (i : Fin n) (x : H0 K (a (next hn i)) m) :
    Γ(nodeLine K n hn p q h a m i, ⊤) :=
  (infinityIso K n hn p q h a m i).hom.app ⊤
    (pullGlobal (ProjectiveLine.infinity K) _
      (moduleScalarH0Equiv (ProjectiveLine.toBase K) (line K (a (next hn i)) m) x))

/-- The zero value has normalized scalar p(0)/(-a)^m. -/
lemma zero_value (i : Fin n) (x : H0 K (a i) m) :
    zeroValue K n hn p q h a m i x =
      (Scheme.ΓSpecIso (.of K)).inv
        ((polynomialEquiv K (a i) m x).val.eval 0 / (-(a i : K)) ^ m) •
        canonical K n hn p q h a m i :=
  LineEndpointTransport.value _ _ _ _ _ _ _
    (PolygonDirectPowerComparison.lineIso_section K n hn p q h a i m) _ _
    (zero_h0 K (a i) m x)

/-- The infinity value has scalar equal to the degree-m coefficient. -/
lemma infinity_value (i : Fin n) (x : H0 K (a (next hn i)) m) :
    infinityValue K n hn p q h a m i x =
      (Scheme.ΓSpecIso (.of K)).inv
        ((polynomialEquiv K (a (next hn i)) m x).val.coeff m) •
        canonical K n hn p q h a m i :=
  LineEndpointTransport.value _ _ _ _ _ _ _
    (PolygonDirectPowerComparison.lineIso_section K n hn p q h a (next hn i) m) _ _
    (infinity_h0 K (a (next hn i)) m x)

/-- The zero endpoint comparison preserves the canonical section. -/
lemma zero_canonical (i : Fin n) :
    (zeroIso K n hn p q h a m i).hom.app ⊤
      (pullGlobal (ProjectiveLine.zero K) (line K (a i) m)
        (divisorSection ((relativeCartier K (a i)).1.pow m) ⊤)) =
      canonical K n hn p q h a m i :=
  LineEndpointTransport.canonical _ _ _ _ _ _ _
    (PolygonDirectPowerComparison.lineIso_section K n hn p q h a i m)

/-- The actual canonical node section cancels scalars. -/
lemma canonical_injective (i : Fin n) :
    Function.Injective (fun r : Γ(Spec (.of K), ⊤) ↦ r • canonical K n hn p q h a m i) := by
  intro r t he
  apply zeroCanonical_injective K (a i) m
  apply (ConcreteCategory.bijective_of_isIso ((zeroIso K n hn p q h a m i).hom.app ⊤)).1
  simpa only [Hom.app_smul, zero_canonical] using he

/-- Equality in the common node line is equality of the normalized polynomial values. -/
lemma matching_iff (i : Fin n) (x : H0 K (a i) m) (y : H0 K (a (next hn i)) m) :
    zeroValue K n hn p q h a m i x = infinityValue K n hn p q h a m i y ↔
      (polynomialEquiv K (a i) m x).val.eval 0 / (-(a i : K)) ^ m =
        (polynomialEquiv K (a (next hn i)) m y).val.coeff m := by
  rw [zero_value, infinity_value, (canonical_injective K n hn p q h a m i).eq_iff]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).1.eq_iff
end FLT.Mazur.PolygonPowerNodeEndpoints
