/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonLineNodeRestriction
public import FLT.Mazur.PolygonPowerNodeWeights
/-!
# Normalization branch values in polynomial coordinates

Restrict actual normalization sections to components, identify their H0 classes,
and compare the two original branch values in the common polygon node line.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonPowerBranchValues
open FCurve PolygonPinching ProjectiveLineMarkedHZero
open PolygonPowerNodeEndpoints LinePullbackRestriction
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (m : ℕ)

/-- The actual pullback of the divisor power to the normalization. -/
abbrev normalizationLine :=
  (Scheme.Modules.pullback p.left).obj (polygonLine K n hn p q h a m)

/-- The H0 class of a restricted normalization section on one component. -/
def componentClass (s : Γ(normalizationLine K n hn p q h a m, ⊤)) (i : Fin n) :
    H0 K (a i) m :=
  (moduleScalarH0Equiv (ProjectiveLine.toBase K)
    (ProjectiveLineMarkedSectionTransition.line K (a i) m)).symm
    ((PolygonDirectPowerComparison.lineIso K n hn p q h a i m).hom.app ⊤
      ((sealedAlong (componentι K n i).left p.left (componentι K n i ≫ p).left rfl
        (polygonLine K n hn p q h a m)).app ⊤ s))

/-- The value of an original normalization branch at a specified node. -/
def nodeValue (b : Bool) (i : Fin n)
    (s : Γ(normalizationLine K n hn p q h a m, ⊤)) :
    Γ(nodeLine K n hn p q h a m i, ⊤) :=
  (sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl
    (polygonLine K n hn p q h a m)).app ⊤
    ((PolygonLineNormalization.branch K n hn p q h _
      ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m).divisorLineBundle_locallyFreeRankOne
      b).app ⊤ s)

/-- The original zero branch has the transported component endpoint value. -/
lemma zero_nodeValue (i : Fin n) (s : Γ(normalizationLine K n hn p q h a m, ⊤)) :
    nodeValue K n hn p q h a m false i s =
      zeroValue K n hn p q h a m i (componentClass K n hn p q h a m s i) := by
  have he := congrArg (fun f ↦ f.app ⊤ s)
    (PolygonLineNodeRestriction.zero_branch K n hn p q h (polygonLine K n hn p q h a m)
      ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m).divisorLineBundle_locallyFreeRankOne
      i)
  change nodeValue K n hn p q h a m false i s = _ at he
  rw [Hom.comp_app, ConcreteCategory.comp_apply, sealedAlong_eq_transport
    _ _ _ _ (PolygonDirectPowerComparison.lineIso K n hn p q h a i m)] at he
  simpa only [zeroValue, zeroIso, ProjectiveLineMarkedSectionTransition.line,
    componentClass, LinearEquiv.apply_symm_apply] using he

/-- The original infinity branch has the adjacent component endpoint value. -/
lemma infinity_nodeValue (i : Fin n) (s : Γ(normalizationLine K n hn p q h a m, ⊤)) :
    nodeValue K n hn p q h a m true i s =
      infinityValue K n hn p q h a m i
        (componentClass K n hn p q h a m s (next hn i)) := by
  have he := congrArg (fun f ↦ f.app ⊤ s)
    (PolygonLineNodeRestriction.infinity_branch K n hn p q h (polygonLine K n hn p q h a m)
      ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m).divisorLineBundle_locallyFreeRankOne
      i)
  change nodeValue K n hn p q h a m true i s = _ at he
  rw [Hom.comp_app, ConcreteCategory.comp_apply, sealedAlong_eq_transport
    _ _ _ _ (PolygonDirectPowerComparison.lineIso K n hn p q h a (next hn i) m)] at he
  simpa only [infinityValue, infinityIso, ProjectiveLineMarkedSectionTransition.line,
    componentClass, LinearEquiv.apply_symm_apply] using he
/-- Matching of original branch values is exactly the existing polynomial predicate. -/
lemma polynomial_matching_iff (d : ℕ)
    (s : Γ(normalizationLine K n hn p q h a (d + 1), ⊤)) :
    (∀ i, nodeValue K n hn p q h a (d + 1) false i s =
      nodeValue K n hn p q h a (d + 1) true i s) ↔
    (fun i ↦ polynomialEquiv K (a i) (d + 1)
      (componentClass K n hn p q h a (d + 1) s i)) ∈
      PolygonPolynomialMatching.matching (fun _ : Fin n ↦ d) (finRotate n).symm
        (weight K n a (d + 1)) := by
  simp only [zero_nodeValue, infinity_nodeValue]
  exact PolygonPowerNodeEndpoints.polynomial_matching_iff K n hn p q h a d _
end FLT.Mazur.PolygonPowerBranchValues
