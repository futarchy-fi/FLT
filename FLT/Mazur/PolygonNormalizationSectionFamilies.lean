/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverCoproductModuleSections
public import FLT.Mazur.SealedLineRestrictionSections
public import FLT.Mazur.PolygonPowerBranchValues
/-!
# Arbitrary normalization section families

Every family of component H0 classes comes from a unique normalization section.
Node restrictions jointly detect equality in the actual node pullback line.
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
omit [NeZero n] in
/-- Component restriction is bijective for arbitrary pulled-back module coefficients. -/
lemma componentRestriction_bijective (L : C.left.Modules) :
    Function.Bijective (fun s : Γ((Scheme.Modules.pullback p.left).obj L, ⊤) ↦
      fun i ↦ (sealedAlong (componentι K n i).left p.left (componentι K n i ≫ p).left
        rfl L).app ⊤ s) :=
  sealedAlong_disjointCover_bijective (overSigmaCover (fun _ : Fin n ↦ component K))
    (overSigmaCover_disjoint _) p.left (fun i ↦ (componentι K n i ≫ p).left) (fun _ ↦ rfl) L
omit [NeZero n] in
/-- The individual node restrictions jointly detect equality. -/
lemma nodeRestriction_injective (L : C.left.Modules) :
    Function.Injective (fun s : Γ((Scheme.Modules.pullback q.left).obj L, ⊤) ↦
      fun i ↦ (sealedAlong (nodeι K n i).left q.left (nodeι K n i ≫ q).left rfl L).app ⊤ s) :=
  sealedAlong_cover_injective (overSigmaCover (fun _ : Fin n ↦ point K))
    q.left (fun i ↦ (nodeι K n i ≫ q).left) (fun _ ↦ rfl) L
/-- All component H0 families are obtained, with a unique normalization section. -/
lemma componentClass_bijective (a : Fin n → Kˣ) (m : ℕ) :
    Function.Bijective (componentClass K n hn p q h a m) := by
  have he := Function.Bijective.piMap (fun i ↦
    (moduleScalarH0Equiv (ProjectiveLine.toBase K)
      (ProjectiveLineMarkedSectionTransition.line K (a i) m)).symm.bijective.comp
      (ConcreteCategory.bijective_of_isIso
        ((PolygonDirectPowerComparison.lineIso K n hn p q h a i m).hom.app ⊤)))
  exact he.comp (componentRestriction_bijective K n p (polygonLine K n hn p q h a m))
end FLT.Mazur.PolygonPowerBranchValues
