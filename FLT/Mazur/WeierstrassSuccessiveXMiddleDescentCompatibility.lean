/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeIntersectionFactors
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterDescent
public import FLT.Mazur.PrincipalOpenTransportGeometry
public import FLT.Mazur.BinaryOpenDescent

/-!
# Compatibility of full middle-node descents on the actual overlap

Both maps factor through the same original conic on their scheme intersection.
Compatibility follows from the common conic restriction for arbitrary targets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "J₁" => PrincipalOpenTransport.chart
  (coord W 0 0 0 0 c 1 + algebraMap K A W.a₁) (middleFirstNodeEquiv W c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W 0 0 0 0 c 1)
  (middleSecondNodeEquiv W c h2 ha)

local notation "p₁" => (conicFirstParameterIso W.a₁ c ha).inv ≫
  conicFirstOpenImmersion W.a₁ c
local notation "p₂" => Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
  (conicSecondParameterIso W.a₁ c ha).inv ≫ conicSecondOpenImmersion W.a₁ c

/-- Common points of the actual node charts induce the same map to the full conic. -/
theorem middleNodeIntersection_conic_agreement {V : Scheme.{u}}
    (q₁ q₂ : V ⟶ Spec (.of (MiddleNodeOpen c))) (h : q₁ ≫ J₁ = q₂ ≫ J₂) :
    q₁ ≫ middleNodeConicProjection c ≫ p₁ =
      q₂ ≫ middleNodeConicProjection c ≫ p₂ := by
  obtain ⟨hf, hg⟩ := middleNodeIntersection_factors c W h2 ha q₁ q₂ h
  apply (cancel_mono (middleConicImmersion W c h2)).mp
  simp only [Category.assoc]
  rw [← middleParameterConicBranch_firstChart,
    ← middleParameterConicBranch_secondChart]
  simpa only [← Category.assoc, hf, hg] using h

/-- Local descents with a common full conic restriction agree on every actual overlap. -/
theorem middleNodeDescents_compatible {Y V : Scheme.{u}}
    (f : Spec (.of (ConicCoordinate W.a₁ c)) ⟶ Y)
    (d₁ d₂ : Spec (.of (MiddleNodeOpen c)) ⟶ Y)
    (h₁ : middleParameterConicBranch c ≫ d₁ = p₁ ≫ f)
    (h₂ : middleParameterConicBranch c ≫ d₂ = p₂ ≫ f)
    (q₁ q₂ : V ⟶ Spec (.of (MiddleNodeOpen c))) (h : q₁ ≫ J₁ = q₂ ≫ J₂) :
    q₁ ≫ d₁ = q₂ ≫ d₂ := by
  obtain ⟨hf, hg⟩ := middleNodeIntersection_factors c W h2 ha q₁ q₂ h
  calc
    q₁ ≫ d₁ = q₁ ≫ middleNodeConicProjection c ≫ p₁ ≫ f := by
      rw [← h₁]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ d₁) hf.symm
    _ = q₂ ≫ middleNodeConicProjection c ≫ p₂ ≫ f := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ f)
        (middleNodeIntersection_conic_agreement W c h2 ha q₁ q₂ h)
    _ = q₂ ≫ d₂ := by
      rw [← h₂]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ d₂) hg

end FLT.Mazur.WeierstrassSuccessiveX
