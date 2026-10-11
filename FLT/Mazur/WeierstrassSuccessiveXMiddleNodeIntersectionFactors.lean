/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodeIntersectionAlgebra
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterBranchCharts

/-!
# Scheme factorizations on the intersection of the full middle nodes

Each affine test scheme in the actual intersection factors through both full
conic branches. These are equalities of scheme maps, including nilpotents.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (c : K)

/-- The original parameter section gives a projection from the entire node. -/
def middleNodeConicProjection :
    Spec (.of (MiddleNodeOpen c)) ⟶ Spec (.of (ConicParameterOpen c)) :=
  Spec.map (CommRingCat.ofHom (conicParameterToMiddleNode c).toRingHom)

/-- A vanishing horizontal function makes the conic projection a true factorization. -/
@[reassoc] theorem middleNodeConicProjection_factor {S : Type u} [CommRing S]
    (f : Spec (.of S) ⟶ Spec (.of (MiddleNodeOpen c)))
    (hu : (Spec.preimage f).hom (middleNodeU c) = 0) :
    f ≫ middleNodeConicProjection c ≫ middleParameterConicBranch c = f := by
  have H := congrArg (fun r : MiddleNodeOpen c →+* S => Spec.map (CommRingCat.ofHom r))
    (middleNode_conicFactor_ringHom c (Spec.preimage f).hom hu)
  change Spec.map ((CommRingCat.ofHom (middleLocalizedConicRestriction c).toRingHom ≫
    CommRingCat.ofHom (conicParameterToMiddleNode c).toRingHom) ≫ Spec.preimage f) =
      Spec.map (Spec.preimage f) at H
  simpa only [Spec.map_comp, Spec.map_preimage, middleNodeConicProjection,
    middleParameterConicBranch] using H

variable (W : WeierstrassCurve K) (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "N" => Spec (CommRingCat.of (MiddleNodeOpen c))
local notation "J₁" => PrincipalOpenTransport.chart
  (coord W 0 0 0 0 c 1 + algebraMap K A W.a₁) (middleFirstNodeEquiv W c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W 0 0 0 0 c 1)
  (middleSecondNodeEquiv W c h2 ha)

/-- Both affine test maps on the actual node intersection factor through the conic. -/
theorem middleNodeIntersection_affine_factors {S : Type u} [CommRing S]
    (f g : Spec (.of S) ⟶ N) (h : f ≫ J₁ = g ≫ J₂) :
    f ≫ middleNodeConicProjection c ≫ middleParameterConicBranch c = f ∧
      g ≫ middleNodeConicProjection c ≫ middleParameterConicBranch c = g := by
  have h' := h
  rw [middleFirstNodeChart_eq_spec, middleSecondNodeChart_eq_spec,
    ← Spec.map_preimage f, ← Spec.map_preimage g, ← Spec.map_comp, ← Spec.map_comp] at h'
  have hh := congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  obtain ⟨hf, hg⟩ := middleNode_intersection_horizontal_zero W c h2 ha
    (Spec.preimage f).hom (Spec.preimage g).hom hh
  exact ⟨middleNodeConicProjection_factor c f hf, middleNodeConicProjection_factor c g hg⟩

/-- The factorization holds on arbitrary common schemes by checking an affine cover. -/
theorem middleNodeIntersection_factors {V : Scheme.{u}}
    (f g : V ⟶ N) (h : f ≫ J₁ = g ≫ J₂) :
    f ≫ middleNodeConicProjection c ≫ middleParameterConicBranch c = f ∧
      g ≫ middleNodeConicProjection c ≫ middleParameterConicBranch c = g := by
  have H (i : V.affineCover.I₀) := middleNodeIntersection_affine_factors c W h2 ha
    (V.affineCover.f i ≫ f) (V.affineCover.f i ≫ g)
    (by simpa only [Category.assoc] using congrArg (fun q => V.affineCover.f i ≫ q) h)
  constructor
  · apply V.affineCover.hom_ext
    intro i
    simpa only [Category.assoc] using (H i).1
  · apply V.affineCover.hom_ext
    intro i
    simpa only [Category.assoc] using (H i).2

end FLT.Mazur.WeierstrassSuccessiveX
