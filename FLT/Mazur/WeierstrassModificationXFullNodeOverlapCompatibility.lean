/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOverlapBranches

/-!
# Full node compatibility from the original exterior and conic restrictions

Shared maps on both complete components imply equality on the actual
categorical tangent intersection for every target scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a) (hc : IsUnit c)
local notation "s₁" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)
local notation "s₂" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)
local notation "t" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (aeval (X - C a : K[X]))))

include hc in
/-- Both complete original branch restrictions suffice for full tangent-overlap compatibility. -/
theorem fullNodeMaps_compatible_of_component_restrictions {Y : Scheme.{u}}
    (d₁ : Spec (.of (FullNodeOpen a c)) ⟶ Y)
    (d₂ : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y)
    (E : ProjectiveLine.chart K ⟶ Y) (C : Spec (.of (ConicCoordinate a c)) ⟶ Y)
    (he₁ : fullNodeSecondBranch a c ha ≫ d₁ = NodeLocalDescent.branchOpen K s₁ ≫ E)
    (he₂ : fullNodeSecondBranch (-a) c ha.neg ≫ d₂ =
      NodeLocalDescent.branchOpen K s₂ ≫ t ≫ E)
    (hc₁ : (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫ d₁ =
      (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ C)
    (hc₂ : (fullNodeConicParameterIso (-a) c ha.neg).hom ≫
      fullNodeFirstBranch (-a) c ha.neg ≫ d₂ =
        (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫ C) :
    pullback.fst (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₁ =
      pullback.snd (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₂ := by
  apply fullNodeOverlap_hom_ext a c ha hc
  · rw [fullNodeOverlapExterior_first_assoc, fullNodeOverlapExterior_second_assoc,
      he₁, he₂, fullNodeSlopeFirstBranch_open_assoc, fullNodeSlopeSecondBranch_open_assoc]
  · apply (cancel_epi (fiberConicOpenIso a c).hom).mp
    simp only [← Category.assoc]
    rw [fullNodeOverlapConic_first, fullNodeOverlapConic_second]
    simp only [Category.assoc]
    rw [hc₁, hc₂, conicIncidenceFirstParameterMap_conic_assoc,
      conicIncidenceSecondParameterMap_conic_assoc]

end FLT.Mazur.WeierstrassModificationX
