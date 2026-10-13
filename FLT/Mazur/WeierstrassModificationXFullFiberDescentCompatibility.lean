/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeOverlapCompatibility
public import FLT.Mazur.WeierstrassModificationXFullNodeParameterDescent

/-!
# Initial full-fiber node descent and overlap compatibility at every constant

Construct each actual node descent from the full conic parameter and localized
exterior. The two descents agree on their scheme intersection even at constant zero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "s" => fullNodeNormalizedDenominator a c
local notation "hs" => fullNodeNormalizedDenominator_value a c ha
local notation "E" => fullNodeConicParameterIso a c ha
local notation "o" => Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)
variable {Y : Scheme.{u}}
  (f : Spec (.of (ConicParameterOpen c)) ⟶ Y)
  (g : Spec (.of (Localization.Away
    (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)))) ⟶ Y)
  (w : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫ f =
    NodeLocalDescent.secondOrigin K (fullNodeNormalizedDenominator a c)
      (fullNodeNormalizedDenominator_value a c ha) ≫ g)

/-- The actual full node map supplied by the proved affine pinching universal property. -/
def fullNodeParameterDesc : Spec (.of (FullNodeOpen a c)) ⟶ Y :=
  (fullNodeConicParameter_exists_unique_desc a c ha f g w).choose

/-- The node descent retains its full original rational conic parameter. -/
@[reassoc] theorem fullNodeParameterDesc_conic :
    (E).hom ≫ fullNodeFirstBranch a c ha ≫ fullNodeParameterDesc a c ha f g w = f :=
  (fullNodeConicParameter_exists_unique_desc a c ha f g w).choose_spec.1.1

/-- The node descent retains the whole original localized incidence branch. -/
@[reassoc] theorem fullNodeParameterDesc_exterior :
    fullNodeSecondBranch a c ha ≫ fullNodeParameterDesc a c ha f g w = g :=
  (fullNodeConicParameter_exists_unique_desc a c ha f g w).choose_spec.1.2

local notation "s₁" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)
local notation "s₂" => PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)
local notation "t" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (aeval (X - C a : K[X]))))

/-- Full exterior and conic restrictions imply node compatibility for every divided constant. -/
theorem fullFiberNodeMaps_compatible
    (d₁ : Spec (.of (FullNodeOpen a c)) ⟶ Y)
    (d₂ : Spec (.of (FullNodeOpen (-a) c)) ⟶ Y)
    (E₀ : ProjectiveLine.chart K ⟶ Y) (C₀ : Spec (.of (ConicCoordinate a c)) ⟶ Y)
    (he₁ : fullNodeSecondBranch a c ha ≫ d₁ = NodeLocalDescent.branchOpen K s₁ ≫ E₀)
    (he₂ : fullNodeSecondBranch (-a) c ha.neg ≫ d₂ =
      NodeLocalDescent.branchOpen K s₂ ≫ t ≫ E₀)
    (hc₁ : (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫ d₁ =
      (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ C₀)
    (hc₂ : (fullNodeConicParameterIso (-a) c ha.neg).hom ≫
      fullNodeFirstBranch (-a) c ha.neg ≫ d₂ =
        (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫ C₀) :
    pullback.fst (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₁ =
      pullback.snd (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₂ := by
  by_cases hc : c = 0
  · exact fullZeroNodeMaps_compatible a c ha hc d₁ d₂ E₀ he₁ he₂
  · exact fullNodeMaps_compatible_of_component_restrictions
      a c ha (isUnit_iff_ne_zero.mpr hc) d₁ d₂ E₀ C₀ he₁ he₂ hc₁ hc₂

end FLT.Mazur.WeierstrassModificationX
