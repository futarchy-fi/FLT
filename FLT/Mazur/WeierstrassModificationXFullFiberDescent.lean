/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullFiberDescentCompatibility
public import FLT.Mazur.WeierstrassModificationXFullFiberHomExt
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt
public import FLT.Mazur.WeierstrassModificationXIncidenceBranchCover

/-!
# Descent on the complete initial incidence-conic fiber

The full exterior and conic maps glue through the two original node pushouts
at every divided constant. Both entire component restrictions are recovered.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
attribute [local irreducible] fullNodeParameterDesc
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "J₁" => fullFirstNodeChart a c ha
local notation "J₂" => fullSecondNodeChart a c ha
local notation "s₁" => fullNodeNormalizedDenominator a c
local notation "s₂" => fullNodeNormalizedDenominator (-a) c
local notation "hs₁" => fullNodeNormalizedDenominator_value a c ha
local notation "hs₂" => fullNodeNormalizedDenominator_value (-a) c ha.neg
local notation "b₁" => NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₁)
local notation "b₂" => NodeLocalDescent.branchOpen K (PolygonNodeEqualizer.second s₂)
local notation "t" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (aeval (X - C a : K[X]))))
local notation "p₁" => (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c
local notation "p₂" => (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c
local notation "o" => Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)
variable {Y : Scheme.{u}} (f : Spec (.of (ConicCoordinate a c)) ⟶ Y)
  (g : ProjectiveLine.chart K ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
    (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫ f =
      NodeLocalDescent.secondOrigin K (fullNodeNormalizedDenominator a c)
        (fullNodeNormalizedDenominator_value a c ha) ≫
          NodeLocalDescent.branchOpen K
            (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator a c)) ≫ g)
  (w₂ : Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
    (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫ f =
      NodeLocalDescent.secondOrigin K (fullNodeNormalizedDenominator (-a) c)
        (fullNodeNormalizedDenominator_value (-a) c ha.neg) ≫
          NodeLocalDescent.branchOpen K
            (PolygonNodeEqualizer.second (fullNodeNormalizedDenominator (-a) c)) ≫
              Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (aeval (X - C a : K[X])))) ≫ g)
local notation "d₁" => fullNodeParameterDesc a c ha (p₁ ≫ f) (b₁ ≫ g)
  (by simpa only [Category.assoc] using w₁)
local notation "d₂" => fullNodeParameterDesc (-a) c ha.neg (p₂ ≫ f) (b₂ ≫ t ≫ g)
  (by simpa only [Category.assoc] using w₂)

/-- The two constructed local descents agree on the whole original tangent intersection. -/
theorem fullFiberDesc_compatible :
    pullback.fst J₁ J₂ ≫ d₁ = pullback.snd J₁ J₂ ≫ d₂ := by
  apply fullFiberNodeMaps_compatible a c ha d₁ d₂ g f
  · exact fullNodeParameterDesc_exterior ..
  · exact fullNodeParameterDesc_exterior ..
  · simpa only [Category.assoc] using fullNodeParameterDesc_conic
      a c ha (p₁ ≫ f) (b₁ ≫ g) (by simpa only [Category.assoc] using w₁)
  · simpa only [Category.assoc] using fullNodeParameterDesc_conic
      (-a) c ha.neg (p₂ ≫ f) (b₂ ≫ t ≫ g)
        (by simpa only [Category.assoc] using w₂)

/-- The full incidence-conic equation carries the glued actual node descents. -/
@[irreducible] def fullFiberDesc : Spec (.of (FiberCoordinate a c)) ⟶ Y := by
  refine BinaryOpenDescent.desc (pullback.fst J₁ J₂) (pullback.snd J₁ J₂) J₁ J₂
    (IsPullback.of_hasPullback J₁ J₂) (fullNodeCharts_cover a c ha) d₁ d₂
    ?_
  exact fullFiberDesc_compatible a c ha f g w₁ w₂

/-- The first entire original node map is retained by the gluing. -/
@[reassoc] theorem fullFiberDesc_firstChart :
    J₁ ≫ fullFiberDesc a c ha f g w₁ w₂ = d₁ := by
  rw [fullFiberDesc]
  exact BinaryOpenDescent.inl_desc ..

/-- The opposite entire original node map is retained with its translated incidence parameter. -/
@[reassoc] theorem fullFiberDesc_secondChart :
    J₂ ≫ fullFiberDesc a c ha f g w₁ w₂ = d₂ := by
  rw [fullFiberDesc]
  exact BinaryOpenDescent.inr_desc ..

/-- Both full conic parameter opens recover the given complete conic map. -/
@[reassoc] theorem fullFiberDesc_conic :
    fiberConicImmersion a c ≫ fullFiberDesc a c ha f g w₁ w₂ = f := by
  apply conicParameter_hom_ext a c ha
  · simp only [Category.assoc]
    rw [← fullNodeFirstBranch_firstChart_assoc, fullFiberDesc_firstChart,
      fullNodeParameterDesc_conic]
    simp only [Category.assoc]
  · simp only [Category.assoc]
    rw [← fullNodeFirstBranch_secondChart_assoc, fullFiberDesc_secondChart,
      fullNodeParameterDesc_conic]
    simp only [Category.assoc]

/-- The two original localized incidence branches recover the entire given exterior map. -/
@[reassoc] theorem fullFiberDesc_incidence :
    fiberIncidenceImmersion a c ≫ fullFiberDesc a c ha f g w₁ w₂ = g := by
  apply fullNodeIncidenceBranches_hom_ext a c ha
  · rw [← fullNodeSecondBranch_firstChart_assoc a c ha, fullFiberDesc_firstChart,
      fullNodeParameterDesc_exterior]
  · rw [← fullNodeSecondBranch_secondChart_assoc a c ha, fullFiberDesc_secondChart,
      fullNodeParameterDesc_exterior]

include ha w₁ w₂ in
/-- The full original incidence and conic maps have a unique compatible descent. -/
theorem fullFiber_exists_unique_desc :
    ∃! d : Spec (.of (FiberCoordinate a c)) ⟶ Y,
      fiberConicImmersion a c ≫ d = f ∧ fiberIncidenceImmersion a c ≫ d = g := by
  refine ⟨fullFiberDesc a c ha f g w₁ w₂,
    ⟨fullFiberDesc_conic a c ha f g w₁ w₂,
      fullFiberDesc_incidence a c ha f g w₁ w₂⟩, ?_⟩
  intro d hd
  apply fullFiber_components_hom_ext a c ha
  · rw [hd.2, fullFiberDesc_incidence]
  · rw [hd.1, fullFiberDesc_conic]

end FLT.Mazur.WeierstrassModificationX
