/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeReciprocalScaling

/-!
# Scaled formal-node maps into the original polygon

The actual original completion and every full finite neighborhood carry scheme
automorphisms. Their maps into the original polygon commute with all finite
evaluations. They are formal test maps, not lifts on original-input open charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local instance] completeNodeScaleAffineAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)
local notation "I" => completeNodeAffineIdeal K n h i U hx

/-- The spectrum of the actual original completed node ring. -/
abbrev completeNodeFormalSpectrum : Scheme :=
  Spec (.of (AdicCompletion (I) Γ(exactVeroneseProj K n h, U)))

/-- The actual full original node thickening at each positive order. -/
abbrev completeNodeNeighborhoodSpectrum (m : ℕ) : Scheme :=
  Spec (.of (Γ(exactVeroneseProj K n h, U) ⧸ (I) ^ (m + 1)))

/-- The actual completion automorphism, viewed as an isomorphism of schemes. -/
def completeNodeFormalScalingIso (a : (PowerSeries K)ˣ) :
    completeNodeFormalSpectrum K n h i U hx ≅ completeNodeFormalSpectrum K n h i U hx :=
  Scheme.Spec.mapIso (completeNodeFormalScale K n h i U hx a).toRingEquiv.toCommRingCatIso.op

/-- The full finite neighborhood automorphism as an isomorphism of schemes. -/
def completeNodeNeighborhoodScalingIso (a : (PowerSeries K)ˣ) (m : ℕ) :
    completeNodeNeighborhoodSpectrum K n h i U hx m ≅
      completeNodeNeighborhoodSpectrum K n h i U hx m :=
  Scheme.Spec.mapIso
    (completeNodeNeighborhoodScale K n h i U hx a m).toRingEquiv.toCommRingCatIso.op

/-- The original finite evaluation map, without reducing the target or source. -/
def completeNodeFormalEvaluation (m : ℕ) :
    completeNodeNeighborhoodSpectrum K n h i U hx m ⟶ completeNodeFormalSpectrum K n h i U hx :=
  Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ (I) (m + 1)).toRingHom)

/-- Finite evaluation intertwines the actual spectrum automorphisms. -/
@[reassoc] theorem completeNodeFormalEvaluation_scaling (a : (PowerSeries K)ˣ) (m : ℕ) :
    completeNodeFormalEvaluation K n h i U hx m ≫
        (completeNodeFormalScalingIso K n h i U hx a).hom =
      (completeNodeNeighborhoodScalingIso K n h i U hx a m).hom ≫
        completeNodeFormalEvaluation K n h i U hx m := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (completeNodeFormalScale_eval K n h i U hx a m)

/-- The completion maps to the actual original affine open and then to the polygon. -/
def completeNodeFormalToOriginal :
    completeNodeFormalSpectrum K n h i U hx ⟶ exactVeroneseProj K n h :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(exactVeroneseProj K n h, U)
    (AdicCompletion (I) Γ(exactVeroneseProj K n h, U)))) ≫ U.2.fromSpec

/-- Each full original node thickening maps into the original polygon. -/
def completeNodeNeighborhoodToOriginal (m : ℕ) :
    completeNodeNeighborhoodSpectrum K n h i U hx m ⟶ exactVeroneseProj K n h :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I) ^ (m + 1)))) ≫ U.2.fromSpec

/-- The formal map recovers each unchanged original finite-neighborhood map. -/
@[reassoc] theorem completeNodeFormalEvaluation_original (m : ℕ) :
    completeNodeFormalEvaluation K n h i U hx m ≫
        completeNodeFormalToOriginal K n h i U hx =
      completeNodeNeighborhoodToOriginal K n h i U hx m := by
  unfold completeNodeFormalToOriginal completeNodeNeighborhoodToOriginal
    completeNodeFormalEvaluation
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1

/-- An actual polygon-valued map from the scaled original formal node. -/
def completeNodeFormalScaledMap (a : (PowerSeries K)ˣ) :
    completeNodeFormalSpectrum K n h i U hx ⟶ exactVeroneseProj K n h :=
  (completeNodeFormalScalingIso K n h i U hx a).hom ≫
    completeNodeFormalToOriginal K n h i U hx

/-- Every full original finite neighborhood has its corresponding scaled polygon map. -/
def completeNodeNeighborhoodScaledMap (a : (PowerSeries K)ˣ) (m : ℕ) :
    completeNodeNeighborhoodSpectrum K n h i U hx m ⟶ exactVeroneseProj K n h :=
  (completeNodeNeighborhoodScalingIso K n h i U hx a m).hom ≫
    completeNodeNeighborhoodToOriginal K n h i U hx m

/-- The scaled formal polygon map retains every original finite-neighborhood map. -/
@[reassoc] theorem completeNodeFormalScaledMap_eval (a : (PowerSeries K)ˣ) (m : ℕ) :
    completeNodeFormalEvaluation K n h i U hx m ≫
        completeNodeFormalScaledMap K n h i U hx a =
      completeNodeNeighborhoodScaledMap K n h i U hx a m := by
  rw [completeNodeFormalScaledMap, ← Category.assoc, completeNodeFormalEvaluation_scaling,
    Category.assoc, completeNodeFormalEvaluation_original, completeNodeNeighborhoodScaledMap]

/-- The constructed completion automorphism keeps the original power-series coefficients. -/
@[reassoc] theorem completeNodeFormalScalingIso_base (a : (PowerSeries K)ˣ) :
    (completeNodeFormalScalingIso K n h i U hx a).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K)
          (AdicCompletion (I) Γ(exactVeroneseProj K n h, U)))) =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K)
        (AdicCompletion (I) Γ(exactVeroneseProj K n h, U)))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (completeNodeFormalScale K n h i U hx a).toAlgHom.comp_algebraMap

end FLT.Mazur.PolygonInfinitesimalStages
