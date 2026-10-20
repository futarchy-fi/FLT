/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterAffineEffectivity
public import FLT.Mazur.FiniteCharacterAdicMapExt

/-!
# The effective character map retains the original base

The structure equations at every constructed finite stage determine the
structure equation over the original complete ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The nilpotent chart identification retains the actual structure morphism. -/
@[reassoc] theorem stageChartIso_structure (m : ℕ) :
    (stageChartIso I t ht m).hom ≫ integralSmoothStructure (equation (parameter I t m)) =
      chartStructure (equation (parameter I t m)) 1 := by
  rw [integralSmoothStructure, ← Category.assoc, stageChartIso_hom_inclusion,
    integralCurveChart_structure]

/-- The original finite chart map is a morphism over its original coefficient spectrum. -/
@[reassoc] theorem towerChart_structure (m : ℕ) :
    towerChart I t ht g m ≫ chartStructure (equation (parameter I t m)) 1 =
      (model (StageRing I m) G).hom := by
  rw [← stageChartIso_structure I t ht m, ← Category.assoc, towerChart_smooth]
  exact (tower I t ht g m).hom.hom.hom.w

/-- Projection of the original chart retains the quotient map on the full base ring. -/
@[reassoc] theorem chartProjection_structure (m : ℕ) :
    chartProjection I t m ≫ chartStructure (equation t) 1 =
      chartStructure (equation (parameter I t m)) 1 ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (m + 1)))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact chartCoefficientRingMapTo_scalar (Ideal.Quotient.mk (I ^ (m + 1)))
    (equation t) 1 (equation (parameter I t m)) (equation_map t _) a

/-- The finite maps into the fixed original chart retain the original relative structure. -/
@[reassoc] theorem towerAffine_structure (m : ℕ) :
    towerAffine I t ht g m ≫ chartStructure (equation t) 1 =
      Spec.map (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫
        (model R G).hom := by
  rw [towerAffine, Category.assoc, chartProjection_structure, towerChart_structure_assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  simp [FiniteCharacterAdicElements.reduction]

variable [Finite G] [IsAdicComplete I R]

/-- The effective affine map is over the original complete coefficient spectrum. -/
@[reassoc] theorem effectiveAffine_structure :
    effectiveAffine I t ht g ≫ chartStructure (equation t) 1 = (model R G).hom := by
  apply FiniteCharacterAdicElements.specMap_ext I
  intro m
  rw [← Category.assoc, effectiveAffine_reduction, towerAffine_structure]

/-- The effective chart map as an actual morphism over the original base. -/
def effectiveAffineOver : model R G ⟶ Over.mk (chartStructure (equation t) 1) :=
  Over.homMk (effectiveAffine I t ht g) (effectiveAffine_structure I t ht g)

end FLT.Mazur.OneGonAdicCharacterTower
