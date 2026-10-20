/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterTower
public import FLT.Mazur.OneGonAdicChartProjection

/-!
# Compatible affine maps extracted from the constructed character tower

The actual homomorphisms factor through their original Y charts. Composing
with the coefficient projections gives compatible morphisms into one fixed
affine scheme over the whole base, retaining the full initial map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The constructed homomorphism expressed in its original finite Y chart. -/
def towerChart (m : ℕ) : Spec (.of (AddMonoidAlgebra (StageRing I m) G)) ⟶
    chartScheme (equation (parameter I t m)) 1 :=
  (tower I t ht g m).hom.hom.hom.left ≫ (stageChartIso I t ht m).inv

/-- Returning from the chart recovers the whole original group-scheme map. -/
@[reassoc] theorem towerChart_smooth (m : ℕ) :
    towerChart I t ht g m ≫ (stageChartIso I t ht m).hom =
      (tower I t ht g m).hom.hom.hom.left := by
  rw [towerChart, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Adjacent chart maps retain the full prescribed coordinate reduction. -/
theorem towerChart_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
      towerChart I t ht g (m + 1) = towerChart I t ht g m ≫ chartRestriction I t m := by
  apply (cancel_mono (stageChartIso I t ht (m + 1)).hom).mp
  rw [Category.assoc, towerChart_smooth, Category.assoc, chartRestriction_smooth,
    ← Category.assoc, towerChart_smooth, tower_reduction]

/-- Every finite group map gives a map to the same original whole-base affine chart. -/
def towerAffine (m : ℕ) : Spec (.of (AddMonoidAlgebra (StageRing I m) G)) ⟶
    chartScheme (equation t) 1 := towerChart I t ht g m ≫ chartProjection I t m

/-- These maps to the fixed original affine chart are compatible under the actual reductions. -/
theorem towerAffine_reduction (m : ℕ) :
    Spec.map (CommRingCat.ofHom (characterRestriction I G m)) ≫
      towerAffine I t ht g (m + 1) = towerAffine I t ht g m := by
  rw [towerAffine, ← Category.assoc, towerChart_reduction, Category.assoc,
    chartRestriction_projection]
  rfl

/-- The affine tower retains the original initial character homomorphism in its original chart. -/
theorem towerAffine_zero :
    towerAffine I t ht g 0 =
      g.hom.hom.hom.left ≫ (stageChartIso I t ht 0).inv ≫ chartProjection I t 0 := by
  rw [towerAffine, towerChart, tower_zero, Category.assoc]

end FLT.Mazur.OneGonAdicCharacterTower
