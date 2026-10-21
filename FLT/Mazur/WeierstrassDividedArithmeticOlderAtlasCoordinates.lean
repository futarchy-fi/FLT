/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts
public import FLT.Mazur.WeierstrassDividedGlobalSmoothAtlas

/-!
# Original arithmetic older charts in the unchanged integral atlas

Project the actual quotient tensor chart to its exact integral atlas index.
Its smooth restriction is the full inverse image of the resolved smooth
locus, including points with zero abscissa.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasMap globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "A" => WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "idx" => (Fin.succ ⟨r + 1, by omega⟩ : Fin (j + 1 + r + 3))
local notation "base" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "old" => finiteArithmeticOlderTensorChart hπ data m j hj r hr
local notation "projection" => pullback.fst base q
local notation "atlas" => globalIntegralAtlasMap hπ data (j + 1 + r) hr idx

/-- The original tensor projection, at the older chart's exact complete-atlas index. -/
def arithmeticOlderAtlasCoordinates :
    Spec (.of A) ⟶ globalIntegralAtlasObject data (j + 1 + r) hr idx :=
  TensorOpenChart.projection ≫ eqToHom (finiteOlderExteriorObject_eq data j hj r hr).symm

local notation "coords" => arithmeticOlderAtlasCoordinates data m j hj r hr

/-- The integral atlas coordinates recover the original arithmetic point in the global model. -/
@[reassoc] theorem arithmeticOlderAtlasCoordinates_global : coords ≫ atlas = old ≫ projection := by
  rw [arithmeticOlderAtlasCoordinates, Category.assoc, globalIntegralAtlasMap_older]
  rw [finiteArithmeticOlderTensorChart, Category.assoc, pullbackSymmetry_hom_comp_fst,
    olderGlobalTensorChart_integralProjection]

/-- The coordinate projection preserves the original quotient coefficient morphism. -/
@[reassoc] theorem arithmeticOlderAtlasCoordinates_structure :
    coords ≫ atlas ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap Q A)) ≫ q := by
  rw [← Category.assoc, arithmeticOlderAtlasCoordinates_global, Category.assoc,
    pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ q)
    (finiteArithmeticOlderTensorChart_structure hπ data m j hj r hr)

variable [IsNoetherianRing R]
local notation "U" => (base).smoothLocus
local notation "V" => globalSmoothAtlasOpen hπ data (j + 1 + r) hr idx

/-- All relatively smooth original arithmetic inputs, with no puncturing condition. -/
def arithmeticOlderAtlasSmoothOpen : (Spec (.of A)).Opens := coords ⁻¹ᵁ V

local notation "O" => arithmeticOlderAtlasSmoothOpen hπ data m j hj r hr

/-- The smooth domain is exactly the original arithmetic preimage of global smoothness. -/
theorem arithmeticOlderAtlasSmoothOpen_eq : O = (old ≫ projection) ⁻¹ᵁ U := by
  change coords ⁻¹ᵁ (atlas ⁻¹ᵁ U) = _
  rw [← Scheme.Hom.comp_preimage, arithmeticOlderAtlasCoordinates_global]

/-- The original tensor coordinates lift to the complete smooth integral atlas chart. -/
def arithmeticOlderSmoothAtlasCoordinates : (O).toScheme ⟶ (V).toScheme := coords ∣_ V

local notation "smooth" => arithmeticOlderSmoothAtlasCoordinates hπ data m j hj r hr

/-- All functions on the integral older chart retain their original tensor pullbacks. -/
@[reassoc] theorem arithmeticOlderSmoothAtlasCoordinates_inclusion :
    smooth ≫ (V).ι = (O).ι ≫ coords := morphismRestrict_ι _ _

/-- The smooth chart represents exactly the original arithmetic resolved input. -/
@[reassoc] theorem arithmeticOlderSmoothAtlasCoordinates_global :
    smooth ≫ globalSmoothAtlasMap hπ data (j + 1 + r) hr idx ≫ (U).ι =
      (O).ι ≫ old ≫ projection := by
  rw [globalSmoothAtlasMap_inclusion, arithmeticOlderSmoothAtlasCoordinates_inclusion_assoc,
    arithmeticOlderAtlasCoordinates_global]

/-- The full smooth tensor chart retains the original arithmetic base point. -/
@[reassoc] theorem arithmeticOlderSmoothAtlasCoordinates_structure :
    smooth ≫ globalSmoothAtlasMap hπ data (j + 1 + r) hr idx ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap Q A)) ≫ q := by
  rw [globalSmoothAtlasMap_inclusion_assoc,
    arithmeticOlderSmoothAtlasCoordinates_inclusion_assoc,
    arithmeticOlderAtlasCoordinates_structure]

end FLT.Mazur.WeierstrassDividedDepth
