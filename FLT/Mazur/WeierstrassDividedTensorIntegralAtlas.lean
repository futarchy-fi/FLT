/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
public import FLT.Mazur.WeierstrassDividedGlobalSmoothAtlas

/-!
# The complete tensor atlas projects to the same integral atlas

Every coefficient chart, including infinity, initial and terminal charts,
projects to its exact original integral index. The full smooth inverse
images consequently map to the unchanged smooth atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "projection" => pullback.snd q base
local notation "chart" => globalTensorAtlasMap hπ data S j hj
local notation "atlas" => globalIntegralAtlasMap hπ data j hj
local notation "E₀" => initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)

/-- The tensor atlas uses the identical index and the original integral chart projection. -/
def tensorIntegralAtlasProjection (a : Fin (j + 3)) :
    globalTensorAtlasObject hπ data S j hj a ⟶ globalIntegralAtlasObject data j hj a :=
  Fin.cases TensorOpenChart.projection
    (fun i => pullback.fst (finiteAtlasMap hπ data E₀ j hj i)
      (pullback.snd q (finiteStructure hπ data j hj))) a

/-- Every indexed projection commutes with the actual whole global model. -/
@[reassoc] theorem tensorIntegralAtlasProjection_global (a : Fin (j + 3)) :
    tensorIntegralAtlasProjection hπ data S j hj a ≫ atlas a = chart a ≫ projection := by
  cases a using Fin.cases with
  | zero => exact (finiteInfinityTensorChart_isPullback hπ data S j hj).w.symm
  | succ i =>
    change pullback.fst _ _ ≫ finiteAtlasMap hπ data E₀ j hj i ≫
      finiteLocalChart hπ data j hj =
        (finiteTensorAtlasMap hπ data S j hj i ≫
          finiteLocalTensorEmbedding hπ data S j hj) ≫ projection
    rw [Category.assoc, finiteLocalTensorEmbedding_square]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ finiteLocalChart hπ data j hj)
      (finiteTensorAtlasMap_isPullback hπ data S j hj i).w.symm

/-- The projected integral chart retains the coefficient point of the original tensor chart. -/
@[reassoc] theorem tensorIntegralAtlasProjection_structure (a : Fin (j + 3)) :
    tensorIntegralAtlasProjection hπ data S j hj a ≫ atlas a ≫ base =
      chart a ≫ pullback.fst q base ≫ q := by
  rw [← Category.assoc, tensorIntegralAtlasProjection_global, Category.assoc,
    pullback.condition]

variable [IsNoetherianRing R] (a : Fin (j + 3))
local notation "coords" => tensorIntegralAtlasProjection hπ data S j hj a
local notation "V" => globalSmoothAtlasOpen hπ data j hj a

/-- The full smooth preimage in the original tensor chart, without removing boundary inputs. -/
def tensorIntegralAtlasSmoothOpen : (globalTensorAtlasObject hπ data S j hj a).Opens :=
  coords ⁻¹ᵁ V

local notation "O" => tensorIntegralAtlasSmoothOpen hπ data S j hj a

/-- This is exactly the tensor chart's full preimage of the original global smooth locus. -/
theorem tensorIntegralAtlasSmoothOpen_eq :
    O = (chart a ≫ projection) ⁻¹ᵁ (base).smoothLocus := by
  change coords ⁻¹ᵁ (atlas a ⁻¹ᵁ (base).smoothLocus) = _
  rw [← Scheme.Hom.comp_preimage, tensorIntegralAtlasProjection_global]

/-- Every full smooth tensor chart maps to the unchanged smooth integral atlas chart. -/
def tensorSmoothIntegralAtlasProjection : (O).toScheme ⟶ (V).toScheme := coords ∣_ V

/-- Both smooth and integral representations retain exactly the same global input. -/
@[reassoc] theorem tensorSmoothIntegralAtlasProjection_global :
    tensorSmoothIntegralAtlasProjection hπ data S j hj a ≫
      globalSmoothAtlasMap hπ data j hj a ≫ (base).smoothLocus.ι =
        (O).ι ≫ chart a ≫ projection := by
  rw [globalSmoothAtlasMap_inclusion, tensorSmoothIntegralAtlasProjection,
    morphismRestrict_ι_assoc, tensorIntegralAtlasProjection_global]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
