/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteAtlas
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import FLT.Mazur.WeierstrassDividedOlderGlobalStep
public import FLT.Mazur.WeierstrassDividedOlderAtlasIndex

/-!
# A complete integral atlas of the global resolved smooth locus

Keep infinity, the terminal divided chart, the retained initial chart, and
every older successive X-chart. Restricting this actual finite atlas to the
relative smooth locus still covers the entire smooth scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "E₀" => initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)

/-- The actual integral atlas includes infinity and every finite local chart. -/
def globalIntegralAtlasObject (j : ℕ) (hj : j ≤ n) : Fin (j + 3) → Scheme :=
  Fin.cases (WeierstrassIntegralChart.chartScheme W 1) (finiteAtlasObject data E₀ j hj)

/-- Each whole original chart embeds into the actual global finite model. -/
def globalIntegralAtlasMap (j : ℕ) (hj : j ≤ n) (i : Fin (j + 3)) :
    globalIntegralAtlasObject data j hj i ⟶ finiteGlobalModel hπ data j hj :=
  Fin.cases (finiteInfinityChart hπ data j hj)
    (fun a => finiteAtlasMap hπ data E₀ j hj a ≫ finiteLocalChart hπ data j hj) i

instance globalIntegralAtlasMap_open (j : ℕ) (hj : j ≤ n) (i : Fin (j + 3)) :
    IsOpenImmersion (globalIntegralAtlasMap hπ data j hj i) := by
  cases i using Fin.cases with
  | zero => change IsOpenImmersion (finiteInfinityChart hπ data j hj); infer_instance
  | succ i => change IsOpenImmersion (_ ≫ finiteLocalChart hπ data j hj); infer_instance

/-- The integral chart family covers every point, including all older X-charts. -/
theorem globalIntegralAtlas_cover (j : ℕ) (hj : j ≤ n)
    (z : finiteGlobalModel hπ data j hj) :
    ∃ i x, globalIntegralAtlasMap hπ data j hj i x = z := by
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := finiteGlobal_charts_cover hπ data j hj z
  · exact ⟨0, x, rfl⟩
  · obtain ⟨i, y, rfl⟩ := finiteAtlas_cover hπ data E₀ j hj x
    exact ⟨i.succ, y, rfl⟩

/-- The original integral atlas packaged as an actual open cover. -/
def globalIntegralOpenCover (j : ℕ) (hj : j ≤ n) :
    (finiteGlobalModel hπ data j hj).OpenCover where
  I₀ := Fin (j + 3)
  X := globalIntegralAtlasObject data j hj
  f := globalIntegralAtlasMap hπ data j hj
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨globalIntegralAtlas_cover hπ data j hj, fun i => inferInstance⟩

/-- Every retained older X-chart occurs at its exact integral atlas index. -/
@[reassoc] theorem globalIntegralAtlasMap_older (j : ℕ) (hj : j + 1 ≤ n)
    (r : ℕ) (hr : j + 1 + r ≤ n) :
    eqToHom (finiteOlderExteriorObject_eq data j hj r hr).symm ≫
      globalIntegralAtlasMap hπ data (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩) =
        olderGlobalChart hπ data j hj r hr := by
  change _ ≫ (finiteAtlasMap hπ data E₀ _ _ _ ≫ _) = _
  rw [olderSuccessiveChart_eq_index_assoc]
  rfl

variable [IsNoetherianRing R] (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The entire relatively smooth preimage of each original integral chart. -/
def globalSmoothAtlasOpen (i : Fin (j + 3)) :
    (globalIntegralAtlasObject data j hj i).Opens :=
  globalIntegralAtlasMap hπ data j hj i ⁻¹ᵁ U

/-- The complete smooth restriction of every integral atlas map. -/
def globalSmoothAtlasMap (i : Fin (j + 3)) :
    (globalSmoothAtlasOpen hπ data j hj i).toScheme ⟶ (U).toScheme :=
  globalIntegralAtlasMap hπ data j hj i ∣_ U

instance globalSmoothAtlasMap_open (i : Fin (j + 3)) :
    IsOpenImmersion (globalSmoothAtlasMap hπ data j hj i) := by
  dsimp only [globalSmoothAtlasMap]
  infer_instance

/-- The restricted chart retains the whole original integral inclusion. -/
@[reassoc] theorem globalSmoothAtlasMap_inclusion (i : Fin (j + 3)) :
    globalSmoothAtlasMap hπ data j hj i ≫ (U).ι =
      (globalSmoothAtlasOpen hπ data j hj i).ι ≫ globalIntegralAtlasMap hπ data j hj i :=
  morphismRestrict_ι _ _

/-- Every resolved smooth input lies in one of these full smooth chart restrictions. -/
theorem globalSmoothAtlas_cover (z : (U).toScheme) :
    ∃ i x, globalSmoothAtlasMap hπ data j hj i x = z := by
  obtain ⟨i, x, hx⟩ := globalIntegralAtlas_cover hπ data j hj z.val
  have hp : x ∈ globalSmoothAtlasOpen hπ data j hj i := by
    change globalIntegralAtlasMap hπ data j hj i x ∈ U
    rw [hx]
    exact z.property
  refine ⟨i, ⟨x, hp⟩, Subtype.ext ?_⟩
  exact (congrArg (fun f : (globalSmoothAtlasOpen hπ data j hj i).toScheme ⟶
    finiteGlobalModel hπ data j hj => f ⟨x, hp⟩)
      (globalSmoothAtlasMap_inclusion hπ data j hj i)).trans hx

/-- The complete resolved smooth locus has a finite cover by the actual chart restrictions. -/
def globalSmoothOpenCover : (U).toScheme.OpenCover where
  I₀ := Fin (j + 3)
  X i := (globalSmoothAtlasOpen hπ data j hj i).toScheme
  f := globalSmoothAtlasMap hπ data j hj
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨globalSmoothAtlas_cover hπ data j hj, fun i => inferInstance⟩

end FLT.Mazur.WeierstrassDividedDepth
