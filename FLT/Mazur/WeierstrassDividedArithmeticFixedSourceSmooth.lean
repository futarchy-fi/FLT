/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentSource
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticSmoothCover
public import FLT.Mazur.WeierstrassDividedBoundaryRangeTransport

/-!
# Smooth coverage in the fixed indexed arithmetic source

Recover the original retained coordinates and apply the arithmetic smooth
criterion without changing the ambient input or quotient order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
open scoped TensorProduct
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
  PrincipalOpenTensor.transitionIso TensorProduct
/-- An equality of whole chart maps transports the corresponding pointwise open test. -/
theorem fixedSource_mem_transport {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (he : f ≫ g = h) (U : Z.Opens) (p : X) :
    g (f p) ∈ U ↔ h p ∈ U := by
  rw [← Scheme.Hom.comp_apply, he]

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsLocalRing R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
  (hgen : IsLocalRing.maximalIdeal R = ideal R π)
  (m k : ℕ) (hk : k ≤ n) (j : ℕ) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "eNext" => data ⟨j + 2, by omega⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) 2
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso Q x u (previousBoundaryEquiv hπ e eNext)
local notation "a" => (A).inv ≫ PrincipalOpenTensor.inclusion Q t
local notation "b" => (B).inv ≫ PrincipalOpenTensor.inclusion Q u
local notation "ia" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "ib" => (Fin.succ ⟨k - (j + 1), by omega⟩ : Fin (k + 3))
local notation "leftIso" => arithmeticRetainedTensorIso hπ data m k hk j (by omega)
local notation "rightIso" => arithmeticRetainedTensorIso hπ data m k hk (j + 1) (by omega)
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk

local notation "coords" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "original" => arithmeticRetainedTensorChart hπ data m k hk j
  ((Nat.lt_succ_self j).trans_le ((Nat.le_succ (j + 1)).trans hj))
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

attribute [local irreducible] arithmeticFixedAdjacentSourceCoordinates
  arithmeticRetainedTensorChart

local instance arithmeticFixedCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- The retained original chart has exactly its original quotient coefficient structure. -/
@[reassoc] theorem arithmeticFixedRetainedChart_structure :
    original ≫ s = Spec.map (CommRingCat.ofHom (algebraMap Q
      (ScalarExtension W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) Q))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show j + 1 ≤ k by omega)
  rw [arithmeticRetainedTensorChart_eq hπ data m (j + 1 + r) hk j (by omega) r hk]
  exact finiteArithmeticOlderTensorChart_structure hπ data m j (by omega) r hk

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Recovering coordinates leaves the whole indexed arithmetic input unchanged. -/
@[reassoc] theorem arithmeticFixedSourceCoordinates_chart : coords ≫ original = chart ia := by
  unfold arithmeticFixedAdjacentSourceCoordinates arithmeticRetainedTensorChart
  rw [Iso.inv_hom_id_assoc]

include D hgen in
/-- Full indexed smoothness is exactly the original incidence-or-horizontal test. -/
theorem arithmeticFixedAdjacentSource_smooth_iff
    (hd : 2 * (start + j + 1) ≤ depth)
    (p : globalTensorAtlasObject hπ data Q k hk ia) :
    chart ia p ∈ (s).smoothLocus ↔
      tt ∉ (coords p).asIdeal ∨ oldU ∉ (coords p).asIdeal := by
  have he := arithmeticAnyDepth_chart_mem_smooth_iff D hπ hgen (start + j) hd
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) m original s
    (arithmeticFixedRetainedChart_structure hπ data m k hk j hj) (coords p)
  exact (fixedSource_mem_transport coords original (chart ia)
    (arithmeticFixedSourceCoordinates_chart hπ data m k hk j hj) (s).smoothLocus p).symm.trans he

end FLT.Mazur.WeierstrassDividedDepth
