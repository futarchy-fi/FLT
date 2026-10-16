/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosingAttachmentUnion
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

/-!
# One transported atlas containing both closing branches

All original labels are retained. Every full retained node is normalized with
its original branch orientation, and the single terminal node is normalized
only once. Infinity and the original initial charts remain in the cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "A" => arithmeticLabeledAtlasObject hπ data H m (j + 1) hj

/-- The retained target orientation is exactly the branch swap used by the polygon maps. -/
def twistedRetainedOrientation (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q τ :=
  if b then branchSwapIso Q τ else Iso.refl _

/-- Full normalized retained and terminal nodes, with all remaining original labels included. -/
def twistedArithmeticAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .terminal => PolygonSmoothing.chart Q τ
  | .retained _ _ => PolygonSmoothing.chart Q τ
  | .infinity => A .infinity
  | .initial b => A (.initial b)

variable (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "P" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu m
local notation "T" => twistedArithmeticAtlasObject hπ data H m j hj

/-- Constructed whole-chart comparisons, including the true-branch coordinate swap. -/
def twistedArithmeticAtlasIso (i : ArithmeticChartLabel (j + 1)) : A i ≅ T i :=
  match i with
  | .terminal => P
  | .retained a b => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj a ≪≫
      twistedRetainedOrientation data H m b
  | .infinity => Iso.refl _
  | .initial _ => Iso.refl _

/-- The target chart inclusion is transported from its unchanged original global inclusion. -/
def twistedArithmeticAtlasMap (i : ArithmeticChartLabel (j + 1)) :
    T i ⟶ finiteGlobalArithmeticStage hπ data (j + 1) hj m :=
  (twistedArithmeticAtlasIso hπ data H m j hj u hu i).inv ≫ c i

instance twistedArithmeticAtlasMap_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (twistedArithmeticAtlasMap hπ data H m j hj u hu i) := by
  unfold twistedArithmeticAtlasMap
  infer_instance

/-- Each target chart recovers the exact original map after its constructed comparison. -/
@[reassoc] theorem twistedArithmeticAtlasIso_map (i : ArithmeticChartLabel (j + 1)) :
    (twistedArithmeticAtlasIso hπ data H m j hj u hu i).hom ≫
      twistedArithmeticAtlasMap hπ data H m j hj u hu i = c i := by
  rw [twistedArithmeticAtlasMap, Iso.hom_inv_id_assoc]

/-- The transported labels still cover the entire original global arithmetic stage. -/
theorem twistedArithmeticAtlas_cover (z : finiteGlobalArithmeticStage hπ data (j + 1) hj m) :
    ∃ i x, twistedArithmeticAtlasMap hπ data H m j hj u hu i x = z := by
  obtain ⟨i, x, rfl⟩ := arithmeticLabeledAtlas_cover hπ data H m (j + 1) hj z
  exact ⟨i, (twistedArithmeticAtlasIso hπ data H m j hj u hu i).hom x,
    congrArg (fun f ↦ f x) (twistedArithmeticAtlasIso_map hπ data H m j hj u hu i)⟩

/-- One finite open cover contains both closing pairs and every remaining original label. -/
def twistedArithmeticOpenCover :
    (finiteGlobalArithmeticStage hπ data (j + 1) hj m).OpenCover where
  I₀ := ArithmeticChartLabel (j + 1)
  X := T
  f := twistedArithmeticAtlasMap hπ data H m j hj u hu
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨twistedArithmeticAtlas_cover hπ data H m j hj u hu,
      fun i ↦ twistedArithmeticAtlasMap_isOpenImmersion hπ data H m j hj u hu i⟩

end FLT.Mazur.WeierstrassDividedDepth
