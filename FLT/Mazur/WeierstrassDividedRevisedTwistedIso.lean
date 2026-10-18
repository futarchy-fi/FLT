/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedGlobalBase

/-!
# The complete simultaneous twisted stage over the revised polygon

The actual first-order comparison transports through the existing simultaneous
isomorphism. Every chart and every full pairwise overlap is retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction arithmeticRevisedPolygon
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "I" => simultaneousTwistedArithmeticIso hπ data H 1 j hj u hu
local notation "E" => arithmeticFirstOriginalRevisedGlobalIso hπ data H j hj u hu
local notation "B" => arithmeticRevisedPolygonToBase data H 1 j hj u hu
local notation "S" => finiteGlobalArithmeticStructure hπ data (j + 1) hj 1
local notation "e" => twistedArithmeticAtlasIso hπ data H 1 j hj u hu
local notation "c" => simultaneousTwistedArithmeticChart hπ data H 1 j hj u hu
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu

/-- The full simultaneous target is isomorphic to the independently glued revised polygon. -/
def arithmeticFirstTwistedRevisedIso :
    simultaneousTwistedArithmeticStage hπ data H 1 j hj u hu ≅
      arithmeticRevisedPolygon data H 1 j hj u hu := (I).symm ≪≫ E

local notation "J" => arithmeticFirstTwistedRevisedIso hπ data H j hj u hu

/-- The transported comparison recovers the actual original global morphism. -/
@[reassoc] theorem arithmeticFirstTwistedRevisedIso_original :
    (I).hom ≫ (J).hom = (E).hom := by
  rw [arithmeticFirstTwistedRevisedIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- The comparison preserves the coefficient structure transported from the original stage. -/
@[reassoc] theorem arithmeticFirstTwistedRevisedIso_base :
    (J).hom ≫ B = (I).inv ≫ S := by
  rw [arithmeticFirstTwistedRevisedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (I).inv ≫ arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu ≫ B = _
  rw [arithmeticFirstOriginalRevisedGlobalMap_base]

/-- The simultaneous comparison is an isomorphism over the actual arithmetic quotient. -/
def arithmeticFirstTwistedRevisedOverIso : Over.mk ((I).inv ≫ S) ≅ Over.mk B :=
  Over.isoMk J (arithmeticFirstTwistedRevisedIso_base hπ data H j hj u hu)

/-- Each whole twisted chart uses the inverse of its actual original chart normalization. -/
def arithmeticFirstTwistedRevisedChart (i : ArithmeticChartLabel (j + 1)) :
    twistedArithmeticAtlasObject hπ data H 1 j hj i ⟶
      arithmeticRevisedPolygon data H 1 j hj u hu := (e i).inv ≫ G i

local notation "g" => arithmeticFirstTwistedRevisedChart hπ data H j hj u hu

/-- Every simultaneous chart satisfies its full original comparison equation. -/
@[reassoc] theorem arithmeticFirstTwistedRevisedIso_chart
    (i : ArithmeticChartLabel (j + 1)) : c i ≫ (J).hom = g i := by
  rw [arithmeticFirstTwistedRevisedIso, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, simultaneousTwistedArithmeticChart_global]
  change ((e i).inv ≫ arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj i) ≫
    arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu = g i
  rw [Category.assoc, arithmeticFirstOriginalRevisedGlobalMap_chart]
  rfl

/-- No points of a simultaneous pairwise overlap are removed in the revised target. -/
def arithmeticFirstTwistedRevisedOverlapIso (a b : ArithmeticChartLabel (j + 1)) :
    pullback (c a) (c b) ≅ pullback (g a) (g b) :=
  asIso (pullback.map (c a) (c b) (g a) (g b) (𝟙 _) (𝟙 _) (J).hom
    (by rw [Category.id_comp, arithmeticFirstTwistedRevisedIso_chart])
    (by rw [Category.id_comp, arithmeticFirstTwistedRevisedIso_chart]))

/-- The complete overlap comparison preserves the first chart projection. -/
@[reassoc] theorem arithmeticFirstTwistedRevisedOverlapIso_fst
    (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticFirstTwistedRevisedOverlapIso hπ data H j hj u hu a b).hom ≫
      pullback.fst (g a) (g b) = pullback.fst (c a) (c b) := by
  dsimp only [arithmeticFirstTwistedRevisedOverlapIso, asIso_hom]
  rw [pullback.lift_fst, Category.comp_id]

/-- The complete overlap comparison also preserves the second chart projection. -/
@[reassoc] theorem arithmeticFirstTwistedRevisedOverlapIso_snd
    (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticFirstTwistedRevisedOverlapIso hπ data H j hj u hu a b).hom ≫
      pullback.snd (g a) (g b) = pullback.snd (c a) (c b) := by
  dsimp only [arithmeticFirstTwistedRevisedOverlapIso, asIso_hom]
  rw [pullback.lift_snd, Category.comp_id]

end FLT.Mazur.WeierstrassDividedDepth
