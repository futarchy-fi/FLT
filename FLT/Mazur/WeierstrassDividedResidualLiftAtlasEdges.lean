/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticPositiveEdgeCompatibility

/-!
# Exact overlap arrows after the full lifted residual corrections

All arrows are transported through their actual node corrections. In
particular, the incoming arrow at a corrected retained node is retained with
its full correction, rather than being assumed unchanged at higher order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ι" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "E" => arithmeticResidualLiftAtlasCorrection hπ data H m j hj u hu
local notation "κ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticResidualLiftAtlasIso hπ data H m j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m

/-- The full corrected inclusion cancels precisely its constructed chart correction. -/
@[reassoc] theorem arithmeticResidualLiftAtlasCorrection_chart
    (i : ArithmeticChartLabel (j + 1)) : (E i).hom ≫ ι i = κ i := by
  rw [arithmeticResidualLiftAtlasChart, Iso.hom_inv_id_assoc]

/-- Both closing arrows include the actual higher-order terminal and retained corrections. -/
@[reassoc] theorem arithmeticResidualLiftAtlas_closing (b : Bool) :
    (arithmeticClosingRetainedBoundary data H m ≫
        (twistedRetainedOrientation data H m b).hom ≫
          (arithmeticResidualLiftOrientedIso hπ data H m j hj u hu b).hom) ≫
      ι (.retained ⟨j, by omega⟩ b) =
    (arithmeticTerminalChangedBoundary data H m j hj u hu b ≫
        (arithmeticResidualLiftTerminalIso hπ data H m j hj u hu).hom) ≫ ι .terminal := by
  have hr := arithmeticResidualLiftAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨j, by omega⟩ b)
  have ht := arithmeticResidualLiftAtlasCorrection_chart hπ data H m j hj u hu .terminal
  simp only [arithmeticResidualLiftAtlasCorrection, ↓reduceIte] at hr ht
  rw [Category.assoc, Category.assoc, hr, Category.assoc, ht]
  exact changedArithmeticAtlas_closing hπ data H m j hj u hu b

/-- Consecutive edges keep the full transported incoming arrow even on the corrected last node. -/
@[reassoc] theorem arithmeticResidualLiftAtlas_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    (leftBranchOpen Q t ≫ (J (.retained ⟨a, by omega⟩ b)).hom) ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (precedingBranch Q t ≫ (J (.retained ⟨a + 1, ha⟩ b)).hom) ≫
        ι (.retained ⟨a + 1, ha⟩ b) := by
  rw [Category.assoc, Category.assoc, ← arithmeticResidualLiftAtlasIso_chart,
    ← arithmeticResidualLiftAtlasIso_chart, ← Category.assoc, ← Category.assoc,
    arithmeticLabeledAtlas_adjacent_overlap]

/-- Every original full overlap is identified with the corrected full overlap. -/
def arithmeticResidualLiftFullOverlapIso (a b : ArithmeticChartLabel (j + 1)) :
    pullback (c a) (c b) ≅ pullback (ι a) (ι b) :=
  asIso (pullback.map (c a) (c b) (ι a) (ι b) (J a).hom (J b).hom (G).hom
    (arithmeticResidualLiftAtlasIso_chart hπ data H m j hj u hu a)
    (arithmeticResidualLiftAtlasIso_chart hπ data H m j hj u hu b))

/-- The first full overlap projection uses its actual corrected label. -/
@[reassoc] theorem arithmeticResidualLiftFullOverlapIso_fst
    (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticResidualLiftFullOverlapIso hπ data H m j hj u hu a b).hom ≫
      pullback.fst (ι a) (ι b) = pullback.fst (c a) (c b) ≫ (J a).hom :=
  pullback.lift_fst _ _ _

/-- The second full overlap projection uses its actual corrected label. -/
@[reassoc] theorem arithmeticResidualLiftFullOverlapIso_snd
    (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticResidualLiftFullOverlapIso hπ data H m j hj u hu a b).hom ≫
      pullback.snd (ι a) (ι b) = pullback.snd (c a) (c b) ≫ (J b).hom :=
  pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
