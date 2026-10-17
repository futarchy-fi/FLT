/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointAtlas
public import FLT.Mazur.WeierstrassDividedResidualLiftAtlasEdges

/-!
# Original full overlaps in the simultaneous second atlas

Every original adjacent edge and full fiber product is transported through
its installed node corrections. The predecessor smoothing is not identified
with the old smoothing in these comparisons.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticSecondJointAtlasCorrection arithmeticSecondJointAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "ι" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "E" => arithmeticSecondJointAtlasCorrection hπ data H m j hj u hu
local notation "κ" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticSecondJointAtlasIso hπ data H m j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m

/-- The installed chart correction recovers the entire previous inclusion. -/
@[reassoc] theorem arithmeticSecondJointAtlasCorrection_chart
    (i : ArithmeticChartLabel (j + 1)) : (E i).hom ≫ ι i = κ i := by
  rw [arithmeticSecondJointAtlasChart, Iso.hom_inv_id_assoc]

/-- Every original consecutive edge keeps both actual endpoint corrections. -/
@[reassoc] theorem arithmeticSecondJointAtlas_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    (leftBranchOpen Q t ≫ (J (.retained ⟨a, by omega⟩ b)).hom) ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (precedingBranch Q t ≫ (J (.retained ⟨a + 1, ha⟩ b)).hom) ≫
        ι (.retained ⟨a + 1, ha⟩ b) := by
  rw [Category.assoc, Category.assoc, ← arithmeticSecondJointAtlasIso_chart,
    ← arithmeticSecondJointAtlasIso_chart, ← Category.assoc, ← Category.assoc,
    arithmeticLabeledAtlas_adjacent_overlap]

/-- The complete original overlap is isomorphic to the installed simultaneous overlap. -/
def arithmeticSecondJointFullOverlapIso (a b : ArithmeticChartLabel (j + 1)) :
    pullback (c a) (c b) ≅ pullback (ι a) (ι b) :=
  asIso (pullback.map (c a) (c b) (ι a) (ι b) (J a).hom (J b).hom (G).hom
    (arithmeticSecondJointAtlasIso_chart hπ data H m j hj u hu a)
    (arithmeticSecondJointAtlasIso_chart hπ data H m j hj u hu b))

/-- The first full overlap projection retains its actual installed endpoint. -/
@[reassoc] theorem arithmeticSecondJointFullOverlapIso_fst
    (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticSecondJointFullOverlapIso hπ data H m j hj u hu a b).hom ≫
      pullback.fst (ι a) (ι b) = pullback.fst (c a) (c b) ≫ (J a).hom :=
  pullback.lift_fst _ _ _

/-- The second full overlap projection retains its actual installed endpoint. -/
@[reassoc] theorem arithmeticSecondJointFullOverlapIso_snd
    (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticSecondJointFullOverlapIso hπ data H m j hj u hu a b).hom ≫
      pullback.snd (ι a) (ι b) = pullback.snd (c a) (c b) ≫ (J b).hom :=
  pullback.lift_snd _ _ _

end FLT.Mazur.WeierstrassDividedDepth
