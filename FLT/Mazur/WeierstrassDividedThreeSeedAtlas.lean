/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeSeedState
public import FLT.Mazur.WeierstrassDividedFifthFartherIdentification
public import FLT.Mazur.WeierstrassDividedFifthFartherEndIdentification

/-!
# Uniform depth-three seed labels with their actual fifth identifications

The four retained nodes keep their full smoothings. The final identification
includes the original orientation; the initial open, terminal and infinity persist.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "S" => arithmeticThreeSeedState hπ data H hj u hu
local notation "B" => arithmeticFifthFartherAtlasObject hπ data H m 3 hj u hu

/-- The uniform seed has the exact four smoothings selected by its algebraic state. -/
def arithmeticThreeSeedAtlasObject : ArithmeticChartLabel 4 → Scheme
  | .initial b => arithmeticFifthFartherObject hπ data H m 3 hj u hu b
  | .retained i b => PolygonSmoothing.chart Q ((S).retained m i b)
  | .terminal => PolygonSmoothing.chart Q ((S).terminal m)
  | .infinity => B .infinity

local notation "A" => arithmeticThreeSeedAtlasObject hπ data H m hj u hu

/-- The uniform labels retain every explicit identification of the fifth depth-three atlas. -/
def arithmeticThreeSeedIdentification (i : ArithmeticChartLabel 4) : A i ≅ B i :=
  match i with
  | .initial b => arithmeticFifthFartherIdentification hπ data H m 3 hj u hu rfl b
  | .retained ⟨0, _⟩ b =>
      arithmeticFifthFartherNeighborIdentification hπ data H m 3 hj u hu rfl b
  | .retained ⟨1, _⟩ b =>
      arithmeticFifthFartherNodeIdentification hπ data H m 3 hj u hu rfl .outer
        (fun h ↦ FifthDeepNode.noConfusion h) 1 rfl b
  | .retained ⟨2, _⟩ b =>
      arithmeticFifthFartherNodeIdentification hπ data H m 3 hj u hu rfl .predecessor
        (fun h ↦ FifthDeepNode.noConfusion h) 2 rfl b
  | .retained ⟨3, _⟩ b => twistedRetainedOrientation data H m b ≪≫
      arithmeticFifthFartherLastIdentification hπ data H m 3 hj u hu b
  | .retained ⟨a + 4, ha⟩ _ => False.elim (by omega)
  | .terminal => Iso.refl _
  | .infinity => Iso.refl _

local notation "J" => arithmeticThreeSeedIdentification hπ data H m hj u hu
local notation "κ" => arithmeticFifthFartherAtlasChart hπ data H m 3 hj u hu rfl

/-- The identified seed includes into the unchanged depth-three global target. -/
def arithmeticThreeSeedAtlasChart (i : ArithmeticChartLabel 4) :
    A i ⟶ simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu := (J i).hom ≫ κ i

instance arithmeticThreeSeedAtlasChart_isOpenImmersion (i : ArithmeticChartLabel 4) :
    IsOpenImmersion (arithmeticThreeSeedAtlasChart hπ data H m hj u hu i) := by
  unfold arithmeticThreeSeedAtlasChart
  infer_instance

/-- Each original chart reaches the uniform seed through the actual fifth comparison. -/
def arithmeticThreeSeedAtlasIso (i : ArithmeticChartLabel 4) :
    arithmeticLabeledAtlasObject hπ data H m 4 hj i ≅ A i :=
  arithmeticFifthFartherAtlasIso hπ data H m 3 hj u hu rfl i ≪≫ (J i).symm

local notation "ι" => arithmeticThreeSeedAtlasChart hπ data H m hj u hu

/-- The identified seed preserves the full original inclusion. -/
@[reassoc] theorem arithmeticThreeSeedAtlasIso_chart (i : ArithmeticChartLabel 4) :
    arithmeticLabeledAtlasMap hπ data H m 4 hj i ≫
        (simultaneousTwistedArithmeticIso hπ data H m 3 hj u hu).hom =
      (arithmeticThreeSeedAtlasIso hπ data H m hj u hu i).hom ≫ ι i := by
  simp only [arithmeticThreeSeedAtlasIso, arithmeticThreeSeedAtlasChart, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact arithmeticFifthFartherAtlasIso_chart hπ data H m 3 hj u hu rfl i

attribute [local irreducible] arithmeticThreeSeedAtlasChart

/-- Explicit identifications transport the whole fifth open cover, including infinity. -/
def arithmeticThreeSeedOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu).OpenCover :=
  (arithmeticFifthFartherOpenCover hπ data H m 3 hj u hu rfl).copy
    (ArithmeticChartLabel 4) A ι (Equiv.refl _) J
      (fun _ ↦ by rw [arithmeticThreeSeedAtlasChart]; rfl)

/-- Every point of the original global target remains covered by a uniform seed chart. -/
theorem arithmeticThreeSeedAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m 3 hj u hu) :
    ∃ i x, ι i x = z := (arithmeticThreeSeedOpenCover hπ data H m hj u hu).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
