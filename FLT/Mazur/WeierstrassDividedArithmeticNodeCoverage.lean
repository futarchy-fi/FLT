/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticOppositeNodeOpen
public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticCoordinates
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts

/-!
# Coverage of the successive arithmetic open inside the original resolved stage

The image of the actual tensor chart is exactly the union of the two polygon
node images. This identifies the local piece of the global arithmetic atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "e" => WeierstrassSuccessiveX.baseChangeEquiv W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q
local notation "c" => WeierstrassSuccessiveX.arithmeticNodeChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6

/-- The successive arithmetic chart placed in the original global stage. -/
def finiteArithmeticSuccessiveChart :
    Spec (.of (WeierstrassSuccessiveX.ExtendedCoordinate W (π ^ (start + j)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)) ⟶
        finiteGlobalArithmeticStage hπ data (j + 1) hj m :=
  Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
    globalSuccessiveTensorChart hπ data Q j hj ≫
      (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom

/-- The original successive arithmetic chart is an open immersion. -/
theorem finiteArithmeticSuccessiveChart_isOpenImmersion :
    IsOpenImmersion (finiteArithmeticSuccessiveChart hπ data j hj m) := by
  have he : IsIso (CommRingCat.ofHom (e).toRingHom) :=
    (e).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold finiteArithmeticSuccessiveChart
  infer_instance

/-- Its coefficient structure is the unchanged arithmetic quotient structure. -/
@[reassoc] theorem finiteArithmeticSuccessiveChart_structure :
    finiteArithmeticSuccessiveChart hπ data j hj m ≫
      finiteGlobalArithmeticStructure hπ data (j + 1) hj m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (WeierstrassSuccessiveX.ExtendedCoordinate W (π ^ (start + j)) π
            (Data.b3 d) (Data.b4 d) (Data.b6 d) Q))) := by
  change (Spec.map (CommRingCat.ofHom (e).toAlgHom.toRingHom) ≫
    globalSuccessiveTensorChart hπ data Q j hj ≫
      (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom) ≫
        pullback.snd (finiteGlobalStructure hπ data (j + 1) hj) q = _
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
    globalSuccessiveTensorChart_structure]
  exact specAlgHom_structure (e).toAlgHom

/-- Every point in the successive arithmetic open is in one of the actual polygon opens. -/
theorem finiteArithmeticNodeCharts_cover
    (p : Spec (.of (WeierstrassSuccessiveX.ExtendedCoordinate W (π ^ (start + j)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q))) :
    (∃ x, finiteArithmeticNodeChart hπ data j hj m ha hs h2 h3 h4 h6 x =
      finiteArithmeticSuccessiveChart hπ data j hj m p) ∨
    ∃ x, finiteArithmeticOppositeNodeChart hπ data j hj m ha hs h2 h3 h4 h6 x =
      finiteArithmeticSuccessiveChart hπ data j hj m p := by
  obtain ⟨x, hx⟩ | ⟨x, hx⟩ := WeierstrassSuccessiveX.arithmeticNodeCharts_cover
    π m W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
    ha hs h2 h3 h4 h6 p
  · exact Or.inl ⟨x, congrArg (finiteArithmeticSuccessiveChart hπ data j hj m) hx⟩
  · exact Or.inr ⟨x, congrArg (finiteArithmeticSuccessiveChart hπ data j hj m) hx⟩

/-- The two original polygon images are exactly the original successive arithmetic open. -/
theorem finiteArithmeticNodeCharts_range_union :
    Set.range (finiteArithmeticNodeChart hπ data j hj m ha hs h2 h3 h4 h6) ∪
      Set.range (finiteArithmeticOppositeNodeChart hπ data j hj m ha hs h2 h3 h4 h6) =
        Set.range (finiteArithmeticSuccessiveChart hπ data j hj m) := by
  ext p
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨c x, rfl⟩
    · exact ⟨WeierstrassSuccessiveX.arithmeticOppositeNodeChart π m W (π ^ (start + j))
        (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6 x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact finiteArithmeticNodeCharts_cover hπ data j hj m ha hs h2 h3 h4 h6 x

end FLT.Mazur.WeierstrassDividedDepth
