/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorAtlasCoordinates
public import FLT.Mazur.WeierstrassDividedGlobalRegularLift

/-!
# Actual lifts for unit-center members of the complete successor atlas

A proved unit output center constructs the whole successor action map on
that member. Its uniqueness holds after every affine restriction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))

local notation "v" => finiteNormalizedChart hπ data j hj

local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => successorDividedAffineCover hπ data j hj a

local notation "D" => successorDividedInputCover hπ data j hj a
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
/-- Construct the whole successor lift from a proved unit output center. -/
def successorDividedUnitAction (i : (U).I₀)
    (hi : (I).map (successorDividedAlpha hπ data j hj a i) = ⊤) :
    Spec ((U).X i) ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  finiteGlobalRegularLift hπ data j hj (successorDividedAlpha hπ data j hj a i) 1
    (hi.trans Ideal.span_singleton_one.symm) isRegular_one

/-- The actual local lift has exactly the normalized output of its simultaneous domain. -/
@[reassoc] theorem successorDividedUnitAction_step (i : (U).I₀)
    (hi : (I).map (successorDividedAlpha hπ data j hj a i) = ⊤) :
    successorDividedUnitAction hπ data j hj a i hi ≫ finiteGlobalStep hπ data j hj =
      (U).f i ≫ pullback.snd _ _ ≫ v := by
  rw [successorDividedUnitAction, finiteGlobalRegularLift_step, successorDividedAlpha_spec,
    Category.assoc]

/-- Unit-center lifts contract to the existing action on their entire source member. -/
@[reassoc] theorem successorDividedUnitAction_output (i : (U).I₀)
    (hi : (I).map (successorDividedAlpha hπ data j hj a i) = ⊤) :
    successorDividedUnitAction hπ data j hj a i hi ≫ finiteGlobalStep hπ data j hj =
      (U).f i ≫ pullback.fst _ _ ≫ successorActionOutput hπ data j hj a := by
  rw [successorDividedUnitAction_step, ← pullback.condition]

/-- Every affine restriction preserves uniqueness, with no flatness requirement. -/
theorem successorDividedUnitAction_affine_unique (i : (U).I₀)
    (hi : (I).map (successorDividedAlpha hπ data j hj a i) = ⊤)
    {S : Type u} [CommRing S] (p : Spec (.of S) ⟶ Spec ((U).X i))
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorDividedUnitAction hπ data j hj a i hi ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorDividedUnitAction hπ data j hj a i hi := by
  let ψ := affineChartRingHom p
  have hψ : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec _
  have hI : (I).map (ψ.comp (successorDividedAlpha hπ data j hj a i)) = Ideal.span {1} := by
    rw [← Ideal.map_map, hi, Ideal.map_top, Ideal.span_singleton_one]
  have he : (p ≫ successorDividedUnitAction hπ data j hj a i hi) ≫
      finiteGlobalStep hπ data j hj =
      Spec.map (CommRingCat.ofHom (ψ.comp (successorDividedAlpha hπ data j hj a i))) ≫ v := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ, Category.assoc,
      successorDividedUnitAction_step, successorDividedAlpha_spec]
    simp only [Category.assoc]
  exact finiteGlobalStep_regular_center_ext hπ data j hj _ 1 hI isRegular_one
    b _ (hb.trans ((Category.assoc _ _ _).symm.trans he)) he

end FLT.Mazur.WeierstrassDividedDepth
