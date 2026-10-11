/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalRegularLift
public import FLT.Mazur.WeierstrassDividedSuccessorRetainedCenter

/-!
# Actual affine lifts on every retained successor input

The proved unit centers of the complete retained-input refinement give
actual successor maps, unique after arbitrary affine restrictions.
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
local notation "U" => successorRetainedAffineCover hπ data j hj a

local notation "D" => successorDividedInputCover hπ data j hj a
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)

/-- Construct the whole successor lift from a proved unit output center. -/
def successorRetainedAffineAction (i : (U).I₀) :
    Spec ((U).X i) ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  finiteGlobalRegularLift hπ data j hj (successorRetainedAlpha hπ data j hj a i) 1
    ((successorRetained_center hπ data j hj a ha i).trans Ideal.span_singleton_one.symm)
    isRegular_one

/-- The actual local lift has exactly the normalized output of its simultaneous domain. -/
@[reassoc] theorem successorRetainedAffineAction_step (i : (U).I₀) :
    successorRetainedAffineAction hπ data j hj a ha i ≫ finiteGlobalStep hπ data j hj =
      (U).f i ≫ (D).f (some none) ≫ pullback.snd _ _ ≫ v := by
  rw [successorRetainedAffineAction, finiteGlobalRegularLift_step, successorRetainedAlpha_spec,
    Category.assoc, Category.assoc]

/-- Unit-center lifts contract to the existing action on their entire source member. -/
@[reassoc] theorem successorRetainedAffineAction_output (i : (U).I₀) :
    successorRetainedAffineAction hπ data j hj a ha i ≫ finiteGlobalStep hπ data j hj =
      (U).f i ≫ (D).f (some none) ≫ pullback.fst _ _ ≫ successorActionOutput hπ data j hj a := by
  rw [successorRetainedAffineAction_step, ← pullback.condition]

/-- Every affine restriction preserves uniqueness, with no flatness requirement. -/
theorem successorRetainedAffineAction_affine_unique (i : (U).I₀)
    {S : Type u} [CommRing S] (p : Spec (.of S) ⟶ Spec ((U).X i))
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorRetainedAffineAction hπ data j hj a ha i ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorRetainedAffineAction hπ data j hj a ha i := by
  let ψ := affineChartRingHom p
  have hψ : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec _
  have hI : (I).map (ψ.comp (successorRetainedAlpha hπ data j hj a i)) = Ideal.span {1} := by
    rw [← Ideal.map_map, successorRetained_center hπ data j hj a ha i,
      Ideal.map_top, Ideal.span_singleton_one]
  have he : (p ≫ successorRetainedAffineAction hπ data j hj a ha i) ≫
      finiteGlobalStep hπ data j hj =
      Spec.map (CommRingCat.ofHom (ψ.comp (successorRetainedAlpha hπ data j hj a i))) ≫ v := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hψ, Category.assoc,
      successorRetainedAffineAction_step, successorRetainedAlpha_spec]
    simp only [Category.assoc]
  exact finiteGlobalStep_regular_center_ext hπ data j hj _ 1 hI isRegular_one
    b _ (hb.trans ((Category.assoc _ _ _).symm.trans he)) he

end FLT.Mazur.WeierstrassDividedDepth
