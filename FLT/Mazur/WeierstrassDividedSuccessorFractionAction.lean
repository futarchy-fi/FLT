/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalRegularLift
public import FLT.Mazur.WeierstrassDividedSuccessorFractionCenter

/-!
# Actual affine successor lifts for all fraction inputs

The proved regular output centers construct maps into the whole successor
model. Flat affine restrictions retain their uniqueness.
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
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "g" => WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "hg" => WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "q" => previousOriginalMap hπ d e
local notation "U" => successorDividedAffineCover hπ data j hj a
local notation "D" => successorDividedInputCover hπ data j hj a
variable (t : Fin 3) (z : ((successorDividedInputCover hπ data j hj a).X
  (some (some t))).affineCover.I₀)
local notation "i" => Sigma.mk (some (some t)) z
local notation "C" => BlowupFractionChart.chart I (g t)

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)

local notation "v" => finiteNormalizedChart hπ data j hj

/-- Construct the successor lift on each actual fraction-input affine member. -/
def successorFractionAffineAction :
    Spec ((U).X i) ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  finiteGlobalRegularLift hπ data j hj (successorDividedAlpha hπ data j hj a i)
    (successorFractionDenominator hπ data j hj a t z)
    (successorFractionAlpha_center hπ data j hj a t z ha)
    (successorFractionDenominator_regular hπ data j hj a t z)

/-- The constructed map retains its actual normalized divided output. -/
@[reassoc] theorem successorFractionAffineAction_step :
    successorFractionAffineAction hπ data j hj a t z ha ≫ finiteGlobalStep hπ data j hj =
      (U).f i ≫ pullback.snd _ _ ≫ v := by
  rw [successorFractionAffineAction, finiteGlobalRegularLift_step, successorDividedAlpha_spec]
  exact Category.assoc _ _ _

/-- The constructed lift contracts to the existing action on its entire source. -/
@[reassoc] theorem successorFractionAffineAction_output :
    successorFractionAffineAction hπ data j hj a t z ha ≫ finiteGlobalStep hπ data j hj =
      (U).f i ≫ pullback.fst _ _ ≫ successorActionOutput hπ data j hj a := by
  rw [successorFractionAffineAction_step, ← pullback.condition]

/-- Any flat affine restriction retains uniqueness of the actual successor lift. -/
theorem successorFractionAffineAction_flat_unique {S : Type u} [CommRing S]
    (p : Spec (.of S) ⟶ Spec ((U).X i)) [Flat p]
    (b : Spec (.of S) ⟶ finiteGlobalModel hπ data (j + 1) hj)
    (hb : b ≫ finiteGlobalStep hπ data j hj =
      p ≫ successorFractionAffineAction hπ data j hj a t z ha ≫ finiteGlobalStep hπ data j hj) :
    b = p ≫ successorFractionAffineAction hπ data j hj a t z ha := by
  let ψ := affineChartRingHom p
  have hp : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec p
  have hflat : RingHom.Flat ψ := by
    apply (Flat.SpecMap_iff (f := CommRingCat.ofHom ψ)).mp
    rw [hp]
    infer_instance
  have hc : (p ≫ successorFractionAffineAction hπ data j hj a t z ha) ≫
      finiteGlobalStep hπ data j hj =
        Spec.map (CommRingCat.ofHom
          (ψ.comp (successorDividedAlpha hπ data j hj a i))) ≫ v := by
    rw [Category.assoc, successorFractionAffineAction_step, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hp, successorDividedAlpha_spec]
    simp only [Category.assoc]
  apply finiteGlobalStep_regular_center_ext hπ data j hj
    (ψ.comp (successorDividedAlpha hπ data j hj a i))
    (ψ (successorFractionDenominator hπ data j hj a t z))
    (successorFractionAlpha_mapped_center hπ data j hj a t z ha ψ)
    (successorFractionDenominator_mapped_regular hπ data j hj a t z ψ hflat)
    b (p ≫ successorFractionAffineAction hπ data j hj a t z ha)
  · exact hb.trans ((Category.assoc _ _ _).symm.trans hc)
  · exact hc

end FLT.Mazur.WeierstrassDividedDepth
