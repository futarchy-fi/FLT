/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorFractionCoordinates

/-!
# Coefficient algebra on every actual successor fraction presentation

The original action identifies the input and output coefficient maps.
Thus the actual atlas carries algebra presentations suitable for the
arbitrary-depth normalized fraction lift.
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

/-- Original divided coordinates preserve the complete coefficient structure map. -/
theorem successorFractionOriginal_structure (γ : B →+* (U).X i) :
    (Spec.map (CommRingCat.ofHom (γ.comp (q).toRingHom)) ≫ integralCurveChart W 2) ≫
        integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (γ.comp (algebraMap R B))) := by
  rw [Category.assoc, integralCurveChart_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact congrArg γ ((q).commutes r)

/-- The canonical coefficient algebra on each actual fraction-input affine member. -/
instance successorFractionAlgebra : Algebra R ((U).X i) :=
  ((successorFractionBeta hπ data j hj a t z).comp (algebraMap R B)).toAlgebra

/-- The actual input divided coordinates as an algebra presentation. -/
def successorFractionBetaAlg : B →ₐ[R] (U).X i :=
  { successorFractionBeta hπ data j hj a t z with commutes' := fun _ => rfl }

/-- The algebra presentation retains its actual flat fraction-input factorization. -/
theorem successorFractionBetaAlg_factor :
    (successorFractionBetaAlg hπ data j hj a t z).toRingHom =
      (successorFractionHom hπ data j hj a t z).comp (algebraMap B C) := rfl

/-- The algebra presentation retains the actual parameter's coefficient morphism. -/
theorem successorFractionAlg_parameter :
    successorDividedParameter hπ data j hj a i ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom
        ((successorFractionBetaAlg hπ data j hj a t z).comp q).toRingHom) ≫
          integralCurveChart W 2) ≫ integralCurveStructure W :=
  successorFractionParameter_structure hπ data j hj a t z

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
include ha in
/-- Both actual divided coordinate maps agree on the original coefficient ring. -/
theorem successorFraction_coefficients :
    (successorDividedAlpha hπ data j hj a i).comp (algebraMap R B) =
      (successorFractionBeta hπ data j hj a t z).comp (algebraMap R B) := by
  have he := congrArg (fun b => b ≫ integralCurveStructure W)
    (successorFractionAlpha_addition hπ data j hj a t z ha)
  rw [leftSmoothPointAddition_structure, successorFractionParameter_structure,
    successorFractionOriginal_structure, successorFractionOriginal_structure] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

/-- The output divided coordinates preserve that same coefficient algebra. -/
def successorFractionAlphaAlg : B →ₐ[R] (U).X i :=
  { successorDividedAlpha hπ data j hj a i with
    commutes' := fun r => RingHom.congr_fun
      (successorFraction_coefficients hπ data j hj a t z ha) r }

/-- The algebra presentations retain the original action on the whole actual input. -/
theorem successorFractionAlg_addition :
    Spec.map (CommRingCat.ofHom
        ((successorFractionAlphaAlg hπ data j hj a t z ha).comp q).toRingHom) ≫
          integralCurveChart W 2 =
      leftSmoothPointAddition W (successorDividedParameter hπ data j hj a i)
        (Spec.map (CommRingCat.ofHom
          ((successorFractionBetaAlg hπ data j hj a t z).comp q).toRingHom) ≫
            integralCurveChart W 2) (successorFractionAlg_parameter hπ data j hj a t z) :=
  successorFractionAlpha_addition hπ data j hj a t z ha

end FLT.Mazur.WeierstrassDividedDepth
