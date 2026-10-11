/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionCoordinates

/-!
# Coefficient-linear coordinates on the actual first-successor atlas

Both divided coordinate maps preserve the same original coefficients.
The atlas therefore has a canonical coefficient algebra, and its ring
presentations are genuine algebra maps ready for the normalized lift.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "C" => BlowupFractionChart.chart I f
local notation "c" => finiteSuccessiveFractionChart hπ data 0 hn f hf
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstFractionCover hπ data hn f hf


/-- Composing a divided presentation with the original cubic retains its coefficient map. -/
theorem firstFractionOriginal_structure (i : (U).I₀) (γ : B →+* (U).X i) :
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

/-- The actual input and output divided coordinates preserve identical coefficients. -/
theorem firstFraction_coefficients (i : (U).I₀) :
    (firstFractionAlpha hπ data hn f hf i).comp (algebraMap R B) =
      (firstFractionBeta hπ data hn f hf i).comp (algebraMap R B) := by
  have he := congrArg (fun t => t ≫ integralCurveStructure W)
    (firstFractionAlpha_original_addition hπ data hn f hf i)
  rw [leftSmoothPointAddition_structure,
    firstFractionParameter_original_structure,
    firstFractionOriginal_structure, firstFractionOriginal_structure] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

/-- The coefficient algebra carried by every actual affine presentation. -/
instance firstFractionAlgebra (i : (U).I₀) : Algebra R ((U).X i) :=
  ((firstFractionBeta hπ data hn f hf i).comp (algebraMap R B)).toAlgebra

/-- The input divided coordinates as an algebra map over the original coefficients. -/
def firstFractionBetaAlg (i : (U).I₀) : B →ₐ[R] (U).X i :=
  { firstFractionBeta hπ data hn f hf i with commutes' := fun _ => rfl }

/-- The output divided coordinates as an algebra map over the same original coefficients. -/
def firstFractionAlphaAlg (i : (U).I₀) : B →ₐ[R] (U).X i :=
  { firstFractionAlpha hπ data hn f hf i with
    commutes' := fun r => RingHom.congr_fun (firstFraction_coefficients hπ data hn f hf i) r }

/-- The algebra presentation retains the actual flat fraction-input factorization. -/
theorem firstFractionBetaAlg_factor (i : (U).I₀) :
    (firstFractionBetaAlg hπ data hn f hf i).toRingHom =
      (firstFractionHom hπ data hn f hf i).comp (algebraMap B C) := rfl

/-- The actual algebra presentations identify the original parameter's base morphism. -/
theorem firstFractionAlg_parameter (i : (U).I₀) :
    firstFractionParameter hπ data hn f hf i ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom
        ((firstFractionBetaAlg hπ data hn f hf i).comp q).toRingHom) ≫
          integralCurveChart W 2) ≫ integralCurveStructure W :=
  firstFractionParameter_original_structure hπ data hn f hf i

/-- The actual algebra presentations identify the original action, including the whole input. -/
theorem firstFractionAlg_addition (i : (U).I₀) :
    Spec.map (CommRingCat.ofHom
        ((firstFractionAlphaAlg hπ data hn f hf i).comp q).toRingHom) ≫
          integralCurveChart W 2 =
      leftSmoothPointAddition W (firstFractionParameter hπ data hn f hf i)
        (Spec.map (CommRingCat.ofHom
          ((firstFractionBetaAlg hπ data hn f hf i).comp q).toRingHom) ≫
            integralCurveChart W 2) (firstFractionAlg_parameter hπ data hn f hf i) :=
  firstFractionAlpha_original_addition hπ data hn f hf i

end FLT.Mazur.WeierstrassDividedDepth
