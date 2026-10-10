/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXBaseChangeGenerators
public import FLT.Mazur.WeierstrassModificationXResidueContraction

/-!
# Original tensor generators at the residue comparison boundary

An opaque package seals the existing coefficient equivalence together with a
proof of equality. Factoring the tensor equivalence through this package avoids
reducing nested coefficient casts while evaluating the original tensor generators.
The final formulas use the original unsealed maps. Their further identification
with the named normal-form generators is a separate coefficient-cast calculation.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)

local notation "K" => ResidueField R
local notation "W'" => W.map (algebraMap R K)
local notation "c" => algebraMap R K b6

/-- An opaque package retains the original equivalence together with its equality proof. -/
opaque residueCoordinateSeal :
    {e : ExtendedCoordinate W (π ^ k) b3 b4 b6 K ≃ₐ[K]
      FiberCoordinate (residue R W.a₁) (residue R b6) //
        e = residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4} :=
  ⟨residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4, rfl⟩

/-- Seal the original residue comparison to prevent reduction of its nested casts. -/
def residueCoordinateSealedEquiv :
    ExtendedCoordinate W (π ^ k) b3 b4 b6 K ≃ₐ[K]
      FiberCoordinate (residue R W.a₁) (residue R b6) :=
  (residueCoordinateSeal D k hk0 hk b3 b4 b6 h3 h4).val

/-- The sealed comparison is the original equivalence, not a replacement construction. -/
theorem residueCoordinateSealedEquiv_def : residueCoordinateSealedEquiv D k hk0 hk b3 b4 b6 h3 h4 =
    residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4 :=
  (residueCoordinateSeal D k hk0 hk b3 b4 b6 h3 h4).property

/-- Unfold the tensor comparison at the equivalence level before evaluating generators. -/
theorem residueFiberEquiv_eq_trans : residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 =
    (baseChangeEquiv W (π ^ k) b3 b4 b6 K).trans
      (residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4) := rfl

/-- The actual tensor equivalence factors through the sealed original comparison. -/
theorem residueFiberEquiv_eq_sealed : residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 =
    (baseChangeEquiv W (π ^ k) b3 b4 b6 K).trans
      (residueCoordinateSealedEquiv D k hk0 hk b3 b4 b6 h3 h4) := by
  rw [residueFiberEquiv_eq_trans, residueCoordinateSealedEquiv_def]

/-- The original incidence tensor maps to the sealed comparison of its specialized generator. -/
theorem residueFiberEquiv_t_sealed :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      ((1 : K) ⊗ₜ[R] t W (π ^ k) b3 b4 b6) =
    residueCoordinateSealedEquiv D k hk0 hk b3 b4 b6 h3 h4
      (t W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) := by
  rw [residueFiberEquiv_eq_sealed, AlgEquiv.trans_apply, baseChangeEquiv_t]
/-- The original slope tensor maps to the sealed comparison of its specialized generator. -/
theorem residueFiberEquiv_v_sealed :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      ((1 : K) ⊗ₜ[R] v W (π ^ k) b3 b4 b6) =
    residueCoordinateSealedEquiv D k hk0 hk b3 b4 b6 h3 h4
      (v W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) := by
  rw [residueFiberEquiv_eq_sealed, AlgEquiv.trans_apply, baseChangeEquiv_v]
/-- The original incidence tensor reduces to the original residue coefficient comparison. -/
theorem residueFiberEquiv_t_coordinate :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      ((1 : K) ⊗ₜ[R] t W (π ^ k) b3 b4 b6) =
    residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
      (t W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) := by
  rw [← residueCoordinateSealedEquiv_def, residueFiberEquiv_t_sealed]

/-- The original slope tensor reduces to the original residue coefficient comparison. -/
theorem residueFiberEquiv_v_coordinate :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      ((1 : K) ⊗ₜ[R] v W (π ^ k) b3 b4 b6) =
    residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
      (v W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) := by
  rw [← residueCoordinateSealedEquiv_def, residueFiberEquiv_v_sealed]

/-- The original chart incidence map has the same remaining coefficient comparison. -/
theorem residueNormalMap_t_coordinate :
    residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 (t W (π ^ k) b3 b4 b6) =
      residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
        (t W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) := by
  rw [residueNormalMap_apply, residueFiberEquiv_t_coordinate]

/-- The original chart slope map has the same remaining coefficient comparison. -/
theorem residueNormalMap_v_coordinate :
    residueNormalMap D k hk0 hk b3 b4 b6 h3 h4 (v W (π ^ k) b3 b4 b6) =
      residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
        (v W' (algebraMap R K (π ^ k)) (algebraMap R K b3) (algebraMap R K b4) c) := by
  rw [residueNormalMap_apply, residueFiberEquiv_v_coordinate]

end FLT.Mazur.WeierstrassModificationX
