/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPairedCharacterBases

/-!
# Character projectors as normalized rank-one maps

The generator and its normalized Cartier dual are constructed from the
proved character bases. Their rank-one map is the actual projector.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing CharacterProjector

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

/-- The normalized dual generator supplies the coefficient of the character projection. -/
theorem FF.character_projector_rankOne (χ : Fˣ →* Rˣ) (a : X.augmentation) :
    (projector (X.augmentationRepresentation lift h1 hmul) χ a : X.CoordinateRing) =
      (show HopfAlgebra.CartierDual R X.CoordinateRing from
        X.dualCharacterGenerator lift h1 hmul p hdim hlift χ) a •
        X.characterGenerator lift h1 hmul p hdim hlift χ := by
  let b := X.characterBasis lift h1 hmul p hdim hlift χ
  let v : X.integralCharacter lift h1 hmul χ :=
    ⟨projector (X.augmentationRepresentation lift h1 hmul) χ a, projector_mem _ _ _⟩
  let φ := X.cartierCharacterTranspose lift h1 hmul χ
    (X.dualCharacterBasis lift h1 hmul p hdim hlift χ ())
  have hv : b.repr v () • b () = v := by simpa using b.sum_repr v
  have hp : φ.val (projector (X.augmentationRepresentation lift h1 hmul) χ a) =
      φ.val a := transpose_pair_projector _ χ φ a
  have hc : b.repr v () = φ.val a := by
    rw [← hp]
    change b.repr v () = φ.val v.val
    conv_rhs => rw [← hv]
    change b.repr v () = φ.val (b.repr v () • (b ()).val)
    rw [φ.val.map_smul]
    change b.repr v () = b.repr v () * _
    rw [show φ.val (b ()).val = 1 from
      X.characterGenerator_pairing lift h1 hmul p hdim hlift χ, mul_one]
  change (v.val : X.CoordinateRing) = φ.val a • (b ()).val.val
  rw [← hc]
  exact (congrArg (fun z : X.integralCharacter lift h1 hmul χ ↦
    (z.val : X.CoordinateRing)) hv).symm

/-- Extend the augmentation character projector to coordinates by removing the counit. -/
def FF.coordinateCharacterProjector (χ : Fˣ →* Rˣ) :
    X.CoordinateRing →ₗ[R] X.CoordinateRing :=
  X.augmentation.subtype.comp
    ((projector (X.augmentationRepresentation lift h1 hmul) χ).comp X.augmentationProjection)

/-- On all coordinates the extended projector is the normalized rank-one map. -/
theorem FF.coordinateCharacterProjector_rankOne (χ : Fˣ →* Rˣ) :
    X.coordinateCharacterProjector lift h1 hmul χ =
      (show HopfAlgebra.CartierDual R X.CoordinateRing from
        X.dualCharacterGenerator lift h1 hmul p hdim hlift χ).ofConv.smulRight
        (X.characterGenerator lift h1 hmul p hdim hlift χ) := by
  ext a
  change (projector (X.augmentationRepresentation lift h1 hmul) χ
    (X.augmentationProjection a) : X.CoordinateRing) = _
  rw [X.character_projector_rankOne lift h1 hmul p hdim hlift]
  congr 1
  let φ : HopfAlgebra.CartierDual R X.CoordinateRing :=
    X.dualCharacterGenerator lift h1 hmul p hdim hlift χ
  have hφ : φ.ofConv 1 = 0 :=
    (X.dualCharacterBasis lift h1 hmul p hdim hlift χ ()).val.property
  change φ.ofConv (a - algebraMap R X.CoordinateRing (Coalgebra.counit a)) = φ.ofConv a
  rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, hφ, smul_zero, sub_zero]

end ThreeAdicPlan
