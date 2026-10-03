/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierCharacterDuality
public import FLT.GroupScheme.RaynaudCharacterPowers

/-!
# Paired character bases and dual power coefficients

The original character basis is derived from the model. The perfect Cartier
pairing constructs its dual basis on the actual dual model; no independently
chosen dual presentation or eigenspace basis is assumed.
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

/-- The dual basis of the proved original character basis, in the actual dual model. -/
def FF.dualCharacterBasis (χ : Fˣ →* Rˣ) :
    Module.Basis Unit R (eigenspace (X.dualAugmentationRepresentation lift h1 hmul) χ) :=
  (X.characterBasis lift h1 hmul p hdim hlift χ).dualBasis.map
    (X.cartierCharacterDuality lift h1 hmul χ).symm

/-- The paired dual generator as an actual dual coordinate. -/
def FF.dualCharacterGenerator (χ : Fˣ →* Rˣ) : X.cartierDual.CoordinateRing :=
  (X.dualCharacterBasis lift h1 hmul p hdim hlift χ ()).val

/-- The two derived generators are normalized to have Cartier pairing one. -/
theorem FF.characterGenerator_pairing (χ : Fˣ →* Rˣ) :
    (show HopfAlgebra.CartierDual R X.CoordinateRing from
      X.dualCharacterGenerator lift h1 hmul p hdim hlift χ)
      (X.characterGenerator lift h1 hmul p hdim hlift χ) = 1 := by
  change X.cartierCharacterDuality lift h1 hmul χ
    (X.dualCharacterBasis lift h1 hmul p hdim hlift χ ())
    (X.characterBasis lift h1 hmul p hdim hlift χ ()) = 1
  simp [FF.dualCharacterBasis]

/-- A positive power of the paired dual generator has an actual integral coefficient. -/
theorem FF.dual_character_power_relation (χ : Fˣ →* Rˣ) (n : ℕ) (hn : n ≠ 0) :
    ∃ c : R, X.dualCharacterGenerator lift h1 hmul p hdim hlift χ ^ n =
      c • X.dualCharacterGenerator lift h1 hmul p hdim hlift (χ ^ n) := by
  let b := X.dualCharacterBasis lift h1 hmul p hdim hlift (χ ^ n)
  let a := X.cartierDual.integralCharacterPow (fun u ↦ (lift u).cartierDual)
    (X.dualScalar_one lift h1) (X.dualScalar_mul lift hmul) χ
    (X.dualCharacterBasis lift h1 hmul p hdim hlift χ ()) n hn
  refine ⟨b.repr a (), ?_⟩
  have h : b.repr a () • b () = a := by simpa using b.sum_repr a
  exact (congrArg (fun z : eigenspace (X.dualAugmentationRepresentation lift h1 hmul) (χ ^ n) ↦
    (z.val : X.cartierDual.CoordinateRing)) h).symm

end ThreeAdicPlan
