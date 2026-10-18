/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLaurentIdentityRestriction
public import FLT.Mazur.PolygonArithmeticLaurentSystemCorrectionField
public import FLT.Mazur.PolygonArithmeticCorrectionPunctureRestriction
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction

/-!
# Raw simultaneous correction states over all arithmetic orders

A state records the actual three smoothings and the two full edge maps.
Compatibility, annihilation and normalization are separate predicates, proved
for constructed states; no field supplies a corrected atlas or its conclusion.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonScalingNaturality PolygonSmoothing LaurentPolynomial
variable (R : Type*) [CommRing R] (π : R)

/-- The actual node parameters and complete initial and closing residuals. -/
structure State where
  /-- The current initial-node smoothing on each branch. -/
  initial : (m : ℕ) → Bool → Quotient R π m
  /-- The current smoothing of the shared last node on each branch. -/
  last : (m : ℕ) → Bool → Quotient R π m
  /-- The current smoothing of the one common terminal. -/
  terminal : (m : ℕ) → Quotient R π m
  /-- The full initial edge, including its original reciprocal base. -/
  initialEquiv : (m : ℕ) → Bool →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]
  /-- The full closing residual on each branch. -/
  closingEquiv : (m : ℕ) → Bool →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]

variable {R π}

/-- A complete Laurent equivalence system respects the original coefficient quotients. -/
def CompatibleEquiv (E : (m : ℕ) →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]) : Prop :=
  ∀ m, (coeffMap (restriction R π m).toRingHom).comp (E (m + 1)).toRingHom =
    (E m).toRingHom.comp (coeffMap (restriction R π m).toRingHom)

/-- All scalar parameters and both edges retain their full quotient squares. -/
def State.Compatible (S : State R π) : Prop :=
  (∀ m b, restriction R π m (S.initial (m + 1) b) = S.initial m b) ∧
  (∀ m b, restriction R π m (S.last (m + 1) b) = S.last m b) ∧
  (∀ m, restriction R π m (S.terminal (m + 1)) = S.terminal m) ∧
  (∀ b, CompatibleEquiv (fun m ↦ S.initialEquiv m b)) ∧
  (∀ b, CompatibleEquiv (fun m ↦ S.closingEquiv m b))

/-- Every actual smoothing is killed by the top parameter power at its own order. -/
def State.Annihilated (S : State R π) : Prop :=
  (∀ m b, parameter R π m ^ m * S.initial m b = 0) ∧
  (∀ m b, parameter R π m ^ m * S.last m b = 0) ∧
  (∀ m, parameter R π m ^ m * S.terminal m = 0)

variable (B : (m : ℕ) →
  (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])

/-- Normalization keeps the entire original initial base and kills both closing errors. -/
def State.Normalized (S : State R π) (r : ℕ) : Prop :=
  (∀ b, S.initialEquiv r b = B r) ∧ (∀ b, S.closingEquiv r b = AlgEquiv.refl)

/-- Measure the initial edge relative to its full base, and the closing edge directly. -/
def State.error (S : State R π) (closing b : Bool) (m : ℕ) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  if closing then S.closingEquiv m b else (S.initialEquiv m b).trans (B m).symm

/-- Taking the relative error preserves every coefficient square. -/
theorem State.error_compatible (S : State R π) (hS : S.Compatible)
    (hB : CompatibleEquiv B) (closing b : Bool) :
    CompatibleEquiv (S.error B closing b) := by
  intro m
  cases closing
  · apply punctureEquiv_trans_naturality
    · exact hS.2.2.2.1 b m
    · exact LaurentUnitSubstitutionNaturality.symm_naturality _ _ _ (hB m)
  · exact hS.2.2.2.2 b m

/-- Normalization of both full edges makes both measured errors the identity. -/
theorem State.error_normalized (S : State R π) (r : ℕ)
    (hS : S.Normalized B r) (closing b : Bool) :
    S.error B closing b r = AlgEquiv.refl := by
  cases closing
  · change (S.initialEquiv r b).trans (B r).symm = _
    rw [hS.1 b]
    ext z : 1
    exact (B r).symm_apply_apply z
  · exact hS.2 b

/-- Normalization of both full edges descends to every earlier arithmetic quotient. -/
theorem State.normalized_restriction (S : State R π) (hS : S.Compatible)
    (hB : CompatibleEquiv B) {k m : ℕ} (hkm : k ≤ m) (hm : S.Normalized B m) :
    S.Normalized B k := by
  have he (c b : Bool) : (S.error B c b k).toAlgHom = AlgHom.id _ _ :=
    laurentSystem_identity_restriction (fun i ↦ (S.error B c b i).toAlgHom)
      (S.error_compatible B hS hB c b) hkm
      (congrArg AlgEquiv.toAlgHom (S.error_normalized B m hm c b))
  constructor
  · intro b
    ext z : 1
    apply (B k).symm.injective
    have h := DFunLike.congr_fun (he false b) z
    change (B k).symm (S.initialEquiv k b z) = z at h
    exact h.trans ((B k).symm_apply_apply z).symm
  · intro b
    exact AlgEquiv.coe_toAlgHom_injective (he true b)

/-- Select the entire next error from each actual compatible edge. -/
def State.nextField (S : State R π) (hS : S.Compatible) (hB : CompatibleEquiv B)
    (r : ℕ) (hr : S.Normalized B r) (closing b : Bool) :
    (Quotient R π (r + 1))[T;T⁻¹] :=
  laurentSystemNextField (fun m ↦ (S.error B closing b m).toAlgHom)
    (S.error_compatible B hS hB closing b) r
    (congrArg AlgEquiv.toAlgHom (S.error_normalized B r hr closing b))

/-- The selected field represents every coefficient of the next complete error. -/
theorem State.nextField_subst (S : State R π) (hS : S.Compatible)
    (hB : CompatibleEquiv B) (r : ℕ) (hr : S.Normalized B r) (closing b : Bool) :
    (S.error B closing b (r + 1)).toAlgHom =
      LaurentSquareZeroAutomorphism.subst (parameter R π (r + 1) ^ (r + 1))
        (nextCorrectionParameter_square R π r) (S.nextField B hS hB r hr closing b) :=
  laurentSystemNextField_subst (fun m ↦ (S.error B closing b m).toAlgHom)
    (S.error_compatible B hS hB closing b) r
    (congrArg AlgEquiv.toAlgHom (S.error_normalized B r hr closing b))

/-- One fixed integral lift for each of the simultaneous measured fields. -/
def State.nextIntegralField (S : State R π) (hS : S.Compatible)
    (hB : CompatibleEquiv B) (r : ℕ) (hr : S.Normalized B r) (closing b : Bool) : R[T;T⁻¹] :=
  integralCorrectionLift R π (r + 1) (S.nextField B hS hB r hr closing b)

/-- The integral lifts retain the full measured fields at their defining layer. -/
theorem State.nextIntegralField_spec (S : State R π) (hS : S.Compatible)
    (hB : CompatibleEquiv B) (r : ℕ) (hr : S.Normalized B r) (closing b : Bool) :
    correctionField R π (r + 1) (S.nextIntegralField B hS hB r hr closing b) =
      S.nextField B hS hB r hr closing b := integralCorrectionLift_spec R π _ _

end FLT.Mazur.PolygonArithmeticSimultaneous
