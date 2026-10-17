/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureCalculus
public import FLT.Mazur.PolygonArithmeticTwoBranchRebase

/-!
# Exact puncture substitutions of the arithmetic correction lifts

Both complete substitutions are composed in the order of the actual node
factors. Reflection exchanges the branches. Rebasing inserts only the proved
equal-parameter identification and retains both scalar smoothing drifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- The actual full Laurent automorphism of either puncture of one arithmetic correction. -/
def correctionPunctureFactor (m : ℕ) (t : Quotient R π m) (q : R[T;T⁻¹]) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  nilpotentShearPunctureEquiv t (parameter R π m) ⟨m + 1, parameter_pow R π m⟩
    (algebraMap R (Quotient R π m) (q.coeff 1))
    (LaurentBoundaryCorrectionSplit.boundaryLift t (correctionField R π m q)) b

/-- Every Laurent function of each actual node lift follows the corresponding substitution. -/
theorem correctionNodeFactor_puncture (m : ℕ) (t : Quotient R π m)
    (q : R[T;T⁻¹]) (b : Bool) :
    (punctureLaurentMap t b).comp (correctionNodeFactor R π m t q).toAlgHom =
      (correctionPunctureFactor R π m t q b).toAlgHom.comp
        (punctureLaurentMap (correctionSmoothing R π m t q) b) := by
  rw [correctionNodeFactor_def]
  exact nilpotentShear_puncture _ _ _ _ _ _

/-- The reflected arithmetic correction uses the full opposite puncture substitution. -/
theorem reflectedCorrectionNodeFactor_puncture (m : ℕ) (t : Quotient R π m)
    (q : R[T;T⁻¹]) (b : Bool) :
    (punctureLaurentMap t b).comp (reflectedCorrectionNodeFactor R π m t q).toAlgHom =
      (correctionPunctureFactor R π m t q (!b)).toAlgHom.comp
        (punctureLaurentMap (correctionSmoothing R π m t q) b) := by
  rw [reflectedCorrectionNodeFactor_def]
  exact punctureFactor_reflect _ _ _ _ (correctionNodeFactor_puncture R π m t q) b

/-- Compose both full puncture automorphisms in the actual terminal correction order. -/
def twoBranchCorrectionPunctureFactor (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (correctionPunctureFactor R π m (correctionSmoothing R π m t (q false)) (q true) b).trans
    (correctionPunctureFactor R π m t (q false) (!b))

/-- The whole two-branch correction has precisely the composed full puncture substitutions. -/
theorem twoBranchCorrectionNodeFactor_puncture (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    (punctureLaurentMap t b).comp (twoBranchCorrectionNodeFactor R π m t q).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m t q b).toAlgHom.comp
        (punctureLaurentMap (twoBranchCorrectionSmoothing R π m t q) b) := by
  rw [twoBranchCorrectionNodeFactor_def]
  exact punctureFactor_comp _ _ _ _ _ _ _ b
    (reflectedCorrectionNodeFactor_puncture R π m t (q false) b)
    (correctionNodeFactor_puncture R π m _ (q true) b)

/-- The rebased terminal substitution retains the same two full factors on its rebased smoothing. -/
def twoBranchCorrectionRebasedPunctureFactor (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  twoBranchCorrectionPunctureFactor R π m (twoBranchCorrectionRebasedSmoothing R π m t q) q b

/-- The positive rebased whole-node factor has its exact full puncture factorization. -/
theorem twoBranchCorrectionRebasedFactor_puncture (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    (punctureLaurentMap (twoBranchCorrectionRebasedSmoothing R π m t q) b).comp
        (twoBranchCorrectionRebasedFactor R π m t q).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m t q b).toAlgHom.comp
        (punctureLaurentMap t b) := by
  rw [twoBranchCorrectionRebasedFactor_def]
  change (punctureLaurentMap _ b).comp
    ((twoBranchCorrectionNodeFactor R π m _ q).toAlgHom.comp
      (nodeParameterEquiv _ _ _).toAlgHom) = _
  rw [← AlgHom.comp_assoc, twoBranchCorrectionNodeFactor_puncture,
    AlgHom.comp_assoc, punctureLaurentMap_parameter]
  rfl

/-- The geometric correction's inverse ring factor uses the entire inverse substitution. -/
theorem twoBranchCorrectionRebasedFactor_symm_puncture (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    (punctureLaurentMap t b).comp (twoBranchCorrectionRebasedFactor R π m t q).symm.toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m t q b).symm.toAlgHom.comp
        (punctureLaurentMap (twoBranchCorrectionRebasedSmoothing R π m t q) b) :=
  punctureFactor_symm _ _ _ _ b (twoBranchCorrectionRebasedFactor_puncture R π m t q b)

end FLT.Mazur.PolygonArithmeticStages
