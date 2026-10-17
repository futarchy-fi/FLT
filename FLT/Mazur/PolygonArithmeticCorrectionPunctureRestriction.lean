/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCorrectionPunctures
public import FLT.Mazur.PolygonArithmeticTwoBranchRebaseNaturality
public import FLT.Mazur.PolygonSmoothingPunctureNaturality

/-!
# Quotient squares for the actual arithmetic puncture automorphisms

The original whole-node quotient squares force both full puncture squares.
Their inverses therefore follow the same arithmetic restrictions, including
the rebased common terminal smoothing and both branch drifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- Either full puncture of the actual arithmetic correction follows its original quotient. -/
theorem correctionPunctureFactor_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : R[T;T⁻¹]) (b : Bool) :
    (coeffMap (restriction R π m).toRingHom).comp
        (correctionPunctureFactor R π (m + 1) t q b).toAlgHom.toRingHom =
      (correctionPunctureFactor R π m s q b).toAlgHom.toRingHom.comp
        (coeffMap (restriction R π m).toRingHom) :=
  punctureFactor_naturality _ _ _ _ _
    (correctionSmoothing_restriction R π m t s hs q) hs
    (correctionNodeFactor R π (m + 1) t q) (correctionNodeFactor R π m s q) _ _ b
    (correctionNodeFactor_puncture R π (m + 1) t q b)
    (correctionNodeFactor_puncture R π m s q b)
    (correctionNodeFactor_restriction R π m t s hs q)

/-- The full inverse retained puncture correction has the same arithmetic quotient square. -/
theorem correctionPunctureFactor_symm_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : R[T;T⁻¹]) (b : Bool) :
    (coeffMap (restriction R π m).toRingHom).comp
        (correctionPunctureFactor R π (m + 1) t q b).symm.toAlgHom.toRingHom =
      (correctionPunctureFactor R π m s q b).symm.toAlgHom.toRingHom.comp
        (coeffMap (restriction R π m).toRingHom) :=
  LaurentUnitSubstitutionNaturality.symm_naturality _ _ _
    (correctionPunctureFactor_restriction R π m t s hs q b)

/-- Both actual rebased terminal puncture factors follow the complete quotient square. -/
theorem twoBranchCorrectionRebasedPunctureFactor_restriction (m : ℕ)
    (t : Quotient R π (m + 1)) (s : Quotient R π m) (hs : restriction R π m t = s)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    (coeffMap (restriction R π m).toRingHom).comp
        (twoBranchCorrectionRebasedPunctureFactor R π (m + 1) t q b).toAlgHom.toRingHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m s q b).toAlgHom.toRingHom.comp
        (coeffMap (restriction R π m).toRingHom) :=
  punctureFactor_naturality _ _ _ _ _ hs
    (twoBranchCorrectionRebasedSmoothing_restriction R π m t s hs q)
    (twoBranchCorrectionRebasedFactor R π (m + 1) t q)
    (twoBranchCorrectionRebasedFactor R π m s q) _ _ b
    (twoBranchCorrectionRebasedFactor_puncture R π (m + 1) t q b)
    (twoBranchCorrectionRebasedFactor_puncture R π m s q b)
    (twoBranchCorrectionRebasedFactor_restriction R π m t s hs q)

/-- The inverse terminal substitutions also preserve every original adjacent quotient. -/
theorem twoBranchCorrectionRebasedPunctureFactor_symm_restriction (m : ℕ)
    (t : Quotient R π (m + 1)) (s : Quotient R π m) (hs : restriction R π m t = s)
    (q : Bool → R[T;T⁻¹]) (b : Bool) :
    (coeffMap (restriction R π m).toRingHom).comp
        (twoBranchCorrectionRebasedPunctureFactor R π (m + 1) t q b).symm.toAlgHom.toRingHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m s q b).symm.toAlgHom.toRingHom.comp
        (coeffMap (restriction R π m).toRingHom) :=
  LaurentUnitSubstitutionNaturality.symm_naturality _ _ _
    (twoBranchCorrectionRebasedPunctureFactor_restriction R π m t s hs q b)

end FLT.Mazur.PolygonArithmeticStages
