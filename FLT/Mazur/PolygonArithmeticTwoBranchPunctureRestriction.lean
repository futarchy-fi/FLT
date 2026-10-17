/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCorrectionPunctureRestriction
public import FLT.Mazur.PolygonSmoothingPunctureSpecNaturality

/-!
# Quotient squares for the two-sided arithmetic puncture substitution

Both successive node corrections retain their actual input smoothings.
Their composed full puncture and its inverse follow the same quotient map.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (t : Quotient R π (m + 1)) (s : Quotient R π m) (hs : restriction R π m t = s)
  (q : Bool → R[T;T⁻¹]) (b : Bool)
local notation "f" => AlgHom.toRingHom (restriction R π m)

include hs

/-- Both full arithmetic punctures preserve the original adjacent coefficient square. -/
theorem twoBranchCorrectionPunctureFactor_restriction :
    (coeffMap f).comp (twoBranchCorrectionPunctureFactor R π (m + 1) t q b).toRingHom =
      (twoBranchCorrectionPunctureFactor R π m s q b).toRingHom.comp (coeffMap f) := by
  unfold twoBranchCorrectionPunctureFactor
  apply punctureEquiv_trans_naturality
  · exact correctionPunctureFactor_restriction R π m _ _
      (correctionSmoothing_restriction R π m t s hs _) _ b
  · exact correctionPunctureFactor_restriction R π m t s hs _ (!b)

/-- Inversion keeps the exact full coefficient square. -/
theorem twoBranchCorrectionPunctureFactor_symm_restriction :
    (coeffMap f).comp (twoBranchCorrectionPunctureFactor R π (m + 1) t q b).symm.toRingHom =
      (twoBranchCorrectionPunctureFactor R π m s q b).symm.toRingHom.comp (coeffMap f) :=
  symm_naturality f _ _ (twoBranchCorrectionPunctureFactor_restriction R π m t s hs q b)

end FLT.Mazur.PolygonArithmeticStages
