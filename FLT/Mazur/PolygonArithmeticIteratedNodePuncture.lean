/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticIteratedNodeRestriction
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction

/-!
# Both punctures of an iterated full node correction

The same finite composite of whole-node factors induces both boundary maps.
Their exact Laurent substitutions retain every arithmetic quotient square.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (t : Quotient R π m) (q : ℕ → Bool → R[T;T⁻¹])

/-- The full puncture substitution induced by the finite sequence on the whole node. -/
def iteratedCorrectionPunctureFactor (b : Bool) : ℕ →
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹]
  | 0 => AlgEquiv.refl
  | k + 1 => (twoBranchCorrectionPunctureFactor R π m
      (iteratedCorrectionSmoothing R π m t q k) (q k) b).trans
        (iteratedCorrectionPunctureFactor b k)

/-- Both boundary maps are induced by the same full recursive node equivalence. -/
theorem iteratedCorrectionNodeFactor_puncture (b : Bool) (k : ℕ) :
    (punctureLaurentMap t b).comp
        (iteratedCorrectionNodeFactor R π m t q k).toAlgHom =
      (iteratedCorrectionPunctureFactor R π m t q b k).toAlgHom.comp
        (punctureLaurentMap (iteratedCorrectionSmoothing R π m t q k) b) := by
  induction k with
  | zero =>
    apply AlgHom.ext
    intro x
    exact congrArg (punctureLaurentMap t b)
      (DFunLike.congr_fun (iteratedCorrectionNodeFactor_zero R π m t q) x)
  | succ k ih =>
    rw [iteratedCorrectionNodeFactor_succ]
    change (punctureLaurentMap t b).comp
      ((iteratedCorrectionNodeFactor R π m t q k).toAlgHom.comp
        (twoBranchCorrectionNodeFactor R π m
          (iteratedCorrectionSmoothing R π m t q k) (q k)).toAlgHom) =
      ((iteratedCorrectionPunctureFactor R π m t q b k).toAlgHom.comp
        (twoBranchCorrectionPunctureFactor R π m
          (iteratedCorrectionSmoothing R π m t q k) (q k) b).toAlgHom).comp _
    rw [← AlgHom.comp_assoc, ih, AlgHom.comp_assoc,
      twoBranchCorrectionNodeFactor_puncture, ← AlgHom.comp_assoc]
    rfl

omit t in
/-- Every full iterated boundary map preserves the original adjacent quotient. -/
theorem iteratedCorrectionPunctureFactor_restriction
    (t : Quotient R π (m + 1)) (s : Quotient R π m)
    (hs : restriction R π m t = s) (b : Bool) (k : ℕ) :
    (coeffMap (restriction R π m).toRingHom).comp
        (iteratedCorrectionPunctureFactor R π (m + 1) t q b k).toRingHom =
      (iteratedCorrectionPunctureFactor R π m s q b k).toRingHom.comp
        (coeffMap (restriction R π m).toRingHom) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (iteratedCorrectionSmoothing_restriction R π m t s hs q k) (q k) b
    · exact ih

end FLT.Mazur.PolygonArithmeticStages
