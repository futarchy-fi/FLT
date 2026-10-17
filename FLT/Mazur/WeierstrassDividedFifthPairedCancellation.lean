/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthPairedNodes
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Cancellation between two full fifth paired node factors

One node's reciprocal incoming puncture and its neighbor's outgoing puncture
cancel the full common residual. Their other incident fields remain arbitrary.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "P" => arithmeticFifthPairedIntegralField hπ data H j hj u hu
local notation "E" => arithmeticFourthJointTransition hπ data H j hj u hu

/-- The incoming puncture in the original reciprocal retained-edge coordinate. -/
def arithmeticFifthPairedEdgeEquiv (out inc : FourthResidualEdge) (m : ℕ)
    (s : Quotient R π m) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m s (P out inc b) false)).trans invert

/-- The full residual includes both actual node substitutions and the complete old edge. -/
def arithmeticFifthPairedResidual (out edge inc : FourthResidualEdge) (m : ℕ)
    (s t : Quotient R π m) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  (twoBranchCorrectionPunctureFactor R π m t (P edge inc b) true).symm.toAlgHom.comp
    ((E edge b m).comp
      (arithmeticFifthPairedEdgeEquiv hπ data H j hj u hu out edge m s b).toAlgHom)

/-- The complementary full incoming factor leaves exactly the neighbor's positive factor. -/
theorem arithmeticFifthPaired_factorization (out edge inc : FourthResidualEdge)
    (s t : Quotient R π 5) (hs : parameter R π 5 ^ 5 * s = 0)
    (ht : parameter R π 5 ^ 5 * t = 0) (b : Bool) :
    (E edge b 5).comp
        (arithmeticFifthPairedEdgeEquiv hπ data H j hj u hu out edge 5 s b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π 5 t (P edge inc b) true).toAlgHom := by
  rw [arithmeticFifthPairedEdgeEquiv,
    arithmeticFifthPairedPuncture_fifth hπ data H j hj u hu out edge s hs,
    arithmeticFifthPairedPuncture_fifth hπ data H j hj u hu edge inc t ht,
    arithmeticFifthPairedField_incoming, arithmeticFifthPairedField_outgoing]
  change (E edge b 5).comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [arithmeticFifthResidualField_subst, LaurentSquareZeroAutomorphism.subst_reciprocal,
    reciprocalField_neg, reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFifthResidualField hπ data H j hj u hu edge b)
  linear_combination -hp

/-- The whole common residual is identity, regardless of the two other incident fields. -/
theorem arithmeticFifthPairedResidual_fifth (out edge inc : FourthResidualEdge)
    (s t : Quotient R π 5) (hs : parameter R π 5 ^ 5 * s = 0)
    (ht : parameter R π 5 ^ 5 * t = 0) (b : Bool) :
    arithmeticFifthPairedResidual hπ data H j hj u hu out edge inc 5 s t b =
      AlgHom.id (Quotient R π 5) _ := by
  unfold arithmeticFifthPairedResidual
  rw [arithmeticFifthPaired_factorization hπ data H j hj u hu out edge inc s t hs ht]
  apply AlgHom.ext
  intro z
  exact (twoBranchCorrectionPunctureFactor R π 5 t (P edge inc b) true).symm_apply_apply z

end FLT.Mazur.WeierstrassDividedDepth
