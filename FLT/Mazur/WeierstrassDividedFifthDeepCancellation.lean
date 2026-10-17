/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepNodes
public import FLT.Mazur.WeierstrassDividedFifthPairedCancellation
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Simultaneous fifth cancellation on the two outer retained edges

The outer factor participates in both residuals. All three nodes use the
complete fourth smoothings, and all residual maps retain every coefficient.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthOuterPrecedingEquiv
  arithmeticFourthOuterIncomingEquiv arithmeticFifthPairedIntegralField
  arithmeticFifthDeepInput arithmeticFifthResidualField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "s" => arithmeticFifthDeepInput hπ data H j hj u hu
local notation "P" => fun v ↦ arithmeticFifthPairedIntegralField hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v)
local notation "C" => fun v m b ↦ arithmeticFifthPairedEdgeEquiv hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v) m (s v m b) b

/-- The full preceding residual uses the outer node's actual outgoing puncture. -/
def arithmeticFifthDeepPrecedingEquiv (m : ℕ) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  ((C .predecessor m b).trans
      (arithmeticFourthOuterPrecedingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s .outer m b) (P .outer b) true).symm

/-- The full outer incoming residual uses the same outer node's other puncture. -/
def arithmeticFifthDeepOuterIncomingEquiv (m : ℕ) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  ((C .outer m b).trans
      (arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s .farther m b) (P .farther b) true).symm

/-- The predecessor and outer factors cancel their complete common fifth error. -/
theorem arithmeticFifthDeepPrecedingEquiv_fifth (b : Bool) :
    arithmeticFifthDeepPrecedingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact arithmeticFifthPairedResidual_fifth hπ data H j hj u hu
    .incoming .outerPreceding .outerIncoming (s .predecessor 5 b) (s .outer 5 b)
    (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu .predecessor 5 b)
    (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu .outer 5 b) b

/-- That same outer factor simultaneously cancels its farther incoming edge. -/
theorem arithmeticFifthDeepOuterIncomingEquiv_fifth (b : Bool) :
    arithmeticFifthDeepOuterIncomingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact arithmeticFifthPairedResidual_fifth hπ data H j hj u hu
    .outerPreceding .outerIncoming .fartherIncoming (s .outer 5 b) (s .farther 5 b)
    (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu .outer 5 b)
    (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu .farther 5 b) b

end FLT.Mazur.WeierstrassDividedDepth
