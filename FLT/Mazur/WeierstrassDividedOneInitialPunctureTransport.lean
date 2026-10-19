/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInitialTotalTransport

/-!
# Both punctures of the full depth-one initial comparison

The explicit Laurent substitutions retain all four corrections and both
boundary orientations of each original initial node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticThirdInitialIso arithmeticFourthInitialIso
  arithmeticFifthInitialIso arithmeticOneFiniteInitialIso
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m


/-- Both boundary substitutions include every correction from the original initial node. -/
def arithmeticOneFiniteInitialTotalPunctureIso (k : ℕ) (b a : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  punctureSpecIso (correctionPunctureFactor R π m τ
    (arithmeticThirdEarlierIntegralField hπ data H 1 hj u hu b) a) ≪≫
  punctureSpecIso (correctionPunctureFactor R π m
    (arithmeticThirdEarlierSmoothing hπ data H 1 hj u hu m b)
    (arithmeticFourthInitialIntegralField hπ data H 1 hj u hu b) a) ≪≫
  punctureSpecIso (correctionPunctureFactor R π m
    (arithmeticFourthInitialSmoothing hπ data H 1 hj u hu m b)
    (arithmeticFifthInitialIntegralField hπ data H 1 hj u hu b) a) ≪≫
  punctureSpecIso (arithmeticOneFiniteInitialPunctureEquiv hπ data H hj u hu k m b a)

/-- The full original node comparison commutes on both entire Laurent boundaries. -/
@[reassoc] theorem arithmeticOneFiniteInitialTotalNodeIso_puncture (k : ℕ) (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticOneFiniteInitialTotalNodeIso hπ data H m hj u hu k b).hom =
      (arithmeticOneFiniteInitialTotalPunctureIso hπ data H m hj u hu k b a).hom ≫
        punctureOpen ((arithmeticOneFiniteState hπ data H hj u hu k).initial m b) a := by
  simp only [arithmeticOneFiniteInitialTotalNodeIso,
    arithmeticOneFiniteInitialTotalPunctureIso, Iso.trans_hom, Category.assoc,
    arithmeticThirdEarlierIso_puncture_assoc, arithmeticFourthInitialNodeIso_puncture_assoc,
    arithmeticFifthInitialNodeIso_puncture_assoc, arithmeticOneFiniteInitialNodeIso_puncture]

/-- The actual diagonal node retains both complete original boundary substitutions. -/
@[reassoc] theorem arithmeticOneDiagonalInitialTotalNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu b).hom =
      (arithmeticOneFiniteInitialTotalPunctureIso hπ data H m hj u hu m b a).hom ≫
        punctureOpen ((arithmeticOneDiagonalState hπ data H hj u hu).initial m b) a :=
  arithmeticOneFiniteInitialTotalNodeIso_puncture hπ data H m hj u hu m b a

end FLT.Mazur.WeierstrassDividedDepth
