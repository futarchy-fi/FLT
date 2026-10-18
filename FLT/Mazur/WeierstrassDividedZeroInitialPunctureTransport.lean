/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatio

/-!
# Both full punctures of the accumulated initial node comparison

The six node factors induce explicit Laurent isomorphisms on both boundaries.
No coefficient reduction or fixed-smoothing identification is used.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFirstInitialIso arithmeticZeroSecondInitialIso arithmeticZeroThirdInitialIso
  arithmeticZeroFourthInitialIso arithmeticZeroFifthInitialIso arithmeticZeroFiniteInitialIso
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
/-- The first accumulated boundary includes every preceding node factor. -/
def arithmeticZeroFirstInitialTotalPunctureIso (b a : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  punctureSpecIso (correctionPunctureFactor R π m τ
    (arithmeticZeroFirstInitialIntegralField hπ data H 0 hj u hu b) a)

/-- Both complete first boundaries commute with their accumulated node map. -/
@[reassoc] theorem arithmeticZeroFirstInitialTotalNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroFirstInitialNodeIso hπ data H m 0 hj u hu b).hom =
      (arithmeticZeroFirstInitialTotalPunctureIso hπ data H m hj u hu b a).hom ≫
        punctureOpen (arithmeticZeroFirstInitialSmoothing hπ data H 0 hj u hu m b) a := by
  exact arithmeticZeroFirstInitialNodeIso_puncture hπ data H m 0 hj u hu b a

/-- The second accumulated boundary includes every preceding node factor. -/
def arithmeticZeroSecondInitialTotalPunctureIso (b a : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  arithmeticZeroFirstInitialTotalPunctureIso hπ data H m hj u hu b a ≪≫
  punctureSpecIso (correctionPunctureFactor R π m
      (arithmeticZeroFirstInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroSecondInitialIntegralField hπ data H 0 hj u hu b) a)

/-- Both complete second boundaries commute with their accumulated node map. -/
@[reassoc] theorem arithmeticZeroSecondInitialTotalNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroSecondInitialTotalNodeIso hπ data H m hj u hu b).hom =
      (arithmeticZeroSecondInitialTotalPunctureIso hπ data H m hj u hu b a).hom ≫
        punctureOpen (arithmeticZeroSecondInitialSmoothing hπ data H 0 hj u hu m b) a := by
  simp only [arithmeticZeroSecondInitialTotalNodeIso,
    arithmeticZeroSecondInitialTotalPunctureIso, Iso.trans_hom, ← Category.assoc,
    arithmeticZeroFirstInitialTotalNodeIso_puncture]
  rw [Category.assoc, arithmeticZeroSecondInitialNodeIso_puncture, ← Category.assoc]

/-- The third accumulated boundary includes every preceding node factor. -/
def arithmeticZeroThirdInitialTotalPunctureIso (b a : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  arithmeticZeroSecondInitialTotalPunctureIso hπ data H m hj u hu b a ≪≫
  punctureSpecIso (correctionPunctureFactor R π m
      (arithmeticZeroSecondInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroThirdInitialIntegralField hπ data H 0 hj u hu b) a)

/-- Both complete third boundaries commute with their accumulated node map. -/
@[reassoc] theorem arithmeticZeroThirdInitialTotalNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroThirdInitialTotalNodeIso hπ data H m hj u hu b).hom =
      (arithmeticZeroThirdInitialTotalPunctureIso hπ data H m hj u hu b a).hom ≫
        punctureOpen (arithmeticZeroThirdInitialSmoothing hπ data H 0 hj u hu m b) a := by
  simp only [arithmeticZeroThirdInitialTotalNodeIso,
    arithmeticZeroThirdInitialTotalPunctureIso, Iso.trans_hom, ← Category.assoc,
    arithmeticZeroSecondInitialTotalNodeIso_puncture]
  rw [Category.assoc, arithmeticZeroThirdInitialNodeIso_puncture, ← Category.assoc]

/-- The fourth accumulated boundary includes every preceding node factor. -/
def arithmeticZeroFourthInitialTotalPunctureIso (b a : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  arithmeticZeroThirdInitialTotalPunctureIso hπ data H m hj u hu b a ≪≫
  punctureSpecIso (correctionPunctureFactor R π m
      (arithmeticZeroThirdInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroFourthInitialIntegralField hπ data H 0 hj u hu b) a)

/-- Both complete fourth boundaries commute with their accumulated node map. -/
@[reassoc] theorem arithmeticZeroFourthInitialTotalNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroFourthInitialTotalNodeIso hπ data H m hj u hu b).hom =
      (arithmeticZeroFourthInitialTotalPunctureIso hπ data H m hj u hu b a).hom ≫
        punctureOpen (arithmeticZeroFourthInitialSmoothing hπ data H 0 hj u hu m b) a := by
  simp only [arithmeticZeroFourthInitialTotalNodeIso,
    arithmeticZeroFourthInitialTotalPunctureIso, Iso.trans_hom, ← Category.assoc,
    arithmeticZeroThirdInitialTotalNodeIso_puncture]
  rw [Category.assoc, arithmeticZeroFourthInitialNodeIso_puncture, ← Category.assoc]

/-- The fifth accumulated boundary includes every preceding node factor. -/
def arithmeticZeroFifthInitialTotalPunctureIso (b a : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  arithmeticZeroFourthInitialTotalPunctureIso hπ data H m hj u hu b a ≪≫
  punctureSpecIso (correctionPunctureFactor R π m
      (arithmeticZeroFourthInitialSmoothing hπ data H 0 hj u hu m b)
    (arithmeticZeroFifthInitialIntegralField hπ data H 0 hj u hu b) a)

/-- Both complete fifth boundaries commute with their accumulated node map. -/
@[reassoc] theorem arithmeticZeroFifthInitialTotalNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroFifthInitialTotalNodeIso hπ data H m hj u hu b).hom =
      (arithmeticZeroFifthInitialTotalPunctureIso hπ data H m hj u hu b a).hom ≫
        punctureOpen (arithmeticZeroFifthInitialSmoothing hπ data H 0 hj u hu m b) a := by
  simp only [arithmeticZeroFifthInitialTotalNodeIso,
    arithmeticZeroFifthInitialTotalPunctureIso, Iso.trans_hom, ← Category.assoc,
    arithmeticZeroFourthInitialTotalNodeIso_puncture]
  rw [Category.assoc, arithmeticZeroFifthInitialNodeIso_puncture, ← Category.assoc]

/-- The finite full boundary composes the first five and the actual finite factor. -/
def arithmeticZeroFiniteInitialTotalPunctureIso (k : ℕ) (b a : Bool) :
    branchTorus Q ≅ branchTorus Q :=
  arithmeticZeroFifthInitialTotalPunctureIso hπ data H m hj u hu b a ≪≫
    punctureSpecIso (arithmeticZeroFiniteInitialPunctureEquiv hπ data H 0 hj u hu k m b a)

/-- All finite corrections preserve both entire original Laurent boundaries. -/
@[reassoc] theorem arithmeticZeroFiniteInitialTotalNodeIso_puncture (k : ℕ) (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroFiniteInitialTotalNodeIso hπ data H m hj u hu k b).hom =
      (arithmeticZeroFiniteInitialTotalPunctureIso hπ data H m hj u hu k b a).hom ≫
        punctureOpen ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).initial m b) a := by
  simp only [arithmeticZeroFiniteInitialTotalNodeIso,
    arithmeticZeroFiniteInitialTotalPunctureIso, Iso.trans_hom, ← Category.assoc,
    arithmeticZeroFifthInitialTotalNodeIso_puncture]
  rw [Category.assoc, arithmeticZeroFiniteInitialNodeIso_puncture, ← Category.assoc]

/-- The actual diagonal boundary retains the full finite Laurent substitution. -/
@[reassoc] theorem arithmeticZeroDiagonalInitialTotalNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu b).hom =
      (arithmeticZeroFiniteInitialTotalPunctureIso hπ data H m hj u hu m b a).hom ≫
        punctureOpen ((arithmeticZeroDiagonalState hπ data H 0 hj u hu).initial m b) a := by
  simp only [arithmeticZeroDiagonalInitialTotalNodeIso, Iso.trans_hom, ← Category.assoc,
    arithmeticZeroFiniteInitialTotalNodeIso_puncture]
  rw [Category.assoc, punctureOpen_parameter]

end FLT.Mazur.WeierstrassDividedDepth
