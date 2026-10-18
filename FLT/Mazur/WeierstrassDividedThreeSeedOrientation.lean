/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThreeSeedAtlas
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasIncoming
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasPreceding
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasLastIncoming
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasClosing
public import FLT.Mazur.WeierstrassDividedFifthFartherAtlasEdge

/-!
# All depth-three seed overlaps in uniform puncture coordinates

Both endpoints of each internal residual are inverted. The retained label
identifications and the last original orientation stay inside the seed inclusions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "S" => arithmeticThreeSeedState hπ data H hj u hu
local notation "ι" => arithmeticThreeSeedAtlasChart hπ data H m hj u hu
attribute [local irreducible] arithmeticFifthFartherAtlasChart
  arithmeticFifthDeepIncomingEquiv


/-- All three internal seed edges have their exact conjugated residual. -/
@[reassoc] theorem arithmeticThreeSeedAtlas_incoming (i : Fin 3) (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((S).retained m i.castSucc b) ≫
        ι (.retained i.castSucc b) =
      (punctureSpecIso (arithmeticThreeSeedIncoming hπ data H hj u hu m i b)).hom ≫
        rightBranchOpen Q ((S).retained m i.succ b) ≫ ι (.retained i.succ b) := by
  fin_cases i
  · have h := congrArg (fun f ↦ (edgeInversion Q).hom ≫ f)
      (arithmeticFifthFartherAtlas_residual_outerIncoming hπ data H m 3 hj u hu rfl b)
    simpa [arithmeticThreeSeedAtlasChart, arithmeticThreeSeedIdentification,
      arithmeticThreeSeedState, arithmeticThreeSeedIncoming, Fin.castSucc, Fin.castAdd, Fin.succ,
      Fin.isValue, ↓reduceIte, punctureSpecIso_trans, punctureSpecIso_invert,
      Iso.trans_hom, precedingBranch, Category.assoc] using h
  · have h := congrArg (fun f ↦ (edgeInversion Q).hom ≫ f)
      (arithmeticFifthFartherAtlas_residual_preceding hπ data H m 3 hj u hu rfl 1 rfl b)
    simpa [arithmeticThreeSeedAtlasChart, arithmeticThreeSeedIdentification,
      arithmeticThreeSeedState, arithmeticThreeSeedIncoming, Fin.castSucc, Fin.castAdd, Fin.succ,
      Fin.isValue, ↓reduceIte, punctureSpecIso_trans, punctureSpecIso_invert,
      Iso.trans_hom, precedingBranch, Category.assoc] using h
  · have h := congrArg (fun f ↦ (edgeInversion Q).hom ≫ f)
      (arithmeticFifthFartherAtlas_residual_incoming hπ data H m 3 hj u hu rfl 2 rfl b)
    simpa [arithmeticThreeSeedAtlasChart, arithmeticThreeSeedIdentification,
      arithmeticThreeSeedState, arithmeticThreeSeedIncoming, Fin.castSucc, Fin.castAdd, Fin.succ,
      Fin.isValue, ↓reduceIte, punctureSpecIso_trans, punctureSpecIso_invert,
      Iso.trans_hom, precedingBranch, Category.assoc] using h

/-- The same last identified node serves the full closing edge. -/
@[reassoc] theorem arithmeticThreeSeedAtlas_closing (b : Bool) :
    (edgeInversion Q).hom ≫ leftBranchOpen Q ((S).retained m 3 b) ≫ ι (.retained 3 b) =
      (punctureSpecIso ((S).edgeEquiv .closing m b)).hom ≫
        punctureOpen ((S).terminal m) b ≫ ι .terminal := by
  simpa [arithmeticThreeSeedAtlasChart, arithmeticThreeSeedIdentification,
    arithmeticThreeSeedState, Fin.isValue, ↓reduceIte, Iso.trans_hom,
    arithmeticClosingRetainedBoundary, Iso.refl_hom, Category.id_comp, Category.assoc]
    using arithmeticFifthFartherAtlas_residual_closing hπ data H m 3 hj u hu rfl b

/-- The actual initial open retains the full original Mobius/right base residual. -/
@[reassoc] theorem arithmeticThreeSeedAtlas_initial (b : Bool) :
    arithmeticFifthFartherPuncture hπ data H m 3 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso ((S).edgeEquiv .initial m b)).hom ≫
        rightBranchOpen Q ((S).retained m 0 b) ≫ ι (.retained 0 b) := by
  simpa [arithmeticThreeSeedAtlasChart, arithmeticThreeSeedIdentification,
    arithmeticThreeSeedState, Fin.isValue, ↓reduceIte, Category.assoc]
    using arithmeticFifthFartherAtlas_residual_initial hπ data H m 3 hj u hu rfl b

end FLT.Mazur.WeierstrassDividedDepth
