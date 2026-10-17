/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEarlierIncoming

/-!
# The next actual edge beyond the fifth deep factors

An unaffected retained chart attaches to the earlier corrected node through
its complete opposite compensation. This edge has no fifth-layer residual.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthDeepAtlasChart arithmeticFifthDeepEarlierIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (hj₄ : 4 ≤ j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthDeepAtlasObject hπ data H m j hj u hu
local notation "ι" => arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m

variable (a : ℕ) (ha : a + 5 = j)
local notation "M" => arithmeticFifthDeepEarlierIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "N" => arithmeticFifthDeepBeforeIdentification hπ data H m j hj u hu
local notation "s" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m

/-- The next actual edge retains the earlier node's full opposite compensation. -/
@[reassoc] theorem arithmeticFifthDeepAtlas_earlier_adjacent (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ (N ⟨a, by omega⟩ (show a + 4 < j by omega) b).hom ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticFifthDeepEarlierIncomingIso hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  rw [arithmeticFifthDeepBefore_chart]
  exact (changedArithmeticAtlas_normalized_adjacent
    hπ data H m j hj u hu a (by omega) b).trans
      (arithmeticFifthDeepEarlier_incoming hπ data H j hj u hu m hj₄ (a + 1) (by omega) b)

omit m in
/-- The next complete retained edge also has identity residual on the fifth layer. -/
@[reassoc] theorem arithmeticFifthDeepAtlas_earlier_adjacent_fifth (b : Bool) :
    leftBranchOpen (Quotient R π 5)
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 5) ≫
      (twistedRetainedOrientation data H 5 b).hom ≫
        (arithmeticFifthDeepBeforeIdentification hπ data H 5 j hj u hu
          ⟨a, by omega⟩ (show a + 4 < j by omega) b).hom ≫
            arithmeticFifthDeepAtlasChart hπ data H 5 j hj u hu hj₄ (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 5)
          (arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu 5 b) ≫
        (arithmeticFifthDeepEarlierIdentification hπ data H 5 j hj u hu
          (a + 1) (by omega) b).hom ≫
            arithmeticFifthDeepAtlasChart hπ data H 5 j hj u hu hj₄
              (.retained ⟨a + 1, by omega⟩ b) := by
  have h := arithmeticFifthDeepAtlas_earlier_adjacent hπ data H 5 j hj u hu hj₄ a ha b
  rw [arithmeticFifthDeepEarlierIncomingIso_fifth, Iso.refl_hom, Category.id_comp] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
