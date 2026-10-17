/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepAtlasIdentification

/-!
# Endpoint identifications in the full fifth deep atlas

The earlier, last and terminal factors recover their exact fourth inclusions.
The whole original initial charts and infinity retain their original inclusions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFifthDeepNodeIso arithmeticFifthDeepEarlierIso
  arithmeticFifthShallowLastOrientedIso arithmeticFifthShallowTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (hj₄ : 4 ≤ j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthDeepAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFifthDeepAtlasCorrection hπ data H m j hj u hu hj₄
local notation "ι" => arithmeticFifthDeepAtlasChart hπ data H m j hj u hu hj₄
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticFifthShallowLastOrientedIso hπ data H m j hj u hu
local notation "N" => arithmeticFourthOuterLastIdentification hπ data H m j hj u hu

omit hj₄ in
/-- The last label keeps the complete normalized smoothing. -/
def arithmeticFifthDeepLastIdentification (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ A (.retained ⟨j, by omega⟩ b) := eqToIso (by
  simp only [arithmeticFifthDeepAtlasObject, ↓reduceIte])

local notation "L" => arithmeticFifthDeepLastIdentification hπ data H m j hj u hu

omit [IsBezout R] in
/-- The installed last correction is its complete oriented factor. -/
theorem arithmeticFifthDeepAtlasCorrection_last (b : Bool) :
    E (.retained ⟨j, by omega⟩ b) = (N b).symm ≪≫ C b ≪≫ L b := by
  simp only [arithmeticFifthDeepAtlasCorrection, ↓reduceDIte, eqToIso_refl, Iso.refl_trans]
  rfl

/-- The complete last factor recovers the actual fourth global chart. -/
@[reassoc] theorem arithmeticFifthDeepLast_chart (b : Bool) :
    (C b).hom ≫ (L b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (N b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticFifthDeepAtlasCorrection_chart hπ data H m j hj u hu hj₄
    (.retained ⟨j, by omega⟩ b)
  rw [arithmeticFifthDeepAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (N b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

/-- The terminal label uses its complete fifth correction. -/
@[reassoc] theorem arithmeticFifthDeepTerminal_chart :
    (arithmeticFifthShallowTerminalIso hπ data H m j hj u hu).hom ≫ ι .terminal =
      κ .terminal := arithmeticFifthDeepAtlasCorrection_chart hπ data H m j hj u hu hj₄ .terminal

/-- Each complete original initial chart retains its fourth inclusion. -/
theorem arithmeticFifthDeepAtlasChart_initial (b : Bool) : ι (.initial b) = κ (.initial b) := by
  simpa only [arithmeticFifthDeepAtlasCorrection, Iso.refl_hom, Category.id_comp] using
    arithmeticFifthDeepAtlasCorrection_chart hπ data H m j hj u hu hj₄ (.initial b)

/-- The full infinity inclusion is unchanged. -/
theorem arithmeticFifthDeepAtlasChart_infinity : ι .infinity = κ .infinity := by
  simpa only [arithmeticFifthDeepAtlasCorrection, Iso.refl_hom, Category.id_comp] using
    arithmeticFifthDeepAtlasCorrection_chart hπ data H m j hj u hu hj₄ .infinity

variable (a : ℕ) (ha : a + 4 = j)
local notation "D" => arithmeticFifthDeepEarlierInputIdentification hπ data H m j hj u hu a ha
local notation "F" => arithmeticFifthDeepEarlierIso hπ data H j hj u hu m
local notation "e" => arithmeticFifthDeepEarlierSmoothing hπ data H j hj u hu m

omit hj₄ in
/-- The next earlier installed label has its full changed fifth smoothing. -/
def arithmeticFifthDeepEarlierIdentification (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅ A (.retained ⟨a, by omega⟩ b) := eqToIso (by
  simp only [arithmeticFifthDeepAtlasObject, show ¬a = j by omega,
    show ¬a + 1 = j by omega, show ¬a + 2 = j by omega,
    show ¬a + 3 = j by omega, ha, ↓reduceIte])

local notation "M" => arithmeticFifthDeepEarlierIdentification hπ data H m j hj u hu a ha

omit [IsBezout R] in
/-- The earlier correction starts from the full original orientation. -/
theorem arithmeticFifthDeepAtlasCorrection_earlier (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) = (D b).symm ≪≫ (O b).symm ≪≫ F b ≪≫ M b := by
  simp only [arithmeticFifthDeepAtlasCorrection, show ¬a = j by omega,
    show ¬a + 1 = j by omega, show ¬a + 2 = j by omega,
    show ¬a + 3 = j by omega, ha, ↓reduceDIte]
  rfl

/-- The installed earlier factor recovers its normalized fourth inclusion. -/
@[reassoc] theorem arithmeticFifthDeepEarlier_chart (b : Bool) :
    (F b).hom ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (O b).hom ≫ (D b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
  have h := arithmeticFifthDeepAtlasCorrection_chart hπ data H m j hj u hu hj₄
    (.retained ⟨a, by omega⟩ b)
  rw [arithmeticFifthDeepAtlasCorrection_earlier hπ data H m j hj u hu hj₄ a ha b] at h
  have hh := congrArg (fun f ↦ (O b).hom ≫ (D b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
