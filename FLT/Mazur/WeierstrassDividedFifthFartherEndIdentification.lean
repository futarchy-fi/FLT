/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodeIdentification

/-!
# Endpoint identifications in the depth-three fifth atlas

The last and terminal factors recover their exact fourth inclusions.
The full original infinity chart retains its inclusion.
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
  (ha₃ : 3 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthFartherAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFifthFartherAtlasCorrection hπ data H m j hj u hu ha₃
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha₃
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticFifthShallowLastOrientedIso hπ data H m j hj u hu
local notation "N" => arithmeticFourthOuterLastIdentification hπ data H m j hj u hu

omit ha₃ in
/-- The last label keeps the complete normalized smoothing. -/
def arithmeticFifthFartherLastIdentification (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ A (.retained ⟨j, by omega⟩ b) := eqToIso (by
  simp only [arithmeticFifthFartherAtlasObject, ↓reduceIte])

local notation "L" => arithmeticFifthFartherLastIdentification hπ data H m j hj u hu

omit [IsBezout R] in
/-- The installed last correction is its complete oriented factor. -/
theorem arithmeticFifthFartherAtlasCorrection_last (b : Bool) :
    E (.retained ⟨j, by omega⟩ b) = (N b).symm ≪≫ C b ≪≫ L b := by
  simp only [arithmeticFifthFartherAtlasCorrection, ↓reduceDIte, eqToIso_refl, Iso.refl_trans]
  rfl

/-- The complete last factor recovers the actual fourth global chart. -/
@[reassoc] theorem arithmeticFifthFartherLast_chart (b : Bool) :
    (C b).hom ≫ (L b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (N b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticFifthFartherAtlasCorrection_chart hπ data H m j hj u hu ha₃
    (.retained ⟨j, by omega⟩ b)
  rw [arithmeticFifthFartherAtlasCorrection_last] at h
  have hh := congrArg (fun f ↦ (N b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

/-- The terminal label uses its complete fifth correction. -/
@[reassoc] theorem arithmeticFifthFartherTerminal_chart :
    (arithmeticFifthShallowTerminalIso hπ data H m j hj u hu).hom ≫ ι .terminal =
      κ .terminal := arithmeticFifthFartherAtlasCorrection_chart hπ data H m j hj u hu ha₃ .terminal

/-- The full infinity inclusion is unchanged. -/
theorem arithmeticFifthFartherAtlasChart_infinity : ι .infinity = κ .infinity := by
  simpa only [arithmeticFifthFartherAtlasCorrection, Iso.refl_hom, Category.id_comp] using
    arithmeticFifthFartherAtlasCorrection_chart hπ data H m j hj u hu ha₃ .infinity


end FLT.Mazur.WeierstrassDividedDepth
