/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasTestPair
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairTransition

/-!
# Arithmetic test transitions on their exact full smooth domain

Equality of the original arithmetic inputs identifies the entire smooth
source domains and induces the canonical integral atlas-pair transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j ≤ n) (a b c d : Fin (j + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
variable {T : Scheme}
  (x : T ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj a)
  (y : T ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj b)
  (z : T ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj c)
  (w : T ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj d)
  (h₁ : x ≫ arithmeticTensorAtlasMap hπ data m j hj a =
    z ≫ arithmeticTensorAtlasMap hπ data m j hj c)
  (h₂ : y ≫ arithmeticTensorAtlasMap hπ data m j hj b =
    w ≫ arithmeticTensorAtlasMap hπ data m j hj d)
local notation "D" => arithmeticAtlasTestOpen hπ data m j hj a b x y
local notation "E" => arithmeticAtlasTestOpen hπ data m j hj c d z w

include h₁ h₂ in
/-- Both sides have exactly the same full smooth preimage, including boundary points. -/
theorem arithmeticAtlasTestTransition_open : D = E := by
  rw [arithmeticAtlasTestOpen_eq, arithmeticAtlasTestOpen_eq]
  simp only [← Category.assoc, h₁, h₂]

variable (h : x ≫ arithmeticTensorAtlasMap hπ data m j hj a ≫
    finiteGlobalArithmeticStructure hπ data j hj m =
  y ≫ arithmeticTensorAtlasMap hπ data m j hj b ≫ finiteGlobalArithmeticStructure hπ data j hj m)
omit [IsNoetherianRing R] in
include h₁ h₂ h in
/-- The target inputs retain the common actual arithmetic coefficient point. -/
theorem arithmeticAtlasTestTransition_base : z ≫ chart c ≫ s = w ≫ chart d ≫ s := by
  simpa only [← Category.assoc, h₁, h₂] using h

local notation "ht" => arithmeticAtlasTestTransition_base hπ data m j hj a b c d x y z w h₁ h₂ h
local notation "u" => arithmeticAtlasTestPair hπ data m j hj a b x y h

/-- The target smooth pair is defined on the complete source smooth domain. -/
def arithmeticAtlasTestTarget : (D).toScheme ⟶
    pullback ((O c).ι ≫ chart c ≫ s) ((O d).ι ≫ chart d ≫ s) :=
  T.homOfLE (arithmeticAtlasTestTransition_open hπ data m j hj a b c d x y z w h₁ h₂).le ≫
    arithmeticAtlasTestPair hπ data m j hj c d z w ht

local notation "v" => arithmeticAtlasTestTarget hπ data m j hj a b c d x y z w h₁ h₂ h

/-- The target's first input equals the original source first input schematically. -/
@[reassoc] theorem arithmeticAtlasTestTarget_first :
    v ≫ pullback.fst _ _ ≫ (O c).ι ≫ chart c = (D).ι ≫ x ≫ chart a := by
  rw [arithmeticAtlasTestTarget, Category.assoc, arithmeticAtlasTestPair_first,
    Scheme.homOfLE_ι_assoc, h₁]

/-- The target's second input equals the original source second input schematically. -/
@[reassoc] theorem arithmeticAtlasTestTarget_second :
    v ≫ pullback.snd _ _ ≫ (O d).ι ≫ chart d = (D).ι ≫ y ≫ chart b := by
  rw [arithmeticAtlasTestTarget, Category.assoc, arithmeticAtlasTestPair_second,
    Scheme.homOfLE_ι_assoc, h₂]

/-- The full smooth test domain maps to the canonical simultaneous integral transition. -/
def arithmeticAtlasTestTransition :
    (D).toScheme ⟶ (atlasPairTransferOpen hπ data j hj a b c d).toScheme :=
  arithmeticAtlasPairTransitionLift hπ data m j hj a b c d u v
    (by rw [arithmeticAtlasTestPair_first, arithmeticAtlasTestTarget_first])
    (by rw [arithmeticAtlasTestPair_second, arithmeticAtlasTestTarget_second])

/-- The integral transition has exactly the original arithmetic source presentation. -/
@[reassoc] theorem arithmeticAtlasTestTransition_source :
    arithmeticAtlasTestTransition hπ data m j hj a b c d x y z w h₁ h₂ h ≫
      (atlasPairTransferOpen hπ data j hj a b c d).ι =
      u ≫ arithmeticAtlasPairPresentation hπ data m j hj a b :=
  arithmeticAtlasPairTransitionLift_source hπ data m j hj a b c d u v _ _

/-- Applying the integral transfer gives exactly the explicit target presentation. -/
@[reassoc] theorem arithmeticAtlasTestTransition_target :
    arithmeticAtlasTestTransition hπ data m j hj a b c d x y z w h₁ h₂ h ≫
      atlasPairTransfer hπ data j hj a b c d =
      v ≫ arithmeticAtlasPairPresentation hπ data m j hj c d :=
  arithmeticAtlasPairTransitionLift_target hπ data m j hj a b c d u v _ _

end FLT.Mazur.WeierstrassDividedDepth
