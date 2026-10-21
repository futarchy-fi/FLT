/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation

/-!
# Full smooth domains of arithmetic test pairs

Two actual indexed inputs with a common quotient coefficient point restrict
to the full simultaneous smooth preimage and give the original atlas pair.
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
  (m j : ℕ) (hj : j ≤ n) (a b : Fin (j + 3))
local notation "Q" => PolygonArithmeticStages.Quotient R π m
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "projection" => pullback.fst base q
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
variable {T : Scheme}
  (x : T ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj a)
  (y : T ⟶ globalTensorAtlasObject hπ data (PolygonArithmeticStages.Quotient R π m) j hj b)

/-- Both full smooth preimages in the actual arithmetic test scheme. -/
def arithmeticAtlasTestOpen : T.Opens := x ⁻¹ᵁ O a ⊓ y ⁻¹ᵁ O b

local notation "D" => arithmeticAtlasTestOpen hπ data m j hj a b x y

/-- The source retains exactly the points where both original resolved inputs are smooth. -/
theorem arithmeticAtlasTestOpen_eq :
    D = (x ≫ chart a ≫ projection) ⁻¹ᵁ (base).smoothLocus ⊓
      (y ≫ chart b ≫ projection) ⁻¹ᵁ (base).smoothLocus := by
  unfold arithmeticAtlasTestOpen tensorIntegralAtlasSmoothOpen globalSmoothAtlasOpen
  rw [← Scheme.Hom.comp_preimage (tensorIntegralAtlasProjection hπ data Q j hj a),
    ← Scheme.Hom.comp_preimage (tensorIntegralAtlasProjection hπ data Q j hj b),
    arithmeticAtlasProjection_global, arithmeticAtlasProjection_global,
    ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]

/-- The first smooth input keeps all original chart functions. -/
def arithmeticAtlasTestLeft : (D).toScheme ⟶ (O a).toScheme :=
  T.homOfLE inf_le_left ≫ (x ∣_ O a)

/-- The second smooth input keeps all original chart functions. -/
def arithmeticAtlasTestRight : (D).toScheme ⟶ (O b).toScheme :=
  T.homOfLE inf_le_right ≫ (y ∣_ O b)

@[reassoc] theorem arithmeticAtlasTestLeft_inclusion :
    arithmeticAtlasTestLeft hπ data m j hj a b x y ≫ (O a).ι = (D).ι ≫ x := by
  rw [arithmeticAtlasTestLeft, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc]

@[reassoc] theorem arithmeticAtlasTestRight_inclusion :
    arithmeticAtlasTestRight hπ data m j hj a b x y ≫ (O b).ι = (D).ι ≫ y := by
  rw [arithmeticAtlasTestRight, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc]

variable (h : x ≫ arithmeticTensorAtlasMap hπ data m j hj a ≫
    finiteGlobalArithmeticStructure hπ data j hj m =
  y ≫ arithmeticTensorAtlasMap hπ data m j hj b ≫ finiteGlobalArithmeticStructure hπ data j hj m)

/-- The entire simultaneous smooth restriction is a genuine arithmetic atlas pair. -/
def arithmeticAtlasTestPair : (D).toScheme ⟶
    pullback ((O a).ι ≫ chart a ≫ s) ((O b).ι ≫ chart b ≫ s) :=
  pullback.lift (arithmeticAtlasTestLeft hπ data m j hj a b x y)
    (arithmeticAtlasTestRight hπ data m j hj a b x y) (by
      simp only [arithmeticAtlasTestLeft_inclusion_assoc,
        arithmeticAtlasTestRight_inclusion_assoc, h])

/-- The first actual arithmetic input is unchanged after forming the smooth pair. -/
@[reassoc] theorem arithmeticAtlasTestPair_first :
    arithmeticAtlasTestPair hπ data m j hj a b x y h ≫ pullback.fst _ _ ≫
      (O a).ι ≫ chart a = (D).ι ≫ x ≫ chart a := by
  rw [arithmeticAtlasTestPair, pullback.lift_fst_assoc,
    arithmeticAtlasTestLeft_inclusion_assoc]

/-- The second actual arithmetic input is unchanged after forming the smooth pair. -/
@[reassoc] theorem arithmeticAtlasTestPair_second :
    arithmeticAtlasTestPair hπ data m j hj a b x y h ≫ pullback.snd _ _ ≫
      (O b).ι ≫ chart b = (D).ι ≫ y ≫ chart b := by
  rw [arithmeticAtlasTestPair, pullback.lift_snd_assoc,
    arithmeticAtlasTestRight_inclusion_assoc]

end FLT.Mazur.WeierstrassDividedDepth
