/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedAtlasPairIso

/-!
# Coefficient presentations of the full smooth atlas pairs

A pair of integral chart presentations over any coefficient scheme gives
an actual map into the unchanged smooth integral atlas pair. The source
retains all smooth inputs in both factors, rather than a punctured subset.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "chart" => globalSmoothAtlasMap hπ data j hj
local notation "A" => globalSmoothAtlasOpen hπ data j hj a
local notation "B" => globalSmoothAtlasOpen hπ data j hj b
local notation "ta" => chart a ≫ t
local notation "tb" => chart b ≫ t
variable {X Y C : Scheme} (q : C ⟶ Spec (.of R)) (f : X ⟶ C) (g : Y ⟶ C)
  (x : X ⟶ globalIntegralAtlasObject data j hj a)
  (y : Y ⟶ globalIntegralAtlasObject data j hj b)
  (hx : x ≫ globalIntegralAtlasMap hπ data j hj a ≫
    finiteGlobalStructure hπ data j hj = f ≫ q)
  (hy : y ≫ globalIntegralAtlasMap hπ data j hj b ≫
    finiteGlobalStructure hπ data j hj = g ≫ q)
local notation "OX" => x ⁻¹ᵁ A
local notation "OY" => y ⁻¹ᵁ B
local notation "fx" => (OX).ι ≫ f
local notation "gy" => (OY).ι ≫ g

include hx in
/-- The entire smooth restriction of a chart presentation retains its coefficient point. -/
@[reassoc] theorem atlasPresentation_left_structure : (x ∣_ A) ≫ ta = fx ≫ q := by
  rw [Category.assoc, globalSmoothAtlasMap_inclusion_assoc, morphismRestrict_ι_assoc, hx]

include hy in
/-- The second complete smooth presentation retains its coefficient point as well. -/
@[reassoc] theorem atlasPresentation_right_structure : (y ∣_ B) ≫ tb = gy ≫ q := by
  rw [Category.assoc, globalSmoothAtlasMap_inclusion_assoc, morphismRestrict_ι_assoc, hy]

/-- The relative product of both full smooth presentations maps to the actual atlas pair. -/
def atlasPairPresentation : pullback fx gy ⟶ pullback ta tb :=
  pullback.map fx gy ta tb (x ∣_ A) (y ∣_ B) q
    (atlasPresentation_left_structure hπ data j hj a q f x hx).symm
    (atlasPresentation_right_structure hπ data j hj b q g y hy).symm

local notation "input" => atlasPairPresentation hπ data j hj a b q f g x y hx hy

/-- The first input uses all the original integral chart functions. -/
@[reassoc] theorem atlasPairPresentation_first :
    input ≫ pullback.fst ta tb ≫ (A).ι = pullback.fst fx gy ≫ (OX).ι ≫ x := by
  rw [atlasPairPresentation, pullback.lift_fst_assoc, Category.assoc, morphismRestrict_ι]

/-- The second input uses all the original integral chart functions simultaneously. -/
@[reassoc] theorem atlasPairPresentation_second :
    input ≫ pullback.snd ta tb ≫ (B).ι = pullback.snd fx gy ≫ (OY).ι ≫ y := by
  rw [atlasPairPresentation, pullback.lift_snd_assoc, Category.assoc, morphismRestrict_ι]

/-- The first resolved input is exactly the original presentation in the global model. -/
@[reassoc] theorem atlasPairPresentation_first_global :
    input ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.fst t t ≫ (base).smoothLocus.ι =
        pullback.fst fx gy ≫ (OX).ι ≫ x ≫ globalIntegralAtlasMap hπ data j hj a := by
  rw [finiteResolvedAtlasPairInput_fst_assoc, globalSmoothAtlasMap_inclusion,
    atlasPairPresentation_first_assoc]

/-- The second resolved input is exactly the original presentation in the global model. -/
@[reassoc] theorem atlasPairPresentation_second_global :
    input ≫ finiteResolvedAtlasPairInput hπ data j hj a b ≫
      pullback.snd t t ≫ (base).smoothLocus.ι =
        pullback.snd fx gy ≫ (OY).ι ≫ y ≫ globalIntegralAtlasMap hπ data j hj b := by
  rw [finiteResolvedAtlasPairInput_snd_assoc, globalSmoothAtlasMap_inclusion,
    atlasPairPresentation_second_assoc]

/-- The integral pair retains the original common coefficient point. -/
@[reassoc] theorem atlasPairPresentation_structure :
    input ≫ pullback.fst ta tb ≫ ta = pullback.fst fx gy ≫ fx ≫ q := by
  rw [atlasPairPresentation, pullback.lift_fst_assoc, Category.assoc,
    atlasPresentation_left_structure hπ data j hj a q f x hx]

end FLT.Mazur.WeierstrassDividedDepth
