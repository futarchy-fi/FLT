/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedPairAtlas
public import FLT.Mazur.WeierstrassDividedPairSecantGeometry

/-!
# Common divided coordinates on genuine resolved atlas pairs

Maps from the integral charts to a common divided chart give actual universal
formula inputs on their full smooth relative product. The two integral charts
need not be smooth after contraction to the divided chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalIntegralAtlasObject globalIntegralAtlasMap
  globalSmoothAtlasOpen globalSmoothAtlasMap
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n k : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (a b : Fin (j + 3)) (d : Data W π k)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "ca" => globalSmoothAtlasMap hπ data j hj a
local notation "cb" => globalSmoothAtlasMap hπ data j hj b
local notation "ta" => ca ≫ t
local notation "tb" => cb ≫ t
local notation "A" => Coordinate W (π ^ k) d.b3 d.b4 d.b6
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "P" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
variable (f : globalIntegralAtlasObject data j hj a ⟶ chart d)
  (g : globalIntegralAtlasObject data j hj b ⟶ chart d)
variable
  (hf : f ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj a ≫ finiteGlobalStructure hπ data j hj)
  (hg : g ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R (Coordinate W (π ^ k) d.b3 d.b4 d.b6))) =
      globalIntegralAtlasMap hπ data j hj b ≫ finiteGlobalStructure hπ data j hj)
local notation "left" => (globalSmoothAtlasOpen hπ data j hj a).ι ≫ f
local notation "right" => (globalSmoothAtlasOpen hπ data j hj b).ι ≫ g

include hf in
/-- The first full smooth chart keeps its coefficient point in divided coordinates. -/
@[reassoc] theorem atlasPairFormula_left_structure : left ≫ q = ta := by
  rw [Category.assoc, hf, ← globalSmoothAtlasMap_inclusion_assoc]

include hg in
/-- The second full smooth chart keeps its coefficient point in divided coordinates. -/
@[reassoc] theorem atlasPairFormula_right_structure : right ≫ q = tb := by
  rw [Category.assoc, hg, ← globalSmoothAtlasMap_inclusion_assoc]

/-- Common divided coordinates on the actual full relative atlas-chart product. -/
def atlasPairFormulaProduct : pullback ta tb ⟶ pullback q q :=
  pullback.map ta tb q q left right (𝟙 _) (by
    rw [Category.comp_id, atlasPairFormula_left_structure hπ data j hj a d f hf]) (by
    rw [Category.comp_id, atlasPairFormula_right_structure hπ data j hj b d g hg])

/-- Universal tensor coordinates for formulas on this actual atlas pair. -/
def atlasPairFormulaInput : pullback ta tb ⟶ Spec (.of P) :=
  atlasPairFormulaProduct hπ data j hj a b d f g hf hg ≫
    (dividedPairSpecIso W (π ^ k) d.b3 d.b4 d.b6).hom

local notation "input" => atlasPairFormulaInput hπ data j hj a b d f g hf hg
local notation "al" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "ar" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6

/-- The universal first input is the given contraction of the actual first chart. -/
@[reassoc] theorem atlasPairFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (al).toRingHom) =
      pullback.fst ta tb ≫ left := by
  rw [← dividedPairSpecIso_fst, atlasPairFormulaInput, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact pullback.lift_fst _ _ _

/-- The universal second input is the given contraction of the actual second chart. -/
@[reassoc] theorem atlasPairFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (ar).toRingHom) =
      pullback.snd ta tb ≫ right := by
  rw [← dividedPairSpecIso_snd, atlasPairFormulaInput, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact pullback.lift_snd _ _ _

/-- The formula source and the ambient resolved pair have the same coefficient point. -/
@[reassoc] theorem atlasPairFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) =
      finiteResolvedAtlasPairInput hπ data j hj a b ≫ pullback.fst t t ≫ t := by
  rw [← WeierstrassIntegralChart.specAlgHom_structure al,
    atlasPairFormulaInput_left_assoc, hf,
    ← globalSmoothAtlasMap_inclusion_assoc,
    finiteResolvedAtlasPairInput_fst_assoc]

end FLT.Mazur.WeierstrassDividedDepth
