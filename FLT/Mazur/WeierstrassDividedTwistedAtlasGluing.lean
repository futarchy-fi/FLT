/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwistedAtlas

/-!
# Simultaneous gluing of the entire transported arithmetic atlas

The target glues every original label and full overlap, including all triple
overlaps. Its comparison with the original global model is constructed from
the whole-chart isomorphisms. Comparison with the prescribed polygon is separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "𝒰" => twistedArithmeticOpenCover hπ data H m j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "e" => twistedArithmeticAtlasIso hπ data H m j hj u hu

/-- All full transported overlaps and their actual triple-overlap cocycle. -/
def twistedArithmeticGlueData : Scheme.GlueData := (𝒰).gluedCover

/-- One target glues the entire transported atlas, including both closing branches. -/
def simultaneousTwistedArithmeticStage : Scheme :=
  (twistedArithmeticGlueData hπ data H m j hj u hu).glued

/-- The original global model is isomorphic to the complete constructed twisted target. -/
def simultaneousTwistedArithmeticIso :
    finiteGlobalArithmeticStage hπ data (j + 1) hj m ≅
      simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (asIso (𝒰).fromGlued).symm

/-- The actual chart inclusions in the simultaneous target. -/
def simultaneousTwistedArithmeticChart (i : ArithmeticChartLabel (j + 1)) :
    twistedArithmeticAtlasObject hπ data H m j hj i ⟶
      simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (twistedArithmeticGlueData hπ data H m j hj u hu).ι i

instance simultaneousTwistedArithmeticChart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (simultaneousTwistedArithmeticChart hπ data H m j hj u hu i) := by
  unfold simultaneousTwistedArithmeticChart
  infer_instance

local notation "I" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "ι" => simultaneousTwistedArithmeticChart hπ data H m j hj u hu

/-- The target chart maps back by the full inverse of its actual chart comparison. -/
@[reassoc] theorem simultaneousTwistedArithmeticChart_global
    (i : ArithmeticChartLabel (j + 1)) :
    ι i ≫ (I).inv = twistedArithmeticAtlasMap hπ data H m j hj u hu i :=
  (𝒰).ι_fromGlued i

/-- Every original labeled inclusion is preserved in the single simultaneous comparison. -/
@[reassoc] theorem simultaneousTwistedArithmeticIso_chart
    (i : ArithmeticChartLabel (j + 1)) : c i ≫ (I).hom = (e i).hom ≫ ι i := by
  apply (cancel_mono (I).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc,
    simultaneousTwistedArithmeticChart_global, twistedArithmeticAtlasIso_map]

/-- The complete original intersection is transported, for every pair of original labels. -/
def simultaneousTwistedArithmeticOverlapIso (a b : ArithmeticChartLabel (j + 1)) :
    pullback (c a) (c b) ≅ pullback (ι a) (ι b) :=
  asIso (pullback.map (c a) (c b) (ι a) (ι b) (e a).hom (e b).hom (I).hom
    (simultaneousTwistedArithmeticIso_chart hπ data H m j hj u hu a)
    (simultaneousTwistedArithmeticIso_chart hπ data H m j hj u hu b))

/-- The full overlap comparison preserves its first original chart projection. -/
@[reassoc] theorem simultaneousTwistedArithmeticOverlapIso_fst
    (a b : ArithmeticChartLabel (j + 1)) :
    (simultaneousTwistedArithmeticOverlapIso hπ data H m j hj u hu a b).hom ≫
      pullback.fst (ι a) (ι b) = pullback.fst (c a) (c b) ≫ (e a).hom :=
  pullback.lift_fst _ _ _

/-- The same complete overlap comparison preserves the second original projection. -/
@[reassoc] theorem simultaneousTwistedArithmeticOverlapIso_snd
    (a b : ArithmeticChartLabel (j + 1)) :
    (simultaneousTwistedArithmeticOverlapIso hπ data H m j hj u hu a b).hom ≫
      pullback.snd (ι a) (ι b) = pullback.snd (c a) (c b) ≫ (e b).hom :=
  pullback.lift_snd _ _ _

/-- The simultaneous gluing retains the full triple-overlap cocycle for every label triple. -/
theorem simultaneousTwistedArithmetic_cocycle (a b z : ArithmeticChartLabel (j + 1)) :
    (twistedArithmeticGlueData hπ data H m j hj u hu).t' a b z ≫
      (twistedArithmeticGlueData hπ data H m j hj u hu).t' b z a ≫
        (twistedArithmeticGlueData hπ data H m j hj u hu).t' z a b = 𝟙 _ :=
  (twistedArithmeticGlueData hπ data H m j hj u hu).cocycle a b z

end FLT.Mazur.WeierstrassDividedDepth
