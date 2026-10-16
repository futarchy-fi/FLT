/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedPolygonInjectivity

/-!
# The complete original closed arithmetic model is the prescribed polygon

The already constructed surjective local isomorphism is now globally
injective. Its resulting isomorphism keeps the full original chart maps
and the simultaneous twisted-stage comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "F" => arithmeticClosedPolygonMap hπ data H j hj u hu
local notation "Y" => arithmeticFactorRatioPolygon π 0 W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu

instance arithmeticClosedPolygonMap_isIso : IsIso F :=
  arithmeticClosedPolygonMap_isIso_of_injective hπ data H j hj u hu
    (arithmeticClosedPolygonMap_injective hπ data H j hj u hu)

/-- The entire original closed arithmetic stage has the prescribed polygon isomorphism. -/
def arithmeticClosedPolygonIso : finiteGlobalArithmeticStage hπ data (j + 1) hj 0 ≅ Y :=
  asIso F

/-- Every full original chart is preserved by the resulting isomorphism. -/
@[reassoc] theorem arithmeticClosedPolygonIso_chart (i : ArithmeticChartLabel (j + 1)) :
    a i ≫ (arithmeticClosedPolygonIso hπ data H j hj u hu).hom = G i :=
  arithmeticClosedPolygonMap_chart hπ data H j hj u hu i

instance twistedArithmeticClosedPolygonMap_isIso :
    IsIso (twistedArithmeticClosedPolygonMap hπ data H j hj u hu) := by
  unfold twistedArithmeticClosedPolygonMap
  infer_instance

/-- The complete simultaneous twisted closed stage has the same prescribed polygon. -/
def twistedArithmeticClosedPolygonIso :
    simultaneousTwistedArithmeticStage hπ data H 0 j hj u hu ≅ Y :=
  asIso (twistedArithmeticClosedPolygonMap hπ data H j hj u hu)

/-- Transport through the full twisted model recovers the original closed isomorphism. -/
@[reassoc] theorem twistedArithmeticClosedPolygonIso_original :
    (simultaneousTwistedArithmeticIso hπ data H 0 j hj u hu).hom ≫
      (twistedArithmeticClosedPolygonIso hπ data H j hj u hu).hom =
        (arithmeticClosedPolygonIso hπ data H j hj u hu).hom :=
  twistedArithmeticClosedPolygonMap_original hπ data H j hj u hu

end FLT.Mazur.WeierstrassDividedDepth
