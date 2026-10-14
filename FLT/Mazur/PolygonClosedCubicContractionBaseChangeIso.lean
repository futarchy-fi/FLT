/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionIso
public import FLT.Mazur.PolygonOneGonContractionBaseChange

/-!
# The original closed contraction comparison after arbitrary base change

Bundle the global isomorphism over the original residue field, then pull it
back along any scheme over that field. The independently descended pinching
contraction factors the actual changed cubic map through this isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "d" => PolygonOneGonContraction.contraction K n (by omega) p q hp i

/-- The entire original cubic comparison is an isomorphism over the original residue field. -/
def closedPointContractionCubicOverIso :
    PolygonAtlas.polygon K 1 ≅ closedPointCubicOver K n h i :=
  Over.isoMk (closedPointContractionCubicIso K n h i)
    (closedPointContractionCubicIso_over K n h i)

/-- The bundled isomorphism retains precisely the original descended comparison. -/
theorem closedPointContractionCubicOverIso_hom :
    (closedPointContractionCubicOverIso K n h i).hom =
      closedPointContractionComparison K n h i := by
  apply Over.OverMorphism.ext
  rfl

/-- The original factorization retains its actual coefficient morphisms. -/
@[reassoc] theorem closedPointContractionCubicOverIso_fac :
    d ≫ (closedPointContractionCubicOverIso K n h i).hom =
      closedPointToCubicOver K n h i := by
  apply Over.OverMorphism.ext
  exact closedPointContractionCubicIso_fac K n h i

variable {T : Scheme} (t : T ⟶ Spec (.of K))

/-- The global closed comparison stays an isomorphism over any original-field scheme. -/
def closedPointContractionCubicBaseChangeIso :
    (Over.pullback t).obj (PolygonAtlas.polygon K 1) ≅
      (Over.pullback t).obj (closedPointCubicOver K n h i) :=
  (Over.pullback t).mapIso (closedPointContractionCubicOverIso K n h i)

/-- The descended changed pinching contraction factors the actual changed cubic morphism. -/
@[reassoc] theorem closedPointContractionCubicBaseChangeIso_fac :
    PolygonOneGonContraction.baseChangedContraction K n (by omega) p q hp i t ≫
      (closedPointContractionCubicBaseChangeIso K n h i t).hom =
        (Over.pullback t).map (closedPointToCubicOver K n h i) := by
  rw [PolygonOneGonContraction.baseChangedContraction_eq]
  change (Over.pullback t).map d ≫
    (Over.pullback t).map (closedPointContractionCubicOverIso K n h i).hom = _
  rw [← Functor.map_comp, closedPointContractionCubicOverIso_fac]

/-- The inverse recovers the actual changed contraction on the full changed polygon. -/
@[reassoc] theorem closedPointContractionCubicBaseChangeIso_inverse_fac :
    (Over.pullback t).map (closedPointToCubicOver K n h i) ≫
      (closedPointContractionCubicBaseChangeIso K n h i t).inv =
        PolygonOneGonContraction.baseChangedContraction K n (by omega) p q hp i t := by
  rw [← closedPointContractionCubicBaseChangeIso_fac, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
