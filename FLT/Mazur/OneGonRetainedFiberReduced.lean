/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionFiberCharts
public import FLT.Mazur.IdealSheafRadicalOpen

/-!
# Reducedness of the original one-gon normalization fiber

The affine endpoint chart has quotient K × K, and the full Laurent chart has
empty fiber. These two original opens prove radicality on the complete P1.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
namespace FLT.Mazur.OneGonRetainedFiberReduced
open PolygonOneGonContraction PolygonPinching BaseAdicThickening
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]
local notation "I" => Scheme.IdealSheafData.comap
  (Scheme.Hom.ker (Over.Hom.left (targetNode K))) (Over.Hom.left (retainedComponent K))

/-- The retained normalization fiber is empty on the entire original Laurent open. -/
theorem torus_ideal : (I).comap (torusToComponent K).left = ⊤ := by
  have he := fiberIdeal_retained_torus K 1 (by decide)
    (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
    (PolygonAtlas.isPushout K 1 (by decide)) 0
  change (fiberIdeal K 1 (by decide) (PolygonAtlas.normalization K 1)
    (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) 0).comap
    ((torusToComponent K).left ≫
      (componentι K 1 0 ≫ PolygonAtlas.normalization K 1).left) = ⊤ at he
  rw [Scheme.IdealSheafData.comap_comp, fiberIdeal_retained] at he
  exact he

/-- The retained affine endpoint equation defines a reduced scheme, with both endpoints. -/
theorem affine_ideal_radical :
    ((I).comap (OneGonAffineNormalization.alpha K)).radical =
      (I).comap (OneGonAffineNormalization.alpha K) := by
  rw [retained_node_chart_ideal]
  have he : baseIdeal (.of K[X]) (Ideal.span ({X * (X - 1)} : Set K[X])) =
      (Spec.map (CommRingCat.ofHom (OneGonNodeNormalizationIdeal.endpoints K))).ker := by
    rw [specMap_ker_baseIdeal]
    exact congrArg (baseIdeal (.of K[X]))
      (OneGonNodeNormalizationIdeal.endpoints_ker K).symm
  rw [he]
  exact IdealSheafRadicalOpen.ker_radical _

/-- The full normalization fiber ideal is radical, not merely generically reduced. -/
theorem retained_ideal_radical : (I).radical = I := by
  apply IdealSheafRadicalOpen.radical_eq_of_cover (I)
    (BinaryOpenDescent.cover (OneGonAffineNormalization.alpha K)
      (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K)
      (OneGonAffineNormalization.covers K))
  intro b
  cases b
  · exact affine_ideal_radical K
  · change ((I).comap (torusToComponent K).left).radical =
      (I).comap (torusToComponent K).left
    rw [torus_ideal, Scheme.IdealSheafData.radical_top]

end FLT.Mazur.OneGonRetainedFiberReduced
