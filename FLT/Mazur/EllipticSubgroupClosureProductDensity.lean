/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupSectionFamilyDensity

/-!
# Actual integral subgroup pairs are schematically dense

The paired section family is identified with the product of the dense section
maps. Its kernel is therefore zero over a DVR, without a density hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The actual section-pair family equals the constructed product comparison. -/
theorem closureSectionPairsMap_eq_product :
    closureSectionPairsMap A W H =
      (closureSectionSourceProductIso A W H).hom ≫ closureSectionsProductMap A W H := by
  apply Sigma.hom_ext
  intro PQ
  apply pullback.hom_ext
  · simp only [closureSectionPairsMap, Sigma.ι_comp_desc_assoc, closureSectionPair_fst,
      Category.assoc, closureSectionsProductMap, pullback.map, pullback.lift_fst,
      closureSectionSourceProductIso_fst_assoc, Sigma.ι_comp_desc_assoc,
      closureSectionsMap_point]
  · simp only [closureSectionPairsMap, Sigma.ι_comp_desc_assoc, closureSectionPair_snd,
      Category.assoc, closureSectionsProductMap, pullback.map, pullback.lift_snd,
      closureSectionSourceProductIso_snd_assoc, Sigma.ι_comp_desc_assoc,
      closureSectionsMap_point]

variable [IsDedekindDomain A]

/-- Every equation on the product is detected by the actual integral subgroup pairs. -/
instance closureSectionPairsMap_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (closureSectionPairsMap A W H) := by
  rw [closureSectionPairsMap_eq_product]
  infer_instance

/-- Pulling back a morphism along all integral pairs does not change its kernel. -/
theorem closureSectionPairsMap_ker_comp {X : Scheme} (f : closureProduct A W H ⟶ X) :
    (closureSectionPairsMap A W H ≫ f).ker = f.ker := by
  rw [Scheme.Hom.ker_comp, (closureSectionPairsMap A W H).ker_eq_bot,
    Scheme.IdealSheafData.map_bot]

end FLT.Mazur.EllipticSubgroupChart
