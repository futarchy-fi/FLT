/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSubgroupIdeal
public import FLT.Mazur.GeneralizedCurveSmoothPullback
public import FLT.Mazur.NoetherianSmoothQuasiFiniteCartier
public import FLT.Mazur.CartierSupportOpenDescent

/-!
# Finite flat subgroups are Cartier over locally Noetherian bases

The full subgroup ideal is Cartier on the smooth group by its finite flat
rank. Its support lies in that open, so the same full ideal is Cartier on
the entire generalized curve, including its singular fibers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} (H : E.FiniteSubgroup n)

/-- The original closed subgroup is its closed image inside the original smooth group. -/
def smoothImageOverIso :
    H.carrier ≅ Over.mk (H.inclusion.left.ker.subschemeι ≫ E.group.hom) :=
  Over.isoMk (asIso H.inclusion.left.toImage) (by
    change H.inclusion.left.toImage ≫ H.inclusion.left.imageι ≫ E.group.hom = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact H.inclusion.w)

/-- Restricting the whole-curve ideal to the smooth group gives its full inclusion kernel. -/
theorem ideal_on_smoothGroup : H.ideal.comap E.inclusion.left = H.inclusion.left.ker := by
  let i := H.inclusion.left
  let j := E.inclusion.left
  let _ : IsClosedImmersion (i ≫ j) := H.curveMap_closed
  have hpb : IsPullback i (𝟙 _) j (i ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  change (i ≫ j).ker.comap j = i.ker
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rw [← Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom,
    hpb.isoPullback_hom_fst]

/-- Finite flat rank makes the full subgroup a Cartier divisor on the entire generalized curve. -/
theorem relativeCartier_of_noetherian_base [IsLocallyNoetherian S]
    [SmoothOfRelativeDimension 1 E.group.hom] :
    FCurve.RelativeEffectiveCartier E.curve.hom H.ideal := by
  refine ⟨?_, H.ideal_degree.2.1⟩
  apply FCurve.effectiveCartier_of_comap_of_support_subset H.ideal E.inclusion.left
  · rw [Scheme.IdealSheafData.range_subschemeι, ideal, Scheme.Hom.support_ker,
      H.curveMap.left.isClosedEmbedding.isClosed_range.closure_eq]
    rintro x ⟨y, rfl⟩
    exact ⟨H.inclusion.left y, rfl⟩
  · rw [ideal_on_smoothGroup]
    exact (FCurve.relativeEffectiveCartier_of_smooth_degree_noetherian_base
      E.group.hom H.inclusion.left.ker n (H.degree.of_overIso H.smoothImageOverIso)).1

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
