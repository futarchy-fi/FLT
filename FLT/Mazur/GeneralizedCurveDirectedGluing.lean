/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCoverMorphism

/-!
# Gluing full generalized-curve maps over directed base covers

Both constituent relative maps glue from their actual refinement equations.
All group and full-curve action conditions descend, and the resulting morphism
recovers the supplied local morphisms uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) [Category* C.I₀] [C.LocallyDirected]
  {E F : GeneralizedEllipticCurve S}
  (a : ∀ i, E.baseChange (C.f i) ⟶ F.baseChange (C.f i))
  (hc : OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).curve))
  (hg : OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).group))

/-- The glued morphism retains the complete generalized-curve structure. -/
def glueHom : E ⟶ F :=
  homOfCover C
    (OverDirectedCoverGluing.glue C (fun i ↦ (a i).curve) hc)
    (OverDirectedCoverGluing.glue C (fun i ↦ (a i).group) hg) a
    (OverDirectedCoverGluing.glue_map C (fun i ↦ (a i).curve) hc)
    (OverDirectedCoverGluing.glue_map C (fun i ↦ (a i).group) hg)

/-- Restriction recovers each specified local full morphism. -/
theorem glueHom_map (i : C.I₀) : baseChangeMap (C.f i) (glueHom C a hc hg) = a i :=
  homOfCover_map C _ _ a _ _ i

include hc hg in
/-- Compatible local maps descend uniquely in the full category. -/
theorem glueHom_unique : ∃! f : E ⟶ F, ∀ i, baseChangeMap (C.f i) f = a i := by
  refine ⟨glueHom C a hc hg, glueHom_map C a hc hg, fun f hf ↦ ?_⟩
  exact hom_ext_of_cover C f _ (fun i ↦ (hf i).trans (glueHom_map C a hc hg i).symm)

end FLT.Mazur.GeneralizedEllipticCurve
