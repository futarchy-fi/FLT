/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveDirectedGluing

/-!
# Gluing full curve isomorphisms on a directed base cover

Compatible actual comparisons and their inverses give an isomorphism of the
original generalized curves. Both inverse laws descend from the given cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] glueHom
variable {S : Scheme} (C : S.OpenCover) [Category* C.I₀] [C.LocallyDirected]
  {E F : GeneralizedEllipticCurve S}
  (a : ∀ i, E.baseChange (C.f i) ≅ F.baseChange (C.f i))
  (hc : OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).hom.curve))
  (hg : OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).hom.group))
  (kc : OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).inv.curve))
  (kg : OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).inv.group))

/-- The complete original comparisons descend to a full global isomorphism. -/
def glueIso : E ≅ F where
  hom := glueHom C (fun i ↦ (a i).hom) hc hg
  inv := glueHom C (fun i ↦ (a i).inv) kc kg
  hom_inv_id := by
    apply hom_ext_of_cover C
    intro i
    change (baseChangeFunctor (C.f i)).map (_ ≫ _) =
      (baseChangeFunctor (C.f i)).map (𝟙 E)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    change baseChangeMap _ _ ≫ baseChangeMap _ _ = _
    rw [glueHom_map, glueHom_map, Iso.hom_inv_id]
    rfl
  inv_hom_id := by
    apply hom_ext_of_cover C
    intro i
    change (baseChangeFunctor (C.f i)).map (_ ≫ _) =
      (baseChangeFunctor (C.f i)).map (𝟙 F)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    change baseChangeMap _ _ ≫ baseChangeMap _ _ = _
    rw [glueHom_map, glueHom_map, Iso.inv_hom_id]
    rfl

/-- Each supplied full comparison is recovered exactly, including its automorphisms. -/
theorem glueIso_map (i : C.I₀) :
    (baseChangeFunctor (C.f i)).mapIso (glueIso C a hc hg kc kg) = a i := by
  apply Iso.ext
  exact glueHom_map C (fun i ↦ (a i).hom) hc hg i

include hc hg kc kg in
/-- A compatible family has exactly one original full curve isomorphism. -/
theorem glueIso_unique :
    ∃! e : E ≅ F, ∀ i, (baseChangeFunctor (C.f i)).mapIso e = a i := by
  refine ⟨glueIso C a hc hg kc kg, glueIso_map C a hc hg kc kg, fun e he ↦ ?_⟩
  apply Iso.ext
  apply hom_ext_of_cover C
  intro i
  exact congrArg Iso.hom ((he i).trans (glueIso_map C a hc hg kc kg i).symm)

end FLT.Mazur.GeneralizedEllipticCurve
