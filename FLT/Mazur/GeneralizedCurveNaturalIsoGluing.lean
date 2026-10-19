/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveDirectedIsoGluing
public import FLT.Mazur.GeneralizedCurveDirectedNaturality

/-!
# Full isomorphism descent from a single refinement identity

Naturality of the supplied isomorphisms forces naturality of their inverses.
The resulting global comparison recovers the complete specified chart family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) [Category* C.I₀] [C.LocallyDirected]
  {E F : GeneralizedEllipticCurve S}
  (a : ∀ i, E.baseChange (C.f i) ≅ F.baseChange (C.f i))
  (ha : ∀ {i j : C.I₀} (h : i ⟶ j),
    coverRefinementIso C E h ≪≫ (baseChangeFunctor (C.trans h)).mapIso (a j) =
      a i ≪≫ coverRefinementIso C F h)

include ha in
/-- Inverse comparisons automatically satisfy the full refinement identity. -/
theorem inverse_refinement {i j : C.I₀} (h : i ⟶ j) :
    coverRefinementIso C F h ≪≫ (baseChangeFunctor (C.trans h)).mapIso (a j).symm =
      (a i).symm ≪≫ coverRefinementIso C E h := by
  rw [Functor.mapIso_symm]
  calc
    _ = (a i).symm ≪≫ (a i ≪≫ coverRefinementIso C F h) ≪≫
        ((baseChangeFunctor (C.trans h)).mapIso (a j)).symm := by simp
    _ = _ := by rw [← ha h]; simp

/-- Full comparisons glue using only their actual forward refinement equations. -/
def glueIsoOfRefinement : E ≅ F :=
  glueIso C a
    (curve_compatible_of_refinement C (fun i ↦ (a i).hom)
      (fun h ↦ congrArg Iso.hom (ha h)))
    (group_compatible_of_refinement C (fun i ↦ (a i).hom)
      (fun h ↦ congrArg Iso.hom (ha h)))
    (curve_compatible_of_refinement C (fun i ↦ (a i).inv)
      (fun h ↦ congrArg Iso.hom (inverse_refinement C a ha h)))
    (group_compatible_of_refinement C (fun i ↦ (a i).inv)
      (fun h ↦ congrArg Iso.hom (inverse_refinement C a ha h)))

/-- The glued isomorphism restricts to every supplied full comparison. -/
theorem glueIsoOfRefinement_map (i : C.I₀) :
    (baseChangeFunctor (C.f i)).mapIso (glueIsoOfRefinement C a ha) = a i := by
  apply Iso.ext
  exact glueHom_map C (fun i ↦ (a i).hom)
    (curve_compatible_of_refinement C (fun i ↦ (a i).hom)
      (fun h ↦ congrArg Iso.hom (ha h)))
    (group_compatible_of_refinement C (fun i ↦ (a i).hom)
      (fun h ↦ congrArg Iso.hom (ha h))) i

include ha in
/-- The full refinement equations give existence and uniqueness on the original families. -/
theorem glueIsoOfRefinement_unique :
    ∃! e : E ≅ F, ∀ i, (baseChangeFunctor (C.f i)).mapIso e = a i := by
  refine ⟨glueIsoOfRefinement C a ha, glueIsoOfRefinement_map C a ha, fun e he ↦ ?_⟩
  apply Iso.ext
  apply hom_ext_of_cover C
  intro i
  exact congrArg Iso.hom ((he i).trans (glueIsoOfRefinement_map C a ha i).symm)

end FLT.Mazur.GeneralizedEllipticCurve
