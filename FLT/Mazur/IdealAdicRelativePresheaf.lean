/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeRestriction

/-!
# Relative graded algebras on the affine basis

The actual tensor restrictions satisfy the functor laws. Their quotient maps
form a natural transformation onto the actual graded coefficient presheaf,
with a surjection at every affine chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open FLT.Mazur.IdealAdicGradedSections
open scoped TensorProduct

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- Relative tensor restriction along an identity fixes every tensor. -/
lemma relativeRestriction_id (U : X.affineOpens) :
    let := closedBaseAlgebra J f U.1
    relativeRestriction J f (𝟙 U.1) = AlgHom.id _ (RelativeAlgebra J f U) := by
  let := closedBaseAlgebra J f U.1
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a r =>
    rw [relativeRestriction_tmul]
    change a ⊗ₜ[Γ(Y, ⊤)]
      ((J.comap f).subscheme.presheaf.map (𝟙 _)) r = a ⊗ₜ[Γ(Y, ⊤)] r
    congr 1
    exact ConcreteCategory.congr_hom
      ((J.comap f).subscheme.presheaf.map_id _) r

omit [IsLocallyNoetherian X] [IsAffine Y] in
/-- Relative tensor restrictions compose along affine inclusions. -/
lemma relativeRestriction_comp {U V W : X.affineOpens} (i : U.1 ⟶ V.1)
    (j : V.1 ⟶ W.1) :
    let := closedBaseAlgebra J f U.1
    let := closedBaseAlgebra J f V.1
    let := closedBaseAlgebra J f W.1
    (relativeRestriction J f i).comp (relativeRestriction J f j) =
      relativeRestriction J f (i ≫ j) := by
  let := closedBaseAlgebra J f U.1
  let := closedBaseAlgebra J f V.1
  let := closedBaseAlgebra J f W.1
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a r =>
    change relativeRestriction J f i (relativeRestriction J f j (a ⊗ₜ[Γ(Y, ⊤)] r)) = _
    rw [relativeRestriction_tmul, relativeRestriction_tmul, relativeRestriction_tmul]
    congr 1
    exact (ConcreteCategory.congr_hom
      ((J.comap f).subscheme.presheaf.map_comp
        ((TopologicalSpace.Opens.map (J.comap f).subschemeι.base).map j).op
        ((TopologicalSpace.Opens.map (J.comap f).subschemeι.base).map i).op) r).symm

/-- The relative graded tensor algebras form a presheaf on the affine basis. -/
def relativeAffinePresheaf : X.affineOpensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := let := closedBaseAlgebra J f U.unop.1
    CommRingCat.of (RelativeAlgebra J f U.unop)
  map i := CommRingCat.ofHom (relativeRestriction J f (homOfLE i.unop.le)).toRingHom
  map_id U := by
    exact congrArg (fun h ↦ CommRingCat.ofHom h.toRingHom)
      (relativeRestriction_id J f U.unop)
  map_comp i j := by
    exact (congrArg (fun h ↦ CommRingCat.ofHom h.toRingHom)
      (relativeRestriction_comp J f (homOfLE j.unop.le) (homOfLE i.unop.le))).symm

/-- The actual coefficient rings restricted to the affine basis. -/
def coefficientAffinePresheaf : X.affineOpensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (IdealAdicGradedSections.Sections (J.comap f) U.unop.1)
  map i := CommRingCat.ofHom (restrictRingHom (J.comap f) _ (homOfLE i.unop.le))
  map_id U := congrArg CommRingCat.ofHom (restrict_id (J.comap f) U.unop.1)
  map_comp i j := (congrArg CommRingCat.ofHom
    (restrict_comp (J.comap f) (homOfLE j.unop.le) (homOfLE i.unop.le))).symm

/-- The actual quotient maps form a morphism of presheaves on the affine basis. -/
def relativeAffineQuotient : relativeAffinePresheaf J f ⟶ coefficientAffinePresheaf J f where
  app U :=
    let := closedBaseAlgebra J f U.unop.1
    let := localBaseAlgebra J f U.unop.1
    CommRingCat.ofHom (relativeMap J f U.unop).toRingHom
  naturality U V i := by
    ext x
    exact (relativeMap_restrict J f (homOfLE i.unop.le) x).symm

/-- Every component of the relative affine quotient is surjective. -/
lemma relativeAffineQuotient_surjective (U : X.affineOpensᵒᵖ) :
    Function.Surjective ((relativeAffineQuotient J f).app U) :=
  relativeMap_surjective J f U.unop

end FLT.Mazur.IdealAdicGradedPullback
