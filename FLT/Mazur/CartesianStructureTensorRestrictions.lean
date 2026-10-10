/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianStructureSections
public import FLT.Mazur.ArtinianRelativeSectionCriterion

/-!
# Structure tensors and the actual affine-cover augmentation

The chart comparison respects restrictions on every tensor. A tensor with
unit function gives precisely the restricted structural scalar; this will
identify the augmentation of the tensor complex with actual constants.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.CartesianStructureSections
open Chow FCurve ArtinianSectionKernel ArtinianRelativeSectionCriterion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g)

/-- Tensoring an actual restriction commutes with the chart comparison. -/
lemma comparison_lTensor {U V : X.Opens} (i : U ≤ V) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ t : Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections (structureModule X) f.appTop.hom V,
      comparison h U
          (AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
            (baseRestriction (structureModule X) f.appTop.hom i) t) =
        baseRestriction (structureModule P) q.appTop.hom
          ((TopologicalSpace.Opens.map p.base).map (homOfLE i)).le (comparison h V t) := by
  dsimp only
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b m => exact (comparison_restrict h i b m).symm

/-- The augmentation at the unit is the original unit function on each chart. -/
lemma comparison_chartMap_one {ι : Type} (U : ι → X.Opens) (i : ι) (b : Γ(T, ⊤)) :
    let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    comparison h (U i)
        (b ⊗ₜ[Γ(S, ⊤)] chartMap (structureModule X) f.appTop.hom U (scalarSections f) 1 i) =
      baseRestriction (structureModule P) q.appTop.hom le_top (scalarSections q b) := by
  dsimp only
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  rw [comparison_tmul]
  change P.presheaf.map _ (q.appTop b) *
    p.app (U i) (X.presheaf.map _ (f.appTop 1)) = P.presheaf.map _ (q.appTop b)
  rw [map_one, map_one, map_one, mul_one]
  rfl

end FLT.Mazur.CartesianStructureSections
