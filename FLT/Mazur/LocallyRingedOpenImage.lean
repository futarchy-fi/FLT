/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Locally ringed identification of an open immersion's actual image

Open immersions with the same image identify their original locally ringed
spaces. In particular, an affine chart identifies the restriction to its image,
including its sheaf, and not just the underlying topological subspace.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.LocallyRingedOpenImage
variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]

/-- Equal open images give an isomorphism of the original locally ringed spaces. -/
def isoOfRangeEq (h : Set.range f.base = Set.range g.base) : X ≅ Y :=
  { hom := LocallyRingedSpace.IsOpenImmersion.lift g f (le_of_eq h)
    inv := LocallyRingedSpace.IsOpenImmersion.lift f g (le_of_eq h.symm)
    hom_inv_id := by
      rw [← cancel_mono f, Category.assoc,
        LocallyRingedSpace.IsOpenImmersion.lift_fac,
        LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp]
    inv_hom_id := by
      rw [← cancel_mono g, Category.assoc,
        LocallyRingedSpace.IsOpenImmersion.lift_fac,
        LocallyRingedSpace.IsOpenImmersion.lift_fac, Category.id_comp] }

/-- The image identification commutes with the original immersions. -/
theorem isoOfRangeEq_hom_comp (h : Set.range f.base = Set.range g.base) :
    (isoOfRangeEq f g h).hom ≫ g = f :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac g f (le_of_eq h)

/-- The restriction to an actual open image is the domain as a locally ringed space. -/
def restrictIso (W : Opens Z) (h : Set.range f.base = (W : Set Z)) :
    Z.restrict W.isOpenEmbedding ≅ X :=
  isoOfRangeEq (Z.ofRestrict W.isOpenEmbedding) f (Subtype.range_val.trans h.symm)

end FLT.Mazur.LocallyRingedOpenImage
