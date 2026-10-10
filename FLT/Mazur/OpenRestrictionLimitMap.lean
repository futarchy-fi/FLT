/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenRestrictionClosed

/-!
# Structure maps of a restricted inverse diagram

All inverse images of a fixed open map naturally to that original open.
The restricted limit cone retains exactly the restriction of its original
projection, giving a fixed target for closed-immersion descent.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  (i : I) (U : (D.obj i).Opens)

/-- The restricted inverse system has a natural map to its original open. -/
def opensDiagramToOpen : opensDiagram D i U ⟶ (Functor.const (Over i)).obj U.toScheme where
  app j := D.map j.hom ∣_ U
  naturality {j k} g := by
    apply (cancel_mono U.ι).mp
    change ((D.map g.left).resLE _ _ _ ≫ D.map k.hom ∣_ U) ≫ U.ι =
      ((D.map j.hom ∣_ U) ≫ 𝟙 _) ≫ U.ι
    simp only [Category.comp_id, Category.assoc, morphismRestrict_ι,
      Scheme.Hom.resLE_comp_ι_assoc, ← D.map_comp, Over.w g]

/-- The natural structural maps are exactly the restrictions of the original transitions. -/
theorem opensDiagramToOpen_app (j : Over i) :
    (opensDiagramToOpen D i U).app j = D.map j.hom ∣_ U := rfl

/-- Composition with the restricted cone recovers the restriction of its original projection. -/
@[reassoc] theorem opensCone_toOpen (c : Cone D) (j : Over i) :
    (opensCone D c i U).π.app j ≫ (opensDiagramToOpen D i U).app j =
      c.π.app i ∣_ U := by
  apply (cancel_mono U.ι).mp
  change ((c.π.app j.left).resLE _ _ _ ≫ D.map j.hom ∣_ U) ≫ U.ι = _
  simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, Cone.w]
  exact (morphismRestrict_ι (c.π.app i) U).symm

end FLT.Mazur.Approximation
