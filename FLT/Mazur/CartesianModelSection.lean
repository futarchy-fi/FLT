/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientSectionRecovery

/-!
# Sections on specified Cartesian models

A section lifts to any specified Cartesian refinement. If the original
family and section recover from that model, the lifted section recovers
the same original marking along the supplied comparison morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {W Y T S : Scheme.{u}} {c : W ⟶ Y} {v : W ⟶ T}
  {p : Y ⟶ S} {b : T ⟶ S} (h : IsPullback c v p b)
  (s : S ⟶ Y) (hs : s ≫ p = 𝟙 _)

/-- The model section lifted through the given Cartesian comparison. -/
def cartesianModelSection : T ⟶ W :=
  h.lift (b ≫ s) (𝟙 T) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

/-- The lifted section has the original model marking as its projection. -/
@[reassoc] theorem cartesianModelSection_projection :
    cartesianModelSection h s hs ≫ c = b ≫ s := IsPullback.lift_fst _ _ _ _

/-- The lifted marking remains a section of the refined model. -/
@[reassoc] theorem cartesianModelSection_over :
    cartesianModelSection h s hs ≫ v = 𝟙 T := IsPullback.lift_snd _ _ _ _

/-- The supplied original recovery map preserves the lifted model marking. -/
theorem cartesianModelSection_recovery {X B : Scheme.{u}}
    (r : X ⟶ B) (a : X ⟶ W) (g : B ⟶ T) (ha : a ≫ v = r ≫ g)
    (t : B ⟶ X) (ht : t ≫ r = 𝟙 B) (he : (g ≫ b) ≫ s = t ≫ a ≫ c) :
    g ≫ cartesianModelSection h s hs = t ≫ a := by
  apply h.hom_ext
  · rw [Category.assoc, cartesianModelSection_projection, ← Category.assoc, he]
    exact (Category.assoc t a c).symm
  · rw [Category.assoc, cartesianModelSection_over, Category.comp_id,
      Category.assoc, ha, ← Category.assoc, ht, Category.id_comp]

end FLT.Mazur.Approximation
