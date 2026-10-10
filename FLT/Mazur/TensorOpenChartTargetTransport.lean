/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChart

/-!
# Original tensor charts under equality of target schemes

Transporting the target and its coefficient structure changes neither the
original tensor source nor its canonical map into the coefficient pullback.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.TensorOpenChart
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]
  {X Y : Scheme.{u}} (h : X = Y) (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of R))
  (hf : eqToHom h ≫ g = f) (i : Spec (.of A) ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))

include hf hi in
/-- Transport of a target retains the entire original affine coefficient square. -/
theorem target_structure :
    (i ≫ eqToHom h) ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [Category.assoc, hf, hi]

/-- The tensor chart is unchanged by transporting its target and the same coefficient square. -/
theorem chart_target_heq :
    HEq (chart (S := S) f i hi)
      (chart (S := S) g (i ≫ eqToHom h) (target_structure h f g hf i hi)) := by
  subst Y
  have H : g = f := by simpa only [eqToHom_refl, Category.id_comp] using hf
  cases H
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end FLT.Mazur.TensorOpenChart
