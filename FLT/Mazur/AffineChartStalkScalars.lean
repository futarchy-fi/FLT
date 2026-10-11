/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Structure coefficients in actual chart stalks

A chart over an affine base retains its specified coefficient homomorphism
on germs of sections on every open neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineChartStalkScalars

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Restricting a pulled-back section before taking its germ has no effect. -/
theorem germ_appLE {X Y : Scheme} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hU : U ≤ f ⁻¹ᵁ V) (x : X) (hx : x ∈ U) (s : Γ(Y, V)) :
    X.presheaf.germ U x hx (f.appLE V U hU s) =
      f.stalkMap x (Y.presheaf.germ V (f x) (hU hx) s) := by
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply]

/-- The original chart and structure morphism retain their coefficient map in the stalk. -/
theorem chart_scalar {X : Scheme} {R A : CommRingCat} (c : Spec A ⟶ X)
    (f : X ⟶ Spec R) (φ : R ⟶ A) (hc : c ≫ f = Spec.map φ)
    (U : X.Opens) (x : Spec A) (hx : c x ∈ U) (r : R) :
    c.stalkMap x (X.presheaf.germ U (c x) hx
      (f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso R).inv r))) =
        StructureSheaf.toStalk A x (φ r) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have he := Scheme.Hom.appLE_comp_appLE c f ⊤ U (c ⁻¹ᵁ U) (by simp) le_rfl
  rw [hc] at he
  simp only [Scheme.Hom.appLE, homOfLE_refl, CategoryTheory.op_id,
    (Spec A).presheaf.map_id, Category.comp_id] at he
  have he' := congrArg (fun g ↦ g ((Scheme.ΓSpecIso R).inv r)) he
  simp only [CommRingCat.comp_apply] at he'
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  rw [he']
  rw [TopCat.Presheaf.germ_res_apply]
  simp only [Scheme.Hom.preimage_top] at *
  have hn := congrArg (fun g ↦ g r) (Scheme.ΓSpecIso_inv_naturality φ)
  exact (congrArg ((Spec A).presheaf.germ ⊤ x trivial) hn.symm).trans (by rfl)

end FLT.Mazur.AffineChartStalkScalars
