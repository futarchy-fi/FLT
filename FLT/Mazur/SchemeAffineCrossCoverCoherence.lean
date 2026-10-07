/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverDescent

/-!
# Coherence of effective cross-cover comparisons

Faithful reconstruction transports the original cocycle to the effectively
descended comparisons on an affine base. The resulting maps have identity,
composition, and inverse laws, even when their covering maps into Y differ.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (a : Spec R ⟶ X) (b c d : Spec S ⟶ Y)
variable (wb : Spec.map φ ≫ a = b ≫ p) (wc : Spec.map φ ≫ a = c ≫ p)
variable (wd : Spec.map φ ≫ a = d ≫ p) (hφ : φ.hom.FaithfullyFlat)
variable [((pullback b).obj M).IsQuasicoherent] [((pullback c).obj M).IsQuasicoherent]
variable [((pullback d).obj M).IsQuasicoherent]
attribute [local irreducible] chartCrossCoverIso chartReconstruction chartSheaf transport

/-- The effective comparisons inherit the cocycle from the original geometric datum. -/
@[reassoc]
theorem chartCrossCoverIso_comp :
    (D.chartCrossCoverIso φ p a b c wb wc hφ).hom ≫
        (D.chartCrossCoverIso φ p a c d wc wd hφ).hom =
      (D.chartCrossCoverIso φ p a b d wb wd hφ).hom := by
  apply D.chartCrossCoverIso_unique φ p a b d wb wd hφ
  rw [Functor.map_comp, Category.assoc, D.chartCrossCoverIso_reconstruction,
    D.chartCrossCoverIso_reconstruction_assoc, D.transport_comp]

/-- Comparing a covering map with itself gives the identity on its descended sheaf. -/
@[simp]
theorem chartCrossCoverIso_self :
    D.chartCrossCoverIso φ p a b b wb wb hφ = Iso.refl _ := by
  apply Iso.ext
  symm
  apply D.chartCrossCoverIso_unique φ p a b b wb wb hφ
  rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp, D.transport_self,
    Iso.refl_hom, Category.comp_id]

/-- Reversing the covering maps gives the inverse effective comparison. -/
theorem chartCrossCoverIso_symm :
    D.chartCrossCoverIso φ p a c b wc wb hφ =
      (D.chartCrossCoverIso φ p a b c wb wc hφ).symm := by
  apply Iso.ext
  apply (cancel_epi (D.chartCrossCoverIso φ p a b c wb wc hφ).hom).mp
  rw [D.chartCrossCoverIso_comp, D.chartCrossCoverIso_self, Iso.refl_hom,
    Iso.symm_hom, Iso.hom_inv_id]

end FLT.Mazur.SchemeGeometricDescent.Data
