/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSourcePullbackSections

/-!
# The canonical tensor comparison is invertible on affine source opens

Transport the affine chart isomorphism through the actual coordinate and
section restrictions. The result applies to the original source-open map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings

universe u

namespace FLT.Mazur.ModuleSourceSectionBaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Coordinate restriction from an ambient open to its open subscheme is base-linear. -/
def scalarChartEquiv (U : X.Opens) :
    (ModuleCat.restrictScalars (scalarMap f U)).obj (ModuleCat.of _ Γ(X, U)) ≃ₗ[Γ(Y, ⊤)]
      (ModuleCat.restrictScalars (U.ι ≫ f).appTop.hom).obj
        (ModuleCat.of _ Γ(U, ⊤)) :=
  LinearEquiv.ofBijective
    ({ toFun := X.presheaf.map (eqToHom U.ι_image_top).op
       map_add' := map_add _
       map_smul' := fun r s ↦ by
         change X.presheaf.map (eqToHom U.ι_image_top).op
           (scalarMap f U r * (show Γ(X, U) from s)) =
           (U.ι ≫ f).appTop r *
             (show Γ(U, ⊤) from X.presheaf.map (eqToHom U.ι_image_top).op s)
         rw [map_mul]
         congr 1
         change X.presheaf.map _ (X.presheaf.map _ (f.appTop r)) =
           X.presheaf.map _ (f.appTop r)
         rw [← Functor.map_comp_apply]
         rfl } :
      (ModuleCat.restrictScalars (scalarMap f U)).obj (ModuleCat.of _ Γ(X, U)) →ₗ[Γ(Y, ⊤)]
        (ModuleCat.restrictScalars (U.ι ≫ f).appTop.hom).obj (ModuleCat.of _ Γ(U, ⊤)))
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom U.ι_image_top).op))

/-- The tensor coordinate comparison changes only the actual source scalar. -/
def tensorChartEquiv (U : X.Opens) :
    (ModuleCat.extendScalars (scalarMap f U)).obj (M.val.obj (op ⊤)) ≃+
      (ModuleCat.extendScalars (U.ι ≫ f).appTop.hom).obj (M.val.obj (op ⊤)) :=
  (TensorProduct.congr (scalarChartEquiv f U) (LinearEquiv.refl Γ(Y, ⊤)
    (M.val.obj (op ⊤)))).toAddEquiv

/-- The tensor coordinate comparison preserves pure tensors. -/
lemma tensorChartEquiv_tmul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, ⊤)) :
    tensorChartEquiv f M U (r ⊗ₜ[Γ(Y, ⊤),scalarMap f U] m) =
      (show Γ(U, ⊤) from X.presheaf.map (eqToHom U.ι_image_top).op r)
        ⊗ₜ[Γ(Y, ⊤),(U.ι ≫ f).appTop.hom] m := rfl

/-- The chart section comparison is the actual restriction, including its equality transport. -/
def sectionChartEquiv (U : X.Opens) :
    Γ((pullback f).obj M, U) ≃+ Γ(((pullback f).obj M).restrict U.ι, ⊤) :=
  CategoryTheory.Iso.addCommGroupIsoToAddEquiv
    (((pullback f).obj M).presheaf.mapIso (eqToIso U.ι_image_top).op)

variable [IsAffine Y] [M.IsQuasicoherent]

/-- The canonical comparison agrees with the affine chart isomorphism on every tensor. -/
lemma comparison_chart (U : X.affineOpens)
    (t : (ModuleCat.extendScalars (scalarMap f U.1)).obj (M.val.obj (op ⊤))) :
    sectionChartEquiv f M U.1 (comparison f M U.1 t) =
      (AffineSourcePullbackSections.sectionsIso f U.1.ι M).hom
        (tensorChartEquiv f M U.1 t) := by
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul r m =>
    rw [tensorChartEquiv_tmul, AffineSourcePullbackSections.sectionsIso_open_tmul,
      comparison_tmul]
    change ((pullback f).obj M).presheaf.map (eqToHom U.1.ι_image_top).op
      ((show Γ(X, U.1) from r) • (show Γ((pullback f).obj M, U.1) from unitMap f M U.1 m)) = _
    rw [map_smul]
    have h := ((pullback f).obj M).smul_restrictAppIso_hom_apply U.1.ι ⊤
      (show Γ(U.1, ⊤) from X.presheaf.map (eqToHom U.1.ι_image_top).op r)
      (show Γ(((pullback f).obj M).restrict U.1.ι, ⊤) from
        ((pullback f).obj M).presheaf.map (eqToHom U.1.ι_image_top).op
          (unitMap f M U.1 m))
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at h
    exact h.symm

/-- The original tensor comparison is an isomorphism on every affine source open. -/
lemma comparison_isIso (U : X.affineOpens) : IsIso (comparison f M U.1) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply ((sectionChartEquiv f M U.1).bijective.of_comp_iff' _).mp
  have h : (sectionChartEquiv f M U.1) ∘ (comparison f M U.1) =
      (AffineSourcePullbackSections.sectionsIso f U.1.ι M).hom ∘
        (tensorChartEquiv f M U.1) := funext (comparison_chart f M U)
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso
    (AffineSourcePullbackSections.sectionsIso f U.1.ι M).hom).comp
      (tensorChartEquiv f M U.1).bijective

end FLT.Mazur.ModuleSourceSectionBaseChange
