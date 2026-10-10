/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafInternalHom
public import FLT.Mazur.IdealModuleSheaf

/-!
# Scalars as local endomorphisms

The canonical map to the internal endomorphism sheaf sends a function to
multiplication by its restrictions. On a trivial line it is invertible.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
open ModuleSheafInternalHom
variable {X : Scheme.{u}} (M : X.Modules)

/-- Scalar multiplication, as a morphism to the actual internal endomorphism sheaf. -/
def scalarMap : structureModule X ⟶ sheaf M M :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun (r : Γ(X, U.unop)) ↦ r • (𝟙 (M.over U.unop))
          map_zero' := by exact zero_smul Γ(X, U.unop) _
          map_add' := fun r s ↦ by
            change Γ(X, U.unop) at r s
            exact add_smul r s _ }
      naturality := fun U V i ↦ by
        ext r : 2
        apply sections_ext
        intro W s
        change X.presheaf.map W.hom.op (X.presheaf.map i r) • s =
          X.presheaf.map (W.hom ≫ i.unop).op r • s
        rw [op_comp, Functor.map_comp]
        rfl }
    (fun U r s ↦ by
      change Γ(X, U.unop) at r s
      change (r * s) • (𝟙 (M.over U.unop)) = r • (s • (𝟙 (M.over U.unop)))
      exact mul_smul r s _)⟩

/-- The scalar morphism acts on every subopen by restricted multiplication. -/
lemma scalarMap_app (U : X.Opens) (r : Γ(X, U)) (V : Over U) (s : Γ(M, V.left)) :
    app M M ((scalarMap M).app U r) V s = X.presheaf.map V.hom.op r • s := rfl

/-- A local endomorphism of the structure module is multiplication by its value at one. -/
lemma unit_end_app {U : X.Opens} (φ : Sections (structureModule X) (structureModule X) U)
    (V : Over U) (s : Γ(X, V.left)) :
    app _ _ φ V s = X.presheaf.map V.hom.op
      (app _ _ φ (Over.mk (𝟙 U)) (1 : Γ(X, U))) * s := by
  have hn := app_naturality _ _ φ (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)) (1 : Γ(X, U))
  change app _ _ φ V (X.presheaf.map V.hom.op 1) =
    X.presheaf.map V.hom.op (app _ _ φ (Over.mk (𝟙 U)) (1 : Γ(X, U))) at hn
  rw [map_one] at hn
  rw [← hn, mul_comm]
  simpa only [smul_eq_mul, mul_one] using
    (app _ _ φ V).map_smul s (1 : Γ(X, V.left))

/-- Scalars classify local endomorphisms of the structure module. -/
lemma unit_bijective (U : X.Opens) :
    Function.Bijective ((scalarMap (structureModule X)).app U) := by
  constructor
  · intro r s h
    change Γ(X, U) at r s
    have hh := congrArg (fun (φ : Sections (structureModule X) (structureModule X) U) ↦
      app _ _ φ (Over.mk (𝟙 U)) (1 : Γ(X, U))) h
    change X.presheaf.map (𝟙 U).op r * 1 = X.presheaf.map (𝟙 U).op s * 1 at hh
    simpa using hh
  · intro φ
    refine ⟨app _ _ φ (Over.mk (𝟙 U)) (1 : Γ(X, U)), ?_⟩
    apply sections_ext
    intro V s
    exact (unit_end_app φ V s).symm

end FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
