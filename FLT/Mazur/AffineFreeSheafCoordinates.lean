/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleGlobalSections
public import FLT.Mazur.ModuleGlobalEvaluationPullback

/-!
# Linear coordinates for actual affine free sheaf isomorphisms

Full faithfulness of affine tilde recovers a genuine free-module linear
isomorphism from a free sheaf isomorphism. Recovery preserves composition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineFreeSheafCoordinates
open AffineModuleGlobalSections
variable (S : Scheme.{u}) [IsAffine S]

/-- Canonical identification of affine tilde of a free module with the free sheaf. -/
def freeIso (ι : Type u) :
    (affineTilde S).obj (ModuleCat.of Γ(S, ⊤) (ι →₀ Γ(S, ⊤))) ≅ SheafOfModules.free ι :=
  (pullback S.isoSpec.hom).mapIso (tildeFinsupp ι) ≪≫
    ModuleGlobalEvaluationPullback.freeIso S.isoSpec.hom ι

/-- The actual free-module isomorphism recovered from a free sheaf isomorphism. -/
def coordinatesIso {ι κ : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ) :
    ModuleCat.of Γ(S, ⊤) (ι →₀ Γ(S, ⊤)) ≅ ModuleCat.of Γ(S, ⊤) (κ →₀ Γ(S, ⊤)) :=
  (affineTilde S).preimageIso (freeIso S ι ≪≫ e ≪≫ (freeIso S κ).symm)

/-- Reconstruction recovers the original sheaf coordinate change. -/
lemma coordinatesIso_reconstruct {ι κ : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ) :
    (affineTilde S).mapIso (coordinatesIso S e) =
      freeIso S ι ≪≫ e ≪≫ (freeIso S κ).symm := by
  apply Iso.ext
  exact (affineTilde S).map_preimage _

/-- Recovery sends the identity sheaf map to the identity module map. -/
lemma coordinatesIso_refl (ι : Type u) :
    coordinatesIso S (Iso.refl (SheafOfModules.free ι)) = Iso.refl _ := by
  apply Iso.ext
  apply (affineTilde S).map_injective
  simp [coordinatesIso, Functor.preimageIso]

/-- Recovery preserves composition of genuine sheaf coordinate changes. -/
lemma coordinatesIso_trans {ι κ ν : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (d : (SheafOfModules.free κ : S.Modules) ≅ SheafOfModules.free ν) :
    coordinatesIso S (e ≪≫ d) = coordinatesIso S e ≪≫ coordinatesIso S d := by
  apply Iso.ext
  apply (affineTilde S).map_injective
  simp [coordinatesIso, Functor.preimageIso]

/-- Recovery preserves inverse coordinate changes. -/
lemma coordinatesIso_symm {ι κ : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ) :
    coordinatesIso S e.symm = (coordinatesIso S e).symm := by
  apply Iso.ext
  apply (affineTilde S).map_injective
  simp [coordinatesIso, Functor.preimageIso]

/-- The recovered coordinate change as a linear equivalence of coefficient vectors. -/
def coordinates {ι κ : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ) :
    (ι →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (κ →₀ Γ(S, ⊤)) :=
  (coordinatesIso S e).toLinearEquiv

/-- Linear coordinate recovery respects identity. -/
lemma coordinates_refl (ι : Type u) :
    coordinates S (Iso.refl (SheafOfModules.free ι)) = LinearEquiv.refl _ _ := by
  rw [coordinates, coordinatesIso_refl]
  rfl

/-- Linear coordinate recovery respects composition. -/
lemma coordinates_trans {ι κ ν : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ)
    (d : (SheafOfModules.free κ : S.Modules) ≅ SheafOfModules.free ν) :
    coordinates S (e ≪≫ d) = (coordinates S e).trans (coordinates S d) := by
  rw [coordinates, coordinatesIso_trans]
  rfl

/-- Linear coordinate recovery respects inverse. -/
lemma coordinates_symm {ι κ : Type u}
    (e : (SheafOfModules.free ι : S.Modules) ≅ SheafOfModules.free κ) :
    coordinates S e.symm = (coordinates S e).symm := by
  rw [coordinates, coordinatesIso_symm]
  rfl

end FLT.Mazur.AffineFreeSheafCoordinates
