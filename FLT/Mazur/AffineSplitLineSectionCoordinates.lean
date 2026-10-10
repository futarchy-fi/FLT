/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSplitLineCoordinates
public import FLT.Mazur.AffineFreeSheafCoordinateNormalization

/-!
# Actual sections of recovered split-line coordinates

Normalize the affine tilde unit on the scalar source and the vector target.
The recovered vector is the actual image of the chosen source frame at one.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.AffineSplitLineCoordinates
open AffineModuleGlobalSections AffineFreeSheafCoordinates FreeSheafSectionCoordinates FCurve
variable (X : Scheme.{u}) [IsAffine X]

/-- The affine unit expressed in the original finite vector coordinates. -/
def vectorSectionIso (ι : Type u) [Finite ι] :
    ModuleCat.of Γ(X, ⊤) (ι → Γ(X, ⊤)) ≅
      (sections X).obj (SheafOfModules.free ι) :=
  asIso ((affineAdjunction X).unit.app _) ≪≫ (sections X).mapIso (vectorFreeIso X ι)

/-- Actual vector sections are finite-support realization in the canonical basis. -/
lemma vectorSectionIso_apply {ι : Type u} [Finite ι] (v : ι → Γ(X, ⊤)) :
    (vectorSectionIso X ι).hom v =
      realize X ι ((Finsupp.linearEquivFunOnFinite Γ(X, ⊤) Γ(X, ⊤) ι).symm v) := by
  rw [← sectionIso_hom_eq_realize]
  change ((affineAdjunction X).unit.app _ ≫
    (sections X).map ((affineTilde X).map
      (Finsupp.linearEquivFunOnFinite Γ(X, ⊤) Γ(X, ⊤) ι).symm.toModuleIso.hom) ≫
        (sections X).map (freeIso X ι).hom) v = _
  have h := (affineAdjunction X).unit.naturality
    (Finsupp.linearEquivFunOnFinite Γ(X, ⊤) Γ(X, ⊤) ι).symm.toModuleIso.hom
  dsimp only [Functor.id_map, Functor.comp_map] at h
  rw [← Category.assoc, ← h]
  rfl

variable {X} {L : X.Modules} (e : L ≅ structureModule X)

/-- The scalar affine unit is the original frame section at one. -/
lemma sourceIso_unit_one :
    (sourceIso e).hom.app ⊤ ((affineAdjunction X).unit.app _ (1 : Γ(X, ⊤))) =
      e.inv.app ⊤ (1 : Γ(X, ⊤)) := by
  change e.inv.app ⊤ ((modulePullbackUnitIso X.isoSpec.hom).hom.app ⊤
    (((pullback X.isoSpec.hom).map tildeSelf.hom).app ⊤
      (pullGlobal X.isoSpec.hom _ (tilde.toOpen _ ⊤ (1 : Γ(X, ⊤)))))) = _
  rw [pullGlobal_naturality, tilde_toOpen_one]
  change e.inv.app ⊤ ((modulePullbackUnitIso X.isoSpec.hom).hom.app ⊤
    (pullGlobal X.isoSpec.hom _ (1 : Γ(Spec Γ(X, ⊤), ⊤)))) = _
  have h : (modulePullbackUnitIso X.isoSpec.hom).hom.app ⊤
      (pullGlobal X.isoSpec.hom (structureModule (Spec Γ(X, ⊤)))
        (1 : Γ(Spec Γ(X, ⊤), ⊤))) = X.isoSpec.hom.appTop 1 :=
    modulePullbackUnitIso_unit X.isoSpec.hom ⊤ (1 : Γ(Spec Γ(X, ⊤), ⊤))
  simpa only [map_one] using congrArg (e.inv.app ⊤) h

attribute [local irreducible] affineTilde sourceIso vectorFreeIso

/-- Recovered vector coordinates realize the actual image of the chosen sheaf frame. -/
lemma vectorSectionIso_vector {ι : Type u} [Finite ι]
    (s : L ⟶ SheafOfModules.free ι) :
    (vectorSectionIso X ι).hom (vector e s) = s.app ⊤ (e.inv.app ⊤ (1 : Γ(X, ⊤))) := by
  have h := (affineAdjunction X).unit.naturality (ModuleCat.ofHom (inclusion e s))
  dsimp only [Functor.id_map, Functor.comp_map] at h
  have hr := congrArg ((sections X).map) (inclusion_reconstruct e s)
  rw [Functor.map_comp, Functor.map_comp] at hr
  have hn := congrArg (fun k ↦ k (1 : Γ(X, ⊤)))
    (show ModuleCat.ofHom (inclusion e s) ≫
      ((affineAdjunction X).unit.app _ ≫ (sections X).map (vectorFreeIso X ι).hom) =
        (affineAdjunction X).unit.app _ ≫
          ((sections X).map (sourceIso e).hom ≫ (sections X).map s) from by
      rw [← Category.assoc, h, Category.assoc, hr])
  change (vectorSectionIso X ι).hom (vector e s) =
    s.app ⊤ ((sourceIso e).hom.app ⊤ ((affineAdjunction X).unit.app _ (1 : Γ(X, ⊤)))) at hn
  rw [sourceIso_unit_one] at hn
  exact hn

end FLT.Mazur.AffineSplitLineCoordinates
