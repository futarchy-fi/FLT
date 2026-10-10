/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildeSemilinearMap
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Actual affine sheaf isomorphisms from module base change

A proved scalar-extension property of an original coefficient map gives an
isomorphism of actual pullback sheaves. Its normalization uses the original
pullback unit, so it can be compared on chart overlaps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.AffineTildeBaseChangeIso

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) (N : ModuleCat S)

/-- Restriction along the given ring map retains the target ring's scalar action. -/
instance restrictScalarTower :
    let _ := φ.hom.toAlgebra
    IsScalarTower R S ((ModuleCat.restrictScalars φ.hom).obj N) := by
  let _ := φ.hom.toAlgebra
  exact ⟨fun r s n ↦ mul_smul (φ.hom r) s n⟩

/-- A coefficient map exhibiting base change gives an actual affine sheaf isomorphism. -/
def iso (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N)
    (h : let _ := φ.hom.toAlgebra
      let _ := restrictScalarTower φ N
      IsBaseChange S g.hom) :
    (pullback (Spec.map φ)).obj (tilde M) ≅ tilde N := by
  let _ := φ.hom.toAlgebra
  exact (AffineModulePullbackSections.tildePullbackIso φ).symm.app M ≪≫
    (tilde.functor S).mapIso h.equiv.toModuleIso

/-- The constructed isomorphism is the map induced by the original coefficients. -/
lemma iso_hom (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N)
    (h : let _ := φ.hom.toAlgebra
      let _ := restrictScalarTower φ N
      IsBaseChange S g.hom) :
    (iso φ M N g h).hom = AffineTildeSemilinearMap.map φ M N g := by
  let _ := φ.hom.toAlgebra
  apply AffineTildeSemilinearMap.map_unique
  intro m
  have he := AffineTildePullbackMap.map_unit φ M N h.equiv.toModuleIso.hom m
  change (AffineTildePullbackMap.map φ M N h.equiv.toModuleIso.hom).app ⊤ _ = _
  refine he.trans ?_
  congr 1
  change h.equiv (1 ⊗ₜ[R] m) = g m
  rw [h.equiv_tmul, one_smul]

end FLT.Mazur.AffineTildeBaseChangeIso
