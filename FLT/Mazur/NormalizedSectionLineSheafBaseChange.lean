/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NormalizedSectionLineSheaf
public import FLT.Mazur.AffineTildeSemilinearNaturality
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Base change preserves the actual section-line inclusion

For finitely many coordinates, the ambient coordinate sheaf also commutes
with scalar extension. The line comparison intertwines the actual inclusions,
so it identifies sheaf subobjects, including on affine localization charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.NormalizedSectionLine
variable {R S : Type u} [CommRing R] [CommRing S] (ι : Type u)

/-- Extend each coordinate of the ambient vector module. -/
def vectorCoefficientMap (φ : R →+* S) :
    ModuleCat.of R (ι → R) ⟶ (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (ι → S)) :=
  ModuleCat.ofHom (X := ι → R)
    (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (ι → S)))
    { toFun v j := φ (v j)
      map_add' v w := funext fun j ↦ φ.map_add (v j) (w j)
      map_smul' r v := funext fun j ↦ φ.map_mul r (v j) }

/-- Finite coordinate modules commute with scalar extension through the actual coefficient map. -/
lemma vectorCoefficientMap_isBaseChange [Finite ι] (φ : R →+* S) :
    let _ := φ.toAlgebra
    let _ := AffineTildeBaseChangeIso.restrictScalarTower (CommRingCat.ofHom φ)
      (ModuleCat.of S (ι → S))
    IsBaseChange S (vectorCoefficientMap ι φ).hom := by
  let _ := φ.toAlgebra
  let _ := AffineTildeBaseChangeIso.restrictScalarTower (CommRingCat.ofHom φ)
    (ModuleCat.of S (ι → S))
  exact IsBaseChange.pi (fun _ : ι ↦ Algebra.linearMap R S)
    (fun _ ↦ IsBaseChange.linearMap R S)

/-- Base change of the finite ambient coordinate sheaf. -/
def vectorSheafBaseChange [Finite ι] (φ : R →+* S) :
    (pullback (Spec.map (CommRingCat.ofHom φ))).obj (tilde (ModuleCat.of R (ι → R))) ≅
      tilde (ModuleCat.of S (ι → S)) :=
  AffineTildeBaseChangeIso.iso (CommRingCat.ofHom φ) _ _ (vectorCoefficientMap ι φ)
    (vectorCoefficientMap_isBaseChange ι φ)

/-- The ambient comparison retains the original coordinate coefficient map. -/
lemma vectorSheafBaseChange_hom [Finite ι] (φ : R →+* S) :
    (vectorSheafBaseChange ι φ).hom =
      AffineTildeSemilinearMap.map (CommRingCat.ofHom φ) _ _ (vectorCoefficientMap ι φ) :=
  AffineTildeBaseChangeIso.iso_hom _ _ _ _ _

attribute [local irreducible] sheafBaseChange vectorSheafBaseChange
attribute [local irreducible] AffineTildeSemilinearMap.map Scheme.Modules.pullback

/-- The line and ambient pullback comparisons identify the actual sheaf inclusions. -/
lemma sheafBaseChange_inclusion [Finite ι] (φ : R →+* S) (i : ι) (L : Chart R ι i) :
    (sheafBaseChange φ i L).hom ≫ sheafInclusion i (baseChange φ i L) =
      (pullback (Spec.map (CommRingCat.ofHom φ))).map (sheafInclusion i L) ≫
        (vectorSheafBaseChange ι φ).hom := by
  rw [sheafBaseChange_hom, vectorSheafBaseChange_hom]
  exact AffineTildeSemilinearNaturality.map_square (CommRingCat.ofHom φ)
    (ModuleCat.ofHom L.val.subtype) (ModuleCat.ofHom (baseChange φ i L).val.subtype)
    (coefficientMap φ i L) (vectorCoefficientMap ι φ) (fun _ ↦ rfl)

end FLT.Mazur.NormalizedSectionLine
