/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Effective affine module descent in coalgebra form

For a faithfully flat ring map, the scalar-extension comonad has effective
descent. Transporting its inverse through tilde constructs an actual
quasi-coherent sheaf on the base, with its pullback reconstruction.

This is module descent in coalgebra form. The comparison with geometric
cocycle descent data and descent of the rank-one property are separate steps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineModuleCoalgebraDescent

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Algebraic descent data with their actual counit and coassociativity equations. -/
abbrev Data := (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.Coalgebra

/-- Faithfully flat module descent as the comparison equivalence. -/
def descentEquivalence (hφ : φ.hom.FaithfullyFlat) : ModuleCat R ≌ Data φ := by
  let h := comonadicExtendScalars hφ
  have : (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).IsEquivalence := h.eqv
  exact (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).asEquivalence

/-- The descended coefficient module. -/
def descendedModule (hφ : φ.hom.FaithfullyFlat) (D : Data φ) : ModuleCat R :=
  (descentEquivalence φ hφ).inverse.obj D

/-- Scalar extension reconstructs the full descent datum, including its coaction. -/
def reconstruction (hφ : φ.hom.FaithfullyFlat) (D : Data φ) :
    (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj
      (descendedModule φ hφ D) ≅ D :=
  (descentEquivalence φ hφ).counitIso.app D

/-- The reconstructed module is isomorphic to the original coefficient module. -/
def coefficientIso (hφ : φ.hom.FaithfullyFlat) (D : Data φ) :
    (ModuleCat.extendScalars φ.hom).obj (descendedModule φ hφ D) ≅ D.A :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.forget.mapIso
    (reconstruction φ hφ D)

/-- The coefficient reconstruction respects the descent coaction. -/
theorem coefficientIso_coaction (hφ : φ.hom.FaithfullyFlat) (D : Data φ) :
    (coefficientIso φ hφ D).hom ≫ D.a =
      ((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj
        (descendedModule φ hφ D)).a ≫
        (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.map
          (coefficientIso φ hφ D).hom :=
  (reconstruction φ hφ D).hom.h.symm

/-- The actual affine sheaf descended from algebraic descent data. -/
def descendedSheaf (hφ : φ.hom.FaithfullyFlat) (D : Data φ) : (Spec R).Modules :=
  tilde (descendedModule φ hφ D)

instance (hφ : φ.hom.FaithfullyFlat) (D : Data φ) :
    (descendedSheaf φ hφ D).IsQuasicoherent := by
  dsimp [descendedSheaf]
  infer_instance

/-- Pullback of the descended sheaf reconstructs the original affine coefficient sheaf. -/
def pullbackDescentIso (hφ : φ.hom.FaithfullyFlat) (D : Data φ) :
    (pullback (Spec.map φ)).obj (descendedSheaf φ hφ D) ≅ tilde D.A :=
  ((AffineModulePullbackSections.tildePullbackIso φ).app
    (descendedModule φ hφ D)).symm ≪≫
    (tilde.functor S).mapIso (coefficientIso φ hφ D)

/-- Descending canonical data recovers the original module sheaf. -/
def descendedCanonicalIso (hφ : φ.hom.FaithfullyFlat) (M : ModuleCat R) :
    descendedSheaf φ hφ
      ((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj M) ≅ tilde M :=
  (tilde.functor R).mapIso ((descentEquivalence φ hφ).unitIso.app M).symm

/-- Descent data isomorphisms identify the descended sheaves. -/
def descendedSheafIso (hφ : φ.hom.FaithfullyFlat) {D E : Data φ} (e : D ≅ E) :
    descendedSheaf φ hφ D ≅ descendedSheaf φ hφ E :=
  (tilde.functor R).mapIso ((descentEquivalence φ hφ).inverse.mapIso e)

end FLT.Mazur.AffineModuleCoalgebraDescent
