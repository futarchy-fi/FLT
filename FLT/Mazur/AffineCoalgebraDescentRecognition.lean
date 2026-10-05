/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoalgebraSheafNaturality

/-!
# Recognizing an affine descended module

An isomorphism from a canonical scalar-extension coalgebra to a descent datum
identifies its source with the effectively descended module. The identification
recovers the specified coefficient map, rather than just an abstract isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineModuleCoalgebraDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem equivalence_recognition {C D : Type*} [Category C] [Category D]
    (q : C ≌ D) {A : C} {B : D} (e : q.functor.obj A ≅ B) :
    q.functor.map ((q.unitIso.app A ≪≫ q.inverse.mapIso e).hom) ≫
      (q.counitIso.app B).hom = e.hom := by
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  have hn := q.counitIso.hom.naturality e.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [Functor.map_comp, Category.assoc, hn,
    ← Category.assoc, q.functor_unitIso_comp, Category.id_comp]

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)
variable (A : ModuleCat.{u} R) (D : Data φ)
variable (e : (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj A ≅ D)

/-- Canonical coefficient data identify a candidate with the descended module. -/
def recognitionIso : A ≅ descendedModule φ hφ D :=
  (descentEquivalence φ hφ).unitIso.app A ≪≫
    (descentEquivalence φ hφ).inverse.mapIso e

/-- The recognition isomorphism recovers exactly the given coefficient isomorphism. -/
@[reassoc]
theorem recognitionIso_reconstruction :
    (ModuleCat.extendScalars φ.hom).map (recognitionIso φ hφ A D e).hom ≫
      (coefficientIso φ hφ D).hom = e.hom.f :=
  congrArg (fun g ↦ g.f) (equivalence_recognition (descentEquivalence φ hφ) e)

/-- The coefficient reconstruction square determines the recognition map uniquely. -/
theorem recognitionIso_unique (g : A ⟶ descendedModule φ hφ D)
    (hg : (ModuleCat.extendScalars φ.hom).map g ≫ (coefficientIso φ hφ D).hom =
      e.hom.f) : g = (recognitionIso φ hφ A D e).hom := by
  apply (descentEquivalence φ hφ).functor.map_injective
  apply Comonad.Coalgebra.Hom.ext
  apply (cancel_mono (coefficientIso φ hφ D).hom).mp
  exact hg.trans (recognitionIso_reconstruction φ hφ A D e).symm

/-- Canonical coefficient recognition also identifies the actual tilde sheaves. -/
def recognitionSheafIso : tilde A ≅ descendedSheaf φ hφ D :=
  (tilde.functor R).mapIso (recognitionIso φ hφ A D e)

/-- The sheaf recognition map has the specified reconstruction on the cover. -/
@[reassoc]
theorem recognitionSheafIso_reconstruction :
    (pullback (Spec.map φ)).map (recognitionSheafIso φ hφ A D e).hom ≫
        (pullbackDescentIso φ hφ D).hom =
      ((AffineModulePullbackSections.tildePullbackIso φ).app A).inv ≫
        (tilde.functor S).map e.hom.f := by
  have hn := (AffineModulePullbackSections.tildePullbackIso φ).inv.naturality
    (recognitionIso φ hφ A D e).hom
  dsimp only [recognitionSheafIso, Functor.mapIso_hom, pullbackDescentIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    recognitionIso_reconstruction]

end FLT.Mazur.AffineModuleCoalgebraDescent
