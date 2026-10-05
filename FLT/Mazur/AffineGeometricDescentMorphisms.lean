/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoalgebraSheafNaturality
public import FLT.Mazur.AffineGeometricDescent
public import FLT.Mazur.AffineFaithfullyFlatPullbackFaithful
public import FLT.Mazur.AffineGeometricMapComparison
public import FLT.Mazur.AffineTensorDescentMorphisms

/-!
# Descent of compatible geometric affine morphisms

The actual geometric overlap square produces a coalgebra morphism. Its
descended sheaf map satisfies the reconstruction square, and its coefficient
map is uniquely determined by reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescent
open AffineOverlapPullback AffineGeometricOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {M N : (Spec S).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
variable (D : Data φ M) (E : Data φ N) (f : M ⟶ N)

/-- Compatibility is the square on the actual pullback sheaves. -/
abbrev MapCompatible : Prop :=
  letI := φ.hom.toAlgebra
  AffineGeometricMapComparison.Compatible R S M N D.val E.val f

variable (hf : MapCompatible φ D E f)

set_option maxRecDepth 2048 in
/-- A compatible geometric map defines the corresponding coalgebra morphism. -/
def coalgebraMap : coalgebra φ M D ⟶ coalgebra φ N E := by
  letI := φ.hom.toAlgebra
  exact AffineTensorCocycle.toCoalgebraHom φ (coefficients S M) (coefficients S N)
    (toDatum R S M D.val D.property.1 D.property.2)
    (toDatum R S N E.val E.property.1 E.property.2) (moduleSpecΓFunctor.map f)
    (AffineGeometricMapComparison.tensor_compatible_tmul R S M N D.val E.val f hf)

/-- The coalgebra map retains the original global-section map. -/
theorem coalgebraMap_f : (coalgebraMap φ D E f hf).f = moduleSpecΓFunctor.map f := rfl

variable (hφ : φ.hom.FaithfullyFlat)

/-- The descended morphism of the actual sheaves on the base. -/
def descendedMap : descendedSheaf φ M D hφ ⟶ descendedSheaf φ N E hφ :=
  AffineModuleCoalgebraDescent.descendedSheafMap φ hφ (coalgebraMap φ D E f hf)

/-- Pullback of the descended map recovers the given geometric morphism. -/
@[reassoc]
theorem reconstruction_naturality :
    (pullback (Spec.map φ)).map (descendedMap φ D E f hf hφ) ≫
        (reconstruction φ N E hφ).hom =
      (reconstruction φ M D hφ).hom ≫ f := by
  have hn := AffineModuleCoalgebraDescent.pullbackDescentIso_naturality φ hφ
    (coalgebraMap φ D E f hf)
  have ht := (tilde.adjunction (R := S)).counit.naturality f
  change (tilde.functor S).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at ht
  change (pullback (Spec.map φ)).map (descendedMap φ D E f hf hφ) ≫
      (AffineModuleCoalgebraDescent.pullbackDescentIso φ hφ (coalgebra φ N E)).hom ≫
        N.fromTildeΓ =
    ((AffineModuleCoalgebraDescent.pullbackDescentIso φ hφ (coalgebra φ M D)).hom ≫
      M.fromTildeΓ) ≫ f
  dsimp only [descendedMap]
  erw [← Category.assoc, hn, Category.assoc, coalgebraMap_f, ht, Category.assoc]

/-- The actual sheaf reconstruction square uniquely determines the descended map. -/
theorem descendedMap_unique
    (g : descendedSheaf φ M D hφ ⟶ descendedSheaf φ N E hφ)
    (hg : (pullback (Spec.map φ)).map g ≫ (reconstruction φ N E hφ).hom =
      (reconstruction φ M D hφ).hom ≫ f) : g = descendedMap φ D E f hf hφ := by
  apply AffineFaithfullyFlatPullbackFaithful.tilde_map_injective φ hφ
  apply (cancel_mono (reconstruction φ N E hφ).hom).mp
  exact hg.trans (reconstruction_naturality φ D E f hf hφ).symm

/-- Reconstruction uniquely determines the descended coefficient morphism. -/
theorem descendedModuleMap_unique
    (g : AffineModuleCoalgebraDescent.descendedModule φ hφ (coalgebra φ M D) ⟶
      AffineModuleCoalgebraDescent.descendedModule φ hφ (coalgebra φ N E))
    (hg : (ModuleCat.extendScalars φ.hom).map g ≫
        (AffineModuleCoalgebraDescent.coefficientIso φ hφ (coalgebra φ N E)).hom =
      (AffineModuleCoalgebraDescent.coefficientIso φ hφ (coalgebra φ M D)).hom ≫
        moduleSpecΓFunctor.map f) :
    g = AffineModuleCoalgebraDescent.descendedModuleMap φ hφ (coalgebraMap φ D E f hf) :=
  AffineModuleCoalgebraDescent.descendedModuleMap_unique φ hφ (coalgebraMap φ D E f hf) g hg

/-- A compatible geometric isomorphism induces a coalgebra isomorphism. -/
def coalgebraIso (i : M ≅ N) (hi : MapCompatible φ D E i.hom) :
    coalgebra φ M D ≅ coalgebra φ N E :=
  Comonad.Coalgebra.isoMk (moduleSpecΓFunctor.mapIso i) (coalgebraMap φ D E i.hom hi).h

/-- Compatible geometric isomorphisms descend to actual sheaf isomorphisms. -/
def descendedIso (i : M ≅ N) (hi : MapCompatible φ D E i.hom) :
    descendedSheaf φ M D hφ ≅ descendedSheaf φ N E hφ :=
  AffineModuleCoalgebraDescent.descendedSheafIso φ hφ (coalgebraIso φ D E i hi)

/-- The descended isomorphism has the previously constructed descended homomorphism. -/
theorem descendedIso_hom (i : M ≅ N) (hi : MapCompatible φ D E i.hom) :
    (descendedIso φ D E hφ i hi).hom = descendedMap φ D E i.hom hi hφ := rfl

end FLT.Mazur.AffineGeometricDescent
