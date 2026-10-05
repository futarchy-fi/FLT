/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoalgebraDescentRecognition
public import FLT.Mazur.AffineGeometricDescent
public import FLT.Mazur.AffinePullbackCoefficientRecognition
public import FLT.Mazur.AffineQuasicoherentPullbackFaithful

/-!
# Recognition of an affine geometric descent by its coaction

A proposed quasi-coherent sheaf on the base, with a reconstruction on the cover,
recovers the descended sheaf whenever its coefficient chart respects the actual
coaction. The resulting isomorphism has the prescribed reconstruction and is
unique. Coaction compatibility is an explicit algebraic equation to be proved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent AffinePullbackCoefficientRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FaithfullyFlat)
variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
variable (e : (pullback (Spec.map φ)).obj A ≅ M)

/-- The coefficient chart intertwines the canonical and specified coactions. -/
def CoactionCompatible : Prop :=
  ((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj
      (moduleSpecΓFunctor.obj A)).a ≫
        (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.map (chart φ A e).hom =
    (chart φ A e).hom ≫ (coalgebra φ M D).a

variable (he : CoactionCompatible φ A D e)

/-- The reconstruction chart is an isomorphism of the actual coefficient coalgebras. -/
def coefficientIso :
    (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj
      (moduleSpecΓFunctor.obj A) ≅ coalgebra φ M D :=
  Comonad.Coalgebra.isoMk (chart φ A e) he

/-- The candidate is canonically isomorphic to the effectively descended sheaf. -/
def sheafIso : A ≅ descendedSheaf φ M D hφ :=
  (asIso A.fromTildeΓ).symm ≪≫
    AffineModuleCoalgebraDescent.recognitionSheafIso φ hφ (moduleSpecΓFunctor.obj A)
      (coalgebra φ M D) (coefficientIso φ A D e he)

/-- Recognition gives precisely the original reconstruction on the cover. -/
@[reassoc]
theorem sheafIso_reconstruction :
    (pullback (Spec.map φ)).map (sheafIso φ hφ A D e he).hom ≫
      (reconstruction φ M D hφ).hom = e.hom := by
  have hr := AffineModuleCoalgebraDescent.recognitionSheafIso_reconstruction φ hφ
    (moduleSpecΓFunctor.obj A) (coalgebra φ M D) (coefficientIso φ A D e he)
  change (pullback (Spec.map φ)).map
      (inv A.fromTildeΓ ≫ (AffineModuleCoalgebraDescent.recognitionSheafIso φ hφ
        (moduleSpecΓFunctor.obj A) (coalgebra φ M D) (coefficientIso φ A D e he)).hom) ≫
      ((AffineModuleCoalgebraDescent.pullbackDescentIso φ hφ (coalgebra φ M D)).hom ≫
        M.fromTildeΓ) = e.hom
  rw [Functor.map_comp, Category.assoc, ← Category.assoc _ _ M.fromTildeΓ, hr]
  change (pullback (Spec.map φ)).map (inv A.fromTildeΓ) ≫
    ((((AffineModulePullbackSections.tildePullbackIso φ).app
      (moduleSpecΓFunctor.obj A)).inv ≫ (tilde.functor S).map (chart φ A e).hom) ≫
        M.fromTildeΓ) = e.hom
  rw [Category.assoc, chart_counit]
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The prescribed reconstruction uniquely determines the recognition map. -/
theorem sheafIso_unique (g : A ⟶ descendedSheaf φ M D hφ)
    (hg : (pullback (Spec.map φ)).map g ≫ (reconstruction φ M D hφ).hom = e.hom) :
    g = (sheafIso φ hφ A D e he).hom :=
  AffineQuasicoherentPullbackFaithful.reconstruction_unique φ hφ
    (reconstruction φ M D hφ) g _
    (hg.trans (sheafIso_reconstruction φ hφ A D e he).symm)

end FLT.Mazur.AffineGeometricDescentRecognition
