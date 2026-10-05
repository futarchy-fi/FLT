/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricChartRecognition
public import FLT.Mazur.AffineReconstructionCoefficientChart

/-!
# Compatibility of the effective geometric reconstruction

The actual reconstruction produced by faithfully flat coefficient descent
intertwines the original geometric coaction. Its coefficient chart therefore
recovers the original geometric datum, and recognition returns the identity.
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
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)

/-- The actual effective reconstruction intertwines the original coaction. -/
theorem reconstruction_compatible :
    CoactionCompatible φ (descendedSheaf φ M D hφ) D (reconstruction φ M D hφ) := by
  let P := AffineModuleCoalgebraDescent.descendedModule φ hφ (coalgebra φ M D)
  let e := AffineModuleCoalgebraDescent.coefficientIso φ hφ (coalgebra φ M D)
  have hc := chart_reconstructed φ P (M := M) e
  change (chart φ (descendedSheaf φ M D hφ) (reconstruction φ M D hφ)).hom =
    (ModuleCat.extendScalars φ.hom).map (tilde.toTildeΓNatIso.app P).inv ≫ e.hom at hc
  unfold CoactionCompatible
  rw [hc, Functor.map_comp]
  have hn := ((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).map
    (tilde.toTildeΓNatIso.app P).inv).h
  change ((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj
      (moduleSpecΓFunctor.obj (tilde P))).a ≫
      (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.map
        ((ModuleCat.extendScalars φ.hom).map (tilde.toTildeΓNatIso.app P).inv) =
    (ModuleCat.extendScalars φ.hom).map (tilde.toTildeΓNatIso.app P).inv ≫
      ((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj P).a at hn
  erw [← Category.assoc, hn, Category.assoc]
  have he := AffineModuleCoalgebraDescent.coefficientIso_coaction φ hφ (coalgebra φ M D)
  rw [← he, ← Category.assoc]

/-- The effective reconstruction chart recovers the original geometric datum. -/
theorem reconstruction_chartData :
    chartData φ (descendedSheaf φ M D hφ) (reconstruction φ M D hφ) = D :=
  ((coactionCompatible_iff_eq_chartData φ (descendedSheaf φ M D hφ)
    (reconstruction φ M D hφ) D).mp (reconstruction_compatible φ hφ D)).symm

/-- Recognizing the original effective reconstruction gives the identity. -/
theorem reconstruction_sheafIso :
    sheafIso φ hφ (descendedSheaf φ M D hφ) D (reconstruction φ M D hφ)
      (reconstruction_compatible φ hφ D) = Iso.refl _ := by
  apply Iso.ext
  exact (sheafIso_unique φ hφ (descendedSheaf φ M D hφ) D (reconstruction φ M D hφ)
    (reconstruction_compatible φ hφ D) (𝟙 _) (by
      simp only [CategoryTheory.Functor.map_id, Category.id_comp])).symm

end FLT.Mazur.AffineGeometricDescentRecognition
