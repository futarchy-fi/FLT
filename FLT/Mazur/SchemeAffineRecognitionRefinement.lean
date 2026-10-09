/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartRecognitionIso
public import FLT.Mazur.SchemeAffineChartReconstruction
public import FLT.Mazur.SchemePullbackCompositeRecognition

/-!
# Recognition of a base sheaf respects chart refinement

The prescribed reconstruction commutes with restriction to a refined chart.
Faithful flatness then identifies the corresponding effective recognition maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open SheafPullbackPathComparison SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable (ρ : C.Refinement C') (A : X.Modules) {M : Y.Modules}
variable (e : (pullback p).obj A ≅ M)

/-- Restricting a proposed reconstruction agrees with the refined reconstruction. -/
@[reassoc]
lemma recognitionChart_refinement :
    (AffineRefinementPullback.reconstruction C.ringMap C'.ringMap ρ.base ρ.cover
        ρ.square (recognitionChart p A e C.ringMap C.base C.cover C.square)).hom ≫
        (SheafPullbackPathComparison.comparison (Spec.map ρ.cover) C.cover C'.cover
          ρ.cover_over).hom.app M =
      (pullback (Spec.map C'.ringMap)).map
          ((SheafPullbackPathComparison.comparison (Spec.map ρ.base) C.base C'.base
            ρ.base_over).hom.app A) ≫
        (recognitionChart p A e C'.ringMap C'.base C'.cover C'.square).hom := by
  exact SchemePullbackSquare.reconstruction_composition_of_eq p (Spec.map C.ringMap)
    (Spec.map C'.ringMap) C.base C.cover (Spec.map ρ.base) (Spec.map ρ.cover)
    C.square (AffineRefinementPullback.spec_square _ _ _ _ ρ.square)
    C'.base C'.cover ρ.base_over ρ.cover_over C'.square e
    (recognitionChart p A e C.ringMap C.base C.cover C.square)
    (AffineRefinementPullback.reconstruction C.ringMap C'.ringMap ρ.base ρ.cover
      ρ.square (recognitionChart p A e C.ringMap C.base C.cover C.square))
    (recognitionChart p A e C'.ringMap C'.base C'.cover C'.square)
    (by simp only [recognitionChart, SchemePullbackSquare.squareIso,
      SheafPullbackPathComparison.comparison, SchemePullbackSquare.reconstructionChart,
      Iso.trans_assoc])
    (by rfl)
    (by simp only [recognitionChart, SchemePullbackSquare.squareIso,
      SheafPullbackPathComparison.comparison, SchemePullbackSquare.reconstructionChart,
      Iso.trans_assoc])
    ((SheafPullbackPathComparison.comparison (Spec.map ρ.base) C.base C'.base
      ρ.base_over).app A)
    ((SheafPullbackPathComparison.comparison (Spec.map ρ.cover) C.cover C'.cover
      ρ.cover_over).app M) (by rfl) (by rfl)

variable (D : SchemeGeometricDescent.Data p M)
variable (he : D.overlap = SchemePullbackOverlap.chartOverlap p
  (Limits.pullback.fst p p) (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [((pullback C.base).obj A).IsQuasicoherent]
variable [((pullback C'.base).obj A).IsQuasicoherent]
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- Effective recognition commutes with the actual chart comparison. -/
@[reassoc]
lemma recognitionIso_refinement :
    (pullback (Spec.map ρ.base)).map (C.recognitionIso D A e he).hom ≫
        (C.comparison C' D ρ).hom =
      (SheafPullbackPathComparison.comparison (Spec.map ρ.base) C.base C'.base
            ρ.base_over).hom.app A ≫
        (C'.recognitionIso D A e he).hom := by
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback ρ.base
    ((pullback C.base).obj A)
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique C'.ringMap
    C'.faithfullyFlat (C'.reconstruction D)
  rw [Functor.map_comp, Category.assoc, comparison_reconstruction]
  rw [Functor.map_comp, Category.assoc, recognitionIso_reconstruction]
  change _ ≫ (AffineRefinementPullback.reconstruction _ _ _ _ _ _).hom ≫ _ = _
  rw [← Category.assoc, AffineRefinementPullback.reconstruction_naturality
    C.ringMap C'.ringMap ρ.base ρ.cover ρ.square
    (recognitionChart p A e C.ringMap C.base C.cover C.square)
    (C.reconstruction D) (C.recognitionIso D A e he).hom (𝟙 _)
    (by simpa using C.recognitionIso_reconstruction D A e he)]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  exact C.recognitionChart_refinement C' ρ A e

end FLT.Mazur.SchemeAffineDescent.Chart
