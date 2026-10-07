/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEffectiveSuccessiveReconstruction
public import FLT.Mazur.AffineRefinementReconstructionRecognition

/-!
# Composition coherence of effective affine refinement

Two effective refinement comparisons compose to the comparison for the
composite square, after the actual base chart and the descended cover chart.
Faithful flat reconstruction determines this identity uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDescentRefinement
open AffineGeometricDescent AffineGeometricOverlapRefinement AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] AffineGeometricOverlapRefinement.data
attribute [local irreducible] effectiveComparisonIso compositionDescentIso
variable {R S R' S' R'' S'' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)
variable (hφ : φ.hom.FaithfullyFlat) (hψ : ψ.hom.FaithfullyFlat)
variable (hχ : χ.hom.FaithfullyFlat)
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
attribute [local instance] isQuasicoherent_twiceReconstructionPullback

/-- The named effective reconstruction is the refinement of the original reconstruction. -/
theorem reconstruction_eq_refinement :
    reconstruction φ ψ a b w hφ D =
      AffineRefinementPullback.reconstruction φ ψ a b w
        (AffineGeometricDescent.reconstruction φ M D hφ) := rfl

/-- Recognize the named effective reconstruction as the scheme square chart. -/
theorem reconstruction_eq_chart :
    reconstruction φ ψ a b w hφ D =
      SchemePullbackSquare.reconstructionChart (Spec.map φ) (Spec.map ψ)
        (Spec.map a) (Spec.map b) (spec_square φ ψ a b w)
        (AffineGeometricDescent.reconstruction φ M D hφ) :=
  (reconstruction_eq_refinement φ ψ a b w hφ D).trans
    (AffineRefinementPullback.reconstruction_eq_chart φ ψ a b w
      (AffineGeometricDescent.reconstruction φ M D hφ))

/-- Composition retains the named intermediate descended sheaf. -/
theorem reconstruction_composition_refinement :
    (AffineRefinementPullback.reconstruction ψ χ c d v
      (reconstruction φ ψ a b w hφ D)).hom ≫ (compositionChart b d M).hom =
    (pullback (Spec.map χ)).map
      (X := (pullback (Spec.map c)).obj (sheaf φ a hφ D))
      (compositionChart a c (descendedSheaf φ M D hφ)).hom ≫
      (AffineRefinementPullback.reconstruction φ χ (a ≫ c) (b ≫ d)
        (composite_square φ ψ χ a b c d w v)
        (AffineGeometricDescent.reconstruction φ M D hφ)).hom :=
  AffineRefinementPullback.reconstruction_composition_named φ ψ χ a b c d w v
    (AffineGeometricDescent.reconstruction φ M D hφ) (sheaf φ a hφ D) rfl
    (reconstruction φ ψ a b w hφ D)
    (heq_of_eq (reconstruction_eq_refinement φ ψ a b w hφ D))
    (compositionChart a c (descendedSheaf φ M D hφ)) (HEq.rfl)

/-- Composition of the named effective reconstruction charts. -/
theorem reconstruction_composition :
    (AffineRefinementPullback.reconstruction ψ χ c d v
      (reconstruction φ ψ a b w hφ D)).hom ≫ (compositionChart b d M).hom =
    (pullback (Spec.map χ)).map
      (X := (pullback (Spec.map c)).obj (sheaf φ a hφ D))
      (compositionChart a c (descendedSheaf φ M D hφ)).hom ≫
      (reconstruction φ χ (a ≫ c) (b ≫ d)
        (composite_square φ ψ χ a b c d w v) hφ D).hom :=
  (reconstruction_composition_refinement φ ψ χ a b c d w v hφ D).trans
    (congrArg (fun e ↦ (pullback (Spec.map χ)).map
        (X := (pullback (Spec.map c)).obj (sheaf φ a hφ D))
        (compositionChart a c (descendedSheaf φ M D hφ)).hom ≫ e.hom)
      (reconstruction_eq_refinement φ χ (a ≫ c) (b ≫ d)
        (composite_square φ ψ χ a b c d w v) hφ D).symm)

end FLT.Mazur.AffineDescentRefinement
