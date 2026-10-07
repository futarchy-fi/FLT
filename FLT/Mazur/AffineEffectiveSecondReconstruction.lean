/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEffectiveCompositeReconstruction

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

/-- The second comparison followed by the descended cover chart reconstructs the cover chart. -/
theorem effectiveComparisonIso_second_reconstruction :
    (pullback (Spec.map χ)).map
      ((effectiveComparisonIso ψ χ c d v hψ (data φ ψ a b w M D) hχ).hom ≫
        (compositionDescentIso φ ψ χ a b c d w v hφ D hχ).hom) ≫
      (AffineGeometricDescent.reconstruction χ _
        (data φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v) M D) hχ).hom =
    (reconstruction ψ χ c d v hψ (data φ ψ a b w M D)).hom ≫
      (compositionChart b d M).hom := by
  rw [Functor.map_comp, Category.assoc, compositionDescentIso_reconstruction,
    ← Category.assoc, effectiveComparisonIso_reconstruction]

end FLT.Mazur.AffineDescentRefinement
