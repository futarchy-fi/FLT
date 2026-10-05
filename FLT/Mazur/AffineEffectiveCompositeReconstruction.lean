/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEffectiveCompositionChart
public import FLT.Mazur.AffineRefinementReconstructionMap
public import FLT.Mazur.ReconstructionComposition

/-!
# Twice-refined effective reconstruction

Restriction of an effective comparison identifies the next reconstruction
with the reconstruction obtained by restricting the original chart twice.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDescentRefinement
open AffineGeometricDescent AffineGeometricOverlapRefinement AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' R'' S'' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)
variable (hφ : φ.hom.FaithfullyFlat) (hψ : ψ.hom.FaithfullyFlat)
variable (hχ : χ.hom.FaithfullyFlat)
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
local instance isQuasicoherent_twiceReconstructionPullback {T U : CommRingCat.{u}} (f : T ⟶ U)
    (P : (Spec T).Modules) [P.IsQuasicoherent] :
    ((pullback (Spec.map f)).obj P).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback f P

/-- Restriction of the first effective comparison intertwines the second reconstructions. -/
@[reassoc]
theorem effectiveComparisonIso_reconstruction_twice :
    (pullback (Spec.map χ)).map
        ((pullback (Spec.map c)).map (effectiveComparisonIso φ ψ a b w hφ D hψ).hom) ≫
      (reconstruction ψ χ c d v hψ (data φ ψ a b w M D)).hom =
    (AffineRefinementPullback.reconstruction ψ χ c d v
      (reconstruction φ ψ a b w hφ D)).hom :=
  AffineRefinementPullback.reconstruction_map ψ χ c d v
    (reconstruction φ ψ a b w hφ D)
    (AffineGeometricDescent.reconstruction ψ _ (data φ ψ a b w M D) hψ)
    (effectiveComparisonIso φ ψ a b w hφ D hψ).hom
    (effectiveComparisonIso_reconstruction φ ψ a b w hφ D hψ)

end FLT.Mazur.AffineDescentRefinement
