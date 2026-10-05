/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCanonicalMapCompatibility
public import FLT.Mazur.AffineRefinementCoactionCompatibility
public import FLT.Mazur.AffineRefinementComposition

/-!
# The cover composition chart intertwines the actual refined data

Two successive refinements and refinement along their composite give compatible
data under the actual cover pullback composition chart. Compatibility follows
from reconstructed charts and requires no extra hypothesis about the refined data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescentRecognition
open AffineGeometricDescent AffineGeometricOverlapRefinement AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' R'' S'' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)
variable {A : (Spec R).Modules} [A.IsQuasicoherent]
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
variable (e : (pullback (Spec.map φ)).obj A ≅ M)
local instance {T U : CommRingCat.{u}} (f : T ⟶ U)
    (P : (Spec T).Modules) [P.IsQuasicoherent] :
    ((pullback (Spec.map f)).obj P).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback f P

/-- The composition chart is compatible with successive and composite refinement. -/
theorem compositionData_compatible (he : CoactionCompatible φ A D e) :
    MapCompatible χ
      (data ψ χ c d v ((pullback (Spec.map b)).obj M) (data φ ψ a b w M D))
      (data φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v) M D)
      (compositionChart b d M).hom :=
  mapCompatible_of_reconstruction χ _ _
    (AffineRefinementPullback.reconstruction ψ χ c d v
      (AffineRefinementPullback.reconstruction φ ψ a b w e))
    (AffineRefinementPullback.reconstruction φ χ (a ≫ c) (b ≫ d)
      (composite_square φ ψ χ a b c d w v) e)
    (refinement_compatible ψ χ c d v _ _ _ (refinement_compatible φ ψ a b w A D e he))
    (refinement_compatible φ χ (a ≫ c) (b ≫ d)
      (composite_square φ ψ χ a b c d w v) A D e he)
    (compositionChart a c A).hom _
    (AffineRefinementPullback.reconstruction_composition φ ψ χ a b c d w v e).symm

end FLT.Mazur.AffineGeometricDescentRecognition
