/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricDescentMorphisms

/-!
# Composition and identity coherence for geometric affine descent

The geometric compatibility square is closed under identities and composition.
Reconstruction uniqueness then proves the corresponding descent identities.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {M N P : (Spec S).Modules}
variable [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent]
variable (D : Data φ M) (E : Data φ N) (F : Data φ P)

omit [M.IsQuasicoherent] in
/-- The identity map satisfies the actual geometric overlap square. -/
theorem mapCompatible_id : MapCompatible φ D D (𝟙 M) := by
  let _ := φ.hom.toAlgebra
  change AffineGeometricMapComparison.Compatible R S M M D.val D.val (𝟙 M)
  simp [AffineGeometricMapComparison.Compatible]

omit [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent] in
/-- Composable geometric overlap squares give a compatible composite. -/
theorem mapCompatible_comp (f : M ⟶ N) (g : N ⟶ P)
    (hf : MapCompatible φ D E f) (hg : MapCompatible φ E F g) :
    MapCompatible φ D F (f ≫ g) := by
  let _ := φ.hom.toAlgebra
  change AffineGeometricMapComparison.Compatible R S M N D.val E.val f at hf
  change AffineGeometricMapComparison.Compatible R S N P E.val F.val g at hg
  change AffineGeometricMapComparison.Compatible R S M P D.val F.val (f ≫ g)
  unfold AffineGeometricMapComparison.Compatible at *
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hf,
    Category.assoc, hg, ← Category.assoc]

variable (hφ : φ.hom.FaithfullyFlat)

/-- Descent of the geometric identity is the identity of the descended sheaf. -/
@[simp]
theorem descendedMap_id :
    descendedMap φ D D (𝟙 M) (mapCompatible_id φ D) hφ = 𝟙 _ := by
  symm
  apply descendedMap_unique
  simp

/-- Descent of compatible geometric maps preserves composition. -/
@[reassoc]
theorem descendedMap_comp (f : M ⟶ N) (g : N ⟶ P)
    (hf : MapCompatible φ D E f) (hg : MapCompatible φ E F g) :
    descendedMap φ D F (f ≫ g) (mapCompatible_comp φ D E F f g hf hg) hφ =
      descendedMap φ D E f hf hφ ≫ descendedMap φ E F g hg hφ := by
  symm
  apply descendedMap_unique
  rw [Functor.map_comp, Category.assoc, reconstruction_naturality,
    ← Category.assoc, reconstruction_naturality, Category.assoc]

/-- Descent of compatible isomorphisms preserves composition. -/
theorem descendedIso_trans (i : M ≅ N) (j : N ≅ P)
    (hi : MapCompatible φ D E i.hom) (hj : MapCompatible φ E F j.hom) :
    descendedIso φ D F hφ (i ≪≫ j) (mapCompatible_comp φ D E F i.hom j.hom hi hj) =
      descendedIso φ D E hφ i hi ≪≫ descendedIso φ E F hφ j hj := by
  apply Iso.ext
  exact descendedMap_comp φ D E F hφ i.hom j.hom hi hj

end FLT.Mazur.AffineGeometricDescent
