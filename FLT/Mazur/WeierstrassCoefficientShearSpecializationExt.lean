/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSpecialization

/-!
# Detecting equality after actual coefficient specialization

The complete original model projection and the target coefficient structure
jointly detect equality. No injectivity of the coefficient homomorphism is needed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (r : S) (v : T) (j : ℕ) (hj : j ≤ n) (f : S →ₐ[R] T)

/-- Equality after specialization lifts when the actual target coefficient legs agree. -/
theorem coefficientShearSpecialization_hom_ext {Z : Scheme.{u}}
    (g h : Z ⟶ coefficientShearGlued hπ data T v j hj)
    (hs : g ≫ coefficientShearGluedStructure hπ data T v j hj =
      h ≫ coefficientShearGluedStructure hπ data T v j hj)
    (hm : g ≫ coefficientShearSpecialization hπ data S T r v j hj f =
      h ≫ coefficientShearSpecialization hπ data S T r v j hj f) : g = h := by
  apply (coefficientShearGlued_isPullback hπ data T v j hj).hom_ext hs
  have H := congrArg (· ≫ coefficientShearGluedProjection hπ data S r j hj) hm
  simpa only [Category.assoc, coefficientShearSpecialization_projection] using H

end FLT.Mazur.WeierstrassDividedDepth
