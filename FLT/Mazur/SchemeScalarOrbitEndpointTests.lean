/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarOrbitTestLifts

/-!
# Actual endpoint characters of original scalar tensor tests

Two original-scalar algebra maps construct the tensor test. Its two scheme
endpoints are precisely the spectra of those supplied coefficient maps.
This identifies the test without any field or reducedness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeScalarOrbitComparison
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} [IsAffine X]
  (ρ : G →* Aut X) {R B : Type u} [CommRing R] [CommRing B]
  (s : R →+* invariantCoordinates ρ) [Algebra R B]

/-- The tensor test retains the first supplied coefficient character as a scheme morphism. -/
theorem tensorTest_productMap_first :
    let _ := sourceAlgebra ρ s
    ∀ u v : Γ(X, ⊤) →ₐ[R] B,
      tensorTest ρ s (Algebra.TensorProduct.productMap u v).toRingHom ≫ tensorFirst ρ s =
        Spec.map (CommRingCat.ofHom u.toRingHom) ≫ X.isoSpec.inv := by
  let _ := sourceAlgebra ρ s
  dsimp only
  intro u v
  unfold tensorTest tensorFirst tensorScheme
  dsimp only [id]
  rw [← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  ext a
  change u a * v 1 = u a
  rw [map_one, mul_one]

/-- The second supplied character remains independent over the same original scalar ring. -/
theorem tensorTest_productMap_second :
    let _ := sourceAlgebra ρ s
    ∀ u v : Γ(X, ⊤) →ₐ[R] B,
      tensorTest ρ s (Algebra.TensorProduct.productMap u v).toRingHom ≫ tensorSecond ρ s =
        Spec.map (CommRingCat.ofHom v.toRingHom) ≫ X.isoSpec.inv := by
  let _ := sourceAlgebra ρ s
  dsimp only
  intro u v
  unfold tensorTest tensorSecond tensorScheme
  dsimp only [id]
  rw [← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  ext a
  change u 1 * v a = v a
  rw [map_one, one_mul]

end FLT.Mazur.SchemeScalarOrbitComparison
