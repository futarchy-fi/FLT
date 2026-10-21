/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBoundary
public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import FLT.Mazur.TensorOpenChart

/-!
# Actual divided input coordinates on the full successive tensor chart

The contraction retains x = u and y = u*v after arbitrary scalar extension.
Its affine map is exactly the original contraction after tensor projection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (hπ : π ≠ 0) (d : Data W π k) (e : Data W π (k + 1))
  (S : Type u) [CommRing S] [Algebra R S]
local notation "T" => ScalarExtension W (π ^ k) π e.b3 e.b4 e.b6 S
local notation "c" => WeierstrassDilatation.parameterEquiv W (π ^ k) (π ^ k)
  d.b3 d.b4 d.b6 (π * e.b3) (π * e.b4) (π ^ 2 * e.b6) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)

/-- The original divided coordinate homomorphism into the entire successive tensor algebra. -/
def successiveTensorInput : WeierstrassDilatation.Coordinate W (π ^ k)
    d.b3 d.b4 d.b6 →ₐ[R] T :=
  (Algebra.TensorProduct.includeRight : Coordinate W (π ^ k) π e.b3 e.b4 e.b6 →ₐ[R] T).comp
    ((fromDivided W (π ^ k) π e.b3 e.b4 e.b6).comp (c).toAlgHom)

/-- The preceding horizontal coordinate is the uncontracted tensor horizontal coordinate. -/
@[simp] theorem successiveTensorInput_x :
    successiveTensorInput hπ d e S (WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6) =
      tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 S 2 := by
  change (Algebra.TensorProduct.includeRight : Coordinate W (π ^ k) π e.b3 e.b4 e.b6 →ₐ[R] T)
    (fromDivided W (π ^ k) π e.b3 e.b4 e.b6
      (c (WeierstrassDilatation.x W (π ^ k) d.b3 d.b4 d.b6))) = _
  rw [WeierstrassDilatation.parameterEquiv_x, fromDivided_x]
  rfl

/-- The preceding ordinate is exactly horizontal coordinate times slope. -/
@[simp] theorem successiveTensorInput_y :
    successiveTensorInput hπ d e S (WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6) =
      tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 S 2 *
        tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 S 1 := by
  change (Algebra.TensorProduct.includeRight : Coordinate W (π ^ k) π e.b3 e.b4 e.b6 →ₐ[R] T)
    (fromDivided W (π ^ k) π e.b3 e.b4 e.b6
      (c (WeierstrassDilatation.y W (π ^ k) d.b3 d.b4 d.b6))) = _
  rw [WeierstrassDilatation.parameterEquiv_y, fromDivided_y, map_mul]
  rfl

/-- The explicit coordinates describe the original contraction on the full tensor chart. -/
theorem successiveTensorInput_spec :
    Spec.map (CommRingCat.ofHom (successiveTensorInput hπ d e S).toRingHom) =
      TensorOpenChart.projection ≫ xContraction hπ d e := by
  change Spec.map _ = Spec.map _ ≫ (Spec.map _ ≫ Spec.map _)
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
