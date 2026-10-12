/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShear

/-!
# The actual horizontal boundary under a divided shear

Localize the whole algebra equivalence at the fixed horizontal coordinate.
The comparison retains all functions and the original open immersion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 r : R)
local notation "U" => rootShearCurve W r
local notation "A" => HorizontalCoordinate W s b3 b4 b6
local notation "B" => HorizontalCoordinate U s b3 (b4 - r * b3) b6

/-- The actual horizontal boundary algebra is identified by shear. -/
def horizontalShearEquiv : A ≃ₐ[R] B :=
  IsLocalization.algEquivOfAlgEquiv A B
    (M := Submonoid.powers (x W s b3 b4 b6))
    (T := Submonoid.powers (x U s b3 (b4 - r * b3) b6))
    (shearEquiv W s b3 b4 b6 r) (by
      rw [Submonoid.map_powers]
      congr 1
      exact shearForward_x W s b3 b4 b6 r)

/-- Every original function survives localization of the shear. -/
theorem horizontalShearEquiv_base (z : Coordinate W s b3 b4 b6) :
    horizontalShearEquiv W s b3 b4 b6 r (algebraMap _ A z) =
      algebraMap _ B (shearForward W s b3 b4 b6 r z) := by
  rw [horizontalShearEquiv, IsLocalization.algEquivOfAlgEquiv_eq]
  rfl

/-- The full horizontal principal-open isomorphism induced by shear. -/
def horizontalShearIso : Spec (.of B) ≅ Spec (.of A) :=
  Scheme.Spec.mapIso (horizontalShearEquiv W s b3 b4 b6 r).toRingEquiv.toCommRingCatIso.op

/-- The sheared boundary retains its original inclusion into the divided chart. -/
@[reassoc] theorem horizontalShearIso_inclusion :
    (horizontalShearIso W s b3 b4 b6 r).hom ≫ horizontalInclusion W s b3 b4 b6 =
      horizontalInclusion U s b3 (b4 - r * b3) b6 ≫
        Spec.map (CommRingCat.ofHom (shearForward W s b3 b4 b6 r).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact horizontalShearEquiv_base W s b3 b4 b6 r z

end FLT.Mazur.WeierstrassDilatation
