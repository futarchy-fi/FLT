/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSplitGroupConnected
public import FLT.Mazur.ProjectiveLineMarkedCharts
public import FLT.Mazur.LaurentUnitPoints
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The oriented identity subgroup of the split polygon group

The zeroth full Laurent component is a subgroup, and reciprocal orientation
is a group automorphism. These are actual morphisms of commutative group schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.PolygonSplitGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K] (n : ℕ) [NeZero n]
local notation "T" => MultiplicativeGroupScheme.gm K

instance identityComponent_isMonHom : IsMonHom (component K n 0) where
  one_hom := rfl
  mul_hom := by simpa only [zero_add] using (component_mul K n 0 0).symm

/-- The complete zeroth summand is a commutative subgroup scheme. -/
def identityComponentGroupHom : CommGrp.mk T ⟶ CommGrp.mk (model K n) :=
  ⟨Grp.ofHom (component K n 0)⟩

/-- Reciprocation is an automorphism of the multiplicative group scheme. -/
def reciprocalGroupIso : CommGrp.mk T ≅ CommGrp.mk T :=
  CommGrp.mkIso' (asIso ι[T])

/-- Group inversion is the original reciprocal Laurent chart morphism. -/
theorem reciprocalGroupIso_left :
    (reciprocalGroupIso K).hom.hom.hom.hom.left = (ProjectiveLine.inversion K).hom := by
  change Spec.map (CommRingCat.ofHom
    (HopfAlgebra.antipodeAlgHom K (LaurentPolynomial K)).toRingHom) = _
  rw [ProjectiveLine.inversion_hom]
  congr 1
  apply CommRingCat.hom_ext
  change (HopfAlgebra.antipodeAlgHom K (LaurentPolynomial K)).toRingHom = _
  suffices HopfAlgebra.antipodeAlgHom K (LaurentPolynomial K) =
      LaurentPolynomial.invert.toAlgHom by exact congrArg AlgHom.toRingHom this
  apply LaurentUnitPoints.hom_ext <;>
    simp [HopfAlgebra.antipodeAlgHom, LaurentPolynomial.antipode_T]

/-- The oriented inclusion into component zero remains a group-scheme morphism. -/
def reciprocalIdentityGroupHom : CommGrp.mk T ⟶ CommGrp.mk (model K n) :=
  (reciprocalGroupIso K).hom ≫ identityComponentGroupHom K n

/-- Its actual underlying map retains the original reciprocal cyclic coordinate. -/
theorem reciprocalIdentityGroupHom_left :
    (reciprocalIdentityGroupHom K n).hom.hom.hom.left =
      (ProjectiveLine.inversion K).hom ≫ (component K n 0).left := by
  change (reciprocalGroupIso K).hom.hom.hom.hom.left ≫ (component K n 0).left = _
  rw [reciprocalGroupIso_left]

end FLT.Mazur.PolygonSplitGroup
