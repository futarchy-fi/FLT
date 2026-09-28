/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantCartierDual
public import FLT.GroupScheme.ConstantFiltrationPurity
public import FLT.GroupScheme.IntegralCartierPoints
public import FLT.GroupScheme.BialgebraBaseChange

/-!
# Constant points of the Cartier dual of the cube-root group

The integral Hopf comparison induces a bijective equivariant additive map
from the existing constant-three point module onto all geometric characters
of the cube-root model. Thus this full character module is trivial and killed by three.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- An integral Hopf equivalence induces a bijection on the chosen geometric point groups. -/
theorem FiniteFlatObject.pointMap_bijective {R : Type} [CommRing R] [Algebra R ℚ]
    {H J : FiniteFlatObject R} (e : J.model.CoordinateRing ≃ₐc[R] H.model.CoordinateRing) :
    Function.Bijective (FiniteFlatObject.pointMap (H := H) (J := J) e.toBialgHom) := by
  let e' := bialgebraBaseChangeEquiv R ℚ J.model.CoordinateRing H.model.CoordinateRing e
  exact J.model.points_bijective.comp
    ((HopfAlgebra.CartierDual.precompPointsEquiv (AlgebraicClosure ℚ) e').bijective.comp
      (AddEquiv.ofBijective H.model.points.toAddMonoidHom H.model.points_bijective).symm.bijective)

/-- All geometric characters of the cube-root group are represented by constant-three points. -/
def muThreeDualConstantPoints : constantThree.points →+[Γ] muThree.points.characterDual :=
  muThree.cartierDualPoints.comp
    (FiniteFlatObject.pointMap (H := constantThree) (J := muThree.cartierDual)
      muThreeCartierDualEquiv.toBialgHom)

/-- The constant-three comparison accounts for every geometric character exactly once. -/
theorem muThreeDualConstantPoints_bijective : Function.Bijective muThreeDualConstantPoints :=
  muThree.cartierDualPoints_bijective.comp
    (FiniteFlatObject.pointMap_bijective muThreeCartierDualEquiv)

/-- The full character group of the cube-root model is killed by three. -/
theorem muThree_characterDual_nsmul (φ : muThree.points.characterDual) : (3 : ℕ) • φ = 0 := by
  obtain ⟨a, rfl⟩ := muThreeDualConstantPoints_bijective.2 φ
  rw [← map_nsmul, constantThree_nsmul, map_zero]

/-- The full contragredient Galois action on the cube-root character group is trivial. -/
theorem muThree_characterDual_smul (σ : Γ) (φ : muThree.points.characterDual) : σ • φ = φ := by
  obtain ⟨a, rfl⟩ := muThreeDualConstantPoints_bijective.2 φ
  rw [← map_smul, constantThree_smul]

end ThreeAdicPlan
