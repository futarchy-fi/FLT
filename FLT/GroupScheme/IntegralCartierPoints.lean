/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralCartierDual
public import FLT.GroupScheme.CartierDualCharacterGroup
public import FLT.GroupScheme.FiniteFlatFiltration
public import FLT.GaloisRepresentation.HardlyRamified.FiniteCharacterDual

/-!
# Integral Cartier duality and the geometric character module

The integral dual model's full geometric point group is identified with
the character dual of the original chosen point module. The identification
is additive, bijective, and equivariant for the rational absolute Galois group.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.CartierDual

/-- Precomposition with a Hopf equivalence gives an additive equivalence
of the full geometric point groups. -/
def precompPointsEquiv {K A B : Type} (L : Type) [Field K] [Field L] [Algebra K L]
    [CommRing A] [CommRing B] [Bialgebra K A] [Bialgebra K B] (e : A ≃ₐc[K] B) :
    Additive (B →ₐ[K] L) ≃+ Additive (A →ₐ[K] L) where
  toFun f := Additive.ofMul (f.toMul.comp e.toAlgEquiv.toAlgHom)
  invFun f := Additive.ofMul (f.toMul.comp e.symm.toAlgEquiv.toAlgHom)
  left_inv f := by ext a; simp
  right_inv f := by ext a; simp
  map_add' f g := congrArg Additive.ofMul
    (BialgHom.algHom_mul_comp f.toMul g.toMul e.toBialgHom)

/-- Precomposition over the base field is Galois equivariant. -/
theorem precompPointsEquiv_smul {K A B : Type} (L : Type)
    [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
    [Bialgebra K A] [Bialgebra K B] (e : A ≃ₐc[K] B)
    (σ : L ≃ₐ[K] L) (p : Additive (B →ₐ[K] L)) :
    precompPointsEquiv L e (σ • p) = σ • precompPointsEquiv L e p := rfl

/-- Transport multiplicative characters along an equivalence of their source groups. -/
def characterSourceEquiv {G H C : Type*} [Monoid G] [Monoid H] [CommMonoid C]
    (e : G ≃* H) : (H →* C) ≃* (G →* C) where
  toFun φ := φ.comp e.toMonoidHom
  invFun φ := φ.comp e.symm.toMonoidHom
  left_inv φ := by ext h; simp
  right_inv φ := by ext g; simp
  map_mul' _ _ := rfl

end HopfAlgebra.CartierDual

namespace ThreeAdicPlan

open HopfAlgebra.CartierDual

attribute [local instance] HopfAlgebra.pointsCommGroup

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]

/-- The chosen model comparison, in multiplicative notation on geometric points. -/
def FiniteFlatObject.genericPointsMulEquiv (H : FiniteFlatObject R) :
    (ℚ ⊗[R] H.model.CoordinateRing →ₐ[ℚ] AlgebraicClosure ℚ) ≃* Multiplicative H.points :=
  (AddEquiv.ofBijective H.model.points.toAddMonoidHom
    H.model.points_bijective).toMultiplicativeRight

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- The inverse chosen point comparison is Galois equivariant. -/
theorem FiniteFlatObject.genericPointsMulEquiv_symm_smul (H : FiniteFlatObject R)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : H.points) :
    H.genericPointsMulEquiv.symm (Multiplicative.ofAdd (σ • w)) =
      σ • H.genericPointsMulEquiv.symm (Multiplicative.ofAdd w) :=
  H.model.inversePoints.map_smul σ w

/-- The geometric points of the actual integral dual form the character
group of the original chosen geometric point module. -/
def FiniteFlatObject.cartierDualPointEquiv (H : FiniteFlatObject R) :
    H.cartierDual.points ≃+ H.points.characterDual :=
  (precompPointsEquiv (AlgebraicClosure ℚ)
    (baseChangeBialgEquiv (R := R) (A := H.model.CoordinateRing) ℚ).symm).trans
      ((geometricCharactersMulEquiv ℚ (AlgebraicClosure ℚ)
        (ℚ ⊗[R] H.model.CoordinateRing)).toAdditive.trans
          (characterSourceEquiv H.genericPointsMulEquiv.symm).toAdditive)

/-- The integral-dual point comparison respects the full rational Galois action. -/
theorem FiniteFlatObject.cartierDualPointEquiv_smul (H : FiniteFlatObject R)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : H.cartierDual.points) :
    H.cartierDualPointEquiv (σ • v) = σ • H.cartierDualPointEquiv v := by
  let p : Additive (ℚ ⊗[R] HopfAlgebra.CartierDual R H.model.CoordinateRing →ₐ[ℚ]
      AlgebraicClosure ℚ) := v
  apply MonoidHom.ext
  intro w
  change geometricCharactersEquiv ℚ (AlgebraicClosure ℚ) (ℚ ⊗[R] H.model.CoordinateRing)
    ((precompPointsEquiv (AlgebraicClosure ℚ)
      (baseChangeBialgEquiv (R := R) (A := H.model.CoordinateRing) ℚ).symm) (σ • p)).toMul
    (H.genericPointsMulEquiv.symm w) =
      σ • geometricCharactersEquiv ℚ (AlgebraicClosure ℚ) (ℚ ⊗[R] H.model.CoordinateRing)
        ((precompPointsEquiv (AlgebraicClosure ℚ)
          (baseChangeBialgEquiv (R := R) (A := H.model.CoordinateRing) ℚ).symm) p).toMul
        (H.genericPointsMulEquiv.symm (Multiplicative.ofAdd (σ⁻¹ • w.toAdd)))
  rw [precompPointsEquiv_smul]
  let ψ := ((precompPointsEquiv (AlgebraicClosure ℚ)
    (baseChangeBialgEquiv (R := R) (A := H.model.CoordinateRing) ℚ).symm) p).toMul
  change geometricCharactersEquiv ℚ (AlgebraicClosure ℚ) (ℚ ⊗[R] H.model.CoordinateRing)
    (σ • ψ) (H.genericPointsMulEquiv.symm w) =
      σ • geometricCharactersEquiv ℚ (AlgebraicClosure ℚ) (ℚ ⊗[R] H.model.CoordinateRing)
        ψ (H.genericPointsMulEquiv.symm (Multiplicative.ofAdd (σ⁻¹ • w.toAdd)))
  rw [geometricCharactersEquiv_smul, FiniteFlatObject.genericPointsMulEquiv_symm_smul]
  rfl

/-- The equivariant additive comparison from integral dual points to characters. -/
def FiniteFlatObject.cartierDualPoints (H : FiniteFlatObject R) :
    H.cartierDual.points →+[AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ]
      H.points.characterDual where
  toAddMonoidHom := H.cartierDualPointEquiv.toAddMonoidHom
  map_smul' := H.cartierDualPointEquiv_smul

/-- Every character is represented by a unique point of the integral Cartier dual. -/
theorem FiniteFlatObject.cartierDualPoints_bijective (H : FiniteFlatObject R) :
    Function.Bijective H.cartierDualPoints := H.cartierDualPointEquiv.bijective

end ThreeAdicPlan
