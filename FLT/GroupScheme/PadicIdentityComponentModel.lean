/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPoints
public import FLT.GroupScheme.PadicIdentityComponentHopf
public import FLT.GroupScheme.RaynaudFlatKernelExactness

/-!
# The connected identity-component model over the three-adic integers

The actual component quotient defines a finite-flat model with étale generic
fibre. Its geometric points embed into the original abelian point group, and
the quotient map gives the identity-component inclusion in `ModelHom`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.FF

variable (X : FF ℤ_[3] ℚ_[3])

/-- The Hopf algebra of the identity component is finite flat. -/
instance identityComponent_finiteFlat :
    HopfAlgebra.IsFiniteFlat ℤ_[3] (X.ComponentAlgebra X.identityComponentIndex) := ⟨⟩

/-- The identity component has étale generic fibre. -/
instance identityComponent_genericEtale :
    Algebra.Etale ℚ_[3] (ℚ_[3] ⊗[ℤ_[3]] X.ComponentAlgebra X.identityComponentIndex) :=
  X.quotient_genericEtale X.identityComponentIdeal

/-- The coordinate map on generic fibres of the identity-component inclusion. -/
def identityComponentGenericProjection :
    ℚ_[3] ⊗[ℤ_[3]] X.CoordinateRing →ₐc[ℚ_[3]]
      ℚ_[3] ⊗[ℤ_[3]] X.ComponentAlgebra X.identityComponentIndex :=
  Bialgebra.TensorProduct.map (BialgHom.id ℚ_[3] ℚ_[3]) X.identityComponentBialgHom

/-- Base change preserves surjectivity of the coordinate quotient. -/
theorem identityComponentGenericProjection_surjective :
    Function.Surjective X.identityComponentGenericProjection :=
  Algebra.TensorProduct.map_surjective (f := AlgHom.id ℚ_[3] ℚ_[3])
    (g := X.identityComponentProjection) Function.surjective_id Ideal.Quotient.mk_surjective

/-- The identity component's geometric points map equivariantly into the given point group. -/
def identityComponentPointsMap :
    Additive (ℚ_[3] ⊗[ℤ_[3]] X.ComponentAlgebra X.identityComponentIndex →ₐ[ℚ_[3]]
      AlgebraicClosure ℚ_[3]) →+[AlgebraicClosure ℚ_[3] ≃ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3]]
      X.Points :=
  X.points.comp (BialgHom.precompPoints X.identityComponentGenericProjection)

/-- A geometric point of the component is determined by its point in the ambient model. -/
theorem identityComponentPointsMap_injective : Function.Injective X.identityComponentPointsMap := by
  intro p q h
  have hpq := X.points_bijective.1 h
  apply Additive.toMul.injective
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := X.identityComponentGenericProjection_surjective b
  exact AlgHom.congr_fun (congrArg Additive.toMul hpq) a

/-- The component Hopf algebra is cocommutative, as detected by its abelian generic points. -/
instance identityComponent_cocomm :
    Coalgebra.IsCocomm ℤ_[3] (X.ComponentAlgebra X.identityComponentIndex) :=
  cocomm_of_injective_points X.identityComponentPointsMap.toAddMonoidHom
    X.identityComponentPointsMap_injective

attribute [local instance] HopfAlgebra.pointsCommGroup

/-- The connected identity component as a model in the existing local `FF` vocabulary. -/
def identityComponent : FF ℤ_[3] ℚ_[3] where
  CoordinateRing := X.ComponentAlgebra X.identityComponentIndex
  Points := Additive (ℚ_[3] ⊗[ℤ_[3]] X.ComponentAlgebra X.identityComponentIndex →ₐ[ℚ_[3]]
    AlgebraicClosure ℚ_[3])
  points :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  points_bijective := Function.bijective_id

/-- The integral closed-subgroup inclusion of the identity component. -/
def identityComponentInclusion : ModelHom X.identityComponent X :=
  X.identityComponentBialgHom

/-- The inclusion is represented by the specified quotient map, not a chosen equivalent map. -/
@[simp] theorem identityComponentInclusion_apply (a : X.CoordinateRing) :
    X.identityComponentInclusion a = X.identityComponentProjection a := rfl

/-- The identity-component inclusion is a closed immersion. -/
theorem identityComponentInclusion_surjective : Function.Surjective X.identityComponentInclusion :=
  X.identityComponentBialgHom_surjective

/-- The identity-component model has connected coordinate algebra. -/
theorem identityComponent_idempotent_trivial (d : X.identityComponent.CoordinateRing)
    (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 :=
  X.componentAlgebra_idempotent_trivial X.identityComponentIndex d hd

/-- The generic restriction of the inclusion is the specified injection on geometric points. -/
theorem identityComponentInclusion_genericHom :
    genericHom X.identityComponentInclusion = X.identityComponentPointsMap := by
  ext p
  exact genericHom_points X.identityComponentInclusion p

/-- The identity-component inclusion is injective on geometric generic points. -/
theorem identityComponentInclusion_genericHom_injective :
    Function.Injective (genericHom X.identityComponentInclusion) := by
  rw [X.identityComponentInclusion_genericHom]
  exact X.identityComponentPointsMap_injective

end ThreeAdicPlan.FF
