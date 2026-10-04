/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalIdentityComponentHopf
public import FLT.GroupScheme.HopfPoints
public import FLT.GroupScheme.RaynaudFlatKernelExactness

/-! # Connected level models over the original rational-place integers -/

@[expose] public noncomputable section
open scoped TensorProduct
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.FF
attribute [local instance] rationalFiniteFlat_henselian rationalSpecialFiber_artinian
variable {p : ℕ} [Fact p.Prime]
  (X : FF ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
    ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ))
local notation "O" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- The Hopf algebra of the identity component is finite flat. -/
instance rationalIdentityComponent_finiteFlat :
    HopfAlgebra.IsFiniteFlat O (X.RationalComponentAlgebra
      X.rationalIdentityComponentIndex) := ⟨⟩

/-- The identity component has étale generic fibre. -/
instance rationalIdentityComponent_genericEtale :
    Algebra.Etale K (K ⊗[O] X.RationalComponentAlgebra X.rationalIdentityComponentIndex) :=
  X.quotient_genericEtale X.rationalIdentityComponentIdeal

/-- The coordinate map on generic fibres of the identity-component inclusion. -/
def rationalIdentityComponentGenericProjection :
    K ⊗[O] X.CoordinateRing →ₐc[K]
      K ⊗[O] X.RationalComponentAlgebra X.rationalIdentityComponentIndex :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) X.rationalIdentityComponentBialgHom

/-- Base change preserves surjectivity of the coordinate quotient. -/
theorem rationalIdentityComponentGenericProjection_surjective :
    Function.Surjective X.rationalIdentityComponentGenericProjection :=
  Algebra.TensorProduct.map_surjective (f := AlgHom.id K K)
    (g := X.rationalIdentityComponentProjection) Function.surjective_id Ideal.Quotient.mk_surjective

/-- The identity component's geometric points map equivariantly into the given point group. -/
def rationalIdentityComponentPointsMap :
    Additive (K ⊗[O] X.RationalComponentAlgebra X.rationalIdentityComponentIndex →ₐ[K]
      AlgebraicClosure K) →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K]
      X.Points :=
  X.points.comp (BialgHom.precompPoints X.rationalIdentityComponentGenericProjection)

/-- A geometric point of the component is determined by its point in the ambient model. -/
theorem rationalIdentityComponentPointsMap_injective : Function.Injective
  X.rationalIdentityComponentPointsMap := by
  intro p q h
  have hpq := X.points_bijective.1 h
  apply Additive.toMul.injective
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := X.rationalIdentityComponentGenericProjection_surjective b
  exact AlgHom.congr_fun (congrArg Additive.toMul hpq) a

/-- The component Hopf algebra is cocommutative, as detected by its abelian generic points. -/
instance rationalIdentityComponent_cocomm :
    Coalgebra.IsCocomm O (X.RationalComponentAlgebra X.rationalIdentityComponentIndex) :=
  cocomm_of_injective_points X.rationalIdentityComponentPointsMap.toAddMonoidHom
    X.rationalIdentityComponentPointsMap_injective

attribute [local instance] HopfAlgebra.pointsCommGroup

/-- The connected identity component as a model in the existing local `FF` vocabulary. -/
def rationalIdentityComponent : FF O K where
  CoordinateRing := X.RationalComponentAlgebra X.rationalIdentityComponentIndex
  Points := Additive (K ⊗[O] X.RationalComponentAlgebra X.rationalIdentityComponentIndex
    →ₐ[K]
    AlgebraicClosure K)
  points :=
    { toFun := id
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  points_bijective := Function.bijective_id

/-- The integral closed-subgroup inclusion of the identity component. -/
def rationalIdentityComponentInclusion : ModelHom X.rationalIdentityComponent X :=
  X.rationalIdentityComponentBialgHom

/-- The inclusion is represented by the specified quotient map, not a chosen equivalent map. -/
@[simp] theorem rationalIdentityComponentInclusion_apply (a : X.CoordinateRing) :
    X.rationalIdentityComponentInclusion a = X.rationalIdentityComponentProjection a := rfl

/-- The identity-component inclusion is a closed immersion. -/
theorem rationalIdentityComponentInclusion_surjective : Function.Surjective
  X.rationalIdentityComponentInclusion :=
  X.rationalIdentityComponentBialgHom_surjective

/-- The identity-component model has connected coordinate algebra. -/
theorem rationalIdentityComponent_idempotent_trivial (d :
  X.rationalIdentityComponent.CoordinateRing)
    (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 :=
  X.rationalComponentAlgebra_idempotent_trivial X.rationalIdentityComponentIndex d hd

/-- The generic restriction of the inclusion is the specified injection on geometric points. -/
theorem rationalIdentityComponentInclusion_genericHom :
    genericHom X.rationalIdentityComponentInclusion = X.rationalIdentityComponentPointsMap := by
  ext p
  exact genericHom_points X.rationalIdentityComponentInclusion p

/-- The identity-component inclusion is injective on geometric generic points. -/
theorem rationalIdentityComponentInclusion_genericHom_injective :
    Function.Injective (genericHom X.rationalIdentityComponentInclusion) := by
  rw [X.rationalIdentityComponentInclusion_genericHom]
  exact X.rationalIdentityComponentPointsMap_injective
end ThreeAdicPlan.FF
