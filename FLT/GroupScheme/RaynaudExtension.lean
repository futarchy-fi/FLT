/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Faithfulness of the generic fibre of finite flat models

`FF` retains the witnesses in `GaloisModule.IsFiniteFlat`. Model morphisms are
contravariant bialgebra maps, and their generic restrictions are equivariant additive
maps. Flatness and the étale generic fibre imply that this restriction is injective.
The existence part of Raynaud's extension theorem is not established here.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

/-- A chosen finite flat Hopf-algebra model, with an abelian geometric generic fibre.
The fields are precisely model and comparison data of `GaloisModule.IsFiniteFlat`;
no morphism-extension or classification assertion is included. The fraction field
can be specified explicitly, for example `FF ℤ_[3] ℚ_[3]`. -/
structure FF (R : Type u) [CommRing R] (K : Type u := FractionRing R)
    [Field K] [Algebra R K] where
  CoordinateRing : Type u
  [commRing : CommRing CoordinateRing]
  [hopfAlgebra : HopfAlgebra R CoordinateRing]
  [finiteFlat : HopfAlgebra.IsFiniteFlat R CoordinateRing]
  [genericEtale : Algebra.Etale K (K ⊗[R] CoordinateRing)]
  Points : Type u
  [addCommGroup : AddCommGroup Points]
  [action : DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) Points]
  points : Additive (K ⊗[R] CoordinateRing →ₐ[K] AlgebraicClosure K) →+[
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] Points
  points_bijective : Function.Bijective points

attribute [instance] FF.commRing FF.hopfAlgebra FF.finiteFlat FF.genericEtale
  FF.addCommGroup FF.action

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- The chosen model witnesses the existing finite-flat Galois-module predicate. -/
theorem FF.isFiniteFlat (X : FF R K) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) X.Points :=
  ⟨X.CoordinateRing, inferInstance, inferInstance, inferInstance, inferInstance,
    X.points, X.points_bijective⟩

/-- The geometric point group of a chosen model is finite. -/
instance (X : FF R K) : Finite X.Points := X.isFiniteFlat.finite

/-- The Galois action on the geometric point group is continuous for the discrete topology. -/
instance (X : FF R K) : ContinuousSMulDiscrete
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points :=
  X.isFiniteFlat.continuousSMulDiscrete

/-- A single power of `p` annihilates every geometric point. For flat models with
étale generic fibre this is the usual condition of being killed by a power of `p`. -/
def KilledByPowerOf (p : ℕ) (X : FF R K) : Prop :=
  ∃ n : ℕ, ∀ x : X.Points, p ^ n • x = 0

/-- Equivariant additive maps between the geometric generic fibres. -/
abbrev GenericGaloisHom (X Y : FF R K) :=
  X.Points →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] Y.Points

/-- Morphisms of the integral models, contravariantly on coordinate Hopf algebras.
A bialgebra homomorphism between Hopf algebras automatically respects antipodes. -/
abbrev ModelHom (X Y : FF R K) := Y.CoordinateRing →ₐc[R] X.CoordinateRing

/-- The chosen point comparison as an additive equivalence. -/
def FF.pointsEquiv (X : FF R K) :
    Additive (K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) ≃+ X.Points :=
  AddEquiv.ofBijective X.points.toAddMonoidHom X.points_bijective

/-- The inverse point comparison, retaining its Galois equivariance. -/
def FF.inversePoints (X : FF R K) :
    X.Points →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K]
      Additive (K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) where
  toFun := X.pointsEquiv.symm
  map_zero' := X.pointsEquiv.symm.map_zero
  map_add' := X.pointsEquiv.symm.map_add
  map_smul' σ x := by
    apply X.points_bijective.1
    change X.pointsEquiv (X.pointsEquiv.symm (σ • x)) =
      X.points (σ • X.pointsEquiv.symm x)
    calc
      X.pointsEquiv (X.pointsEquiv.symm (σ • x)) = σ • x :=
        X.pointsEquiv.apply_symm_apply _
      _ = σ • X.points (X.pointsEquiv.symm x) :=
        (congrArg (σ • ·) (X.pointsEquiv.apply_symm_apply x)).symm
      _ = X.points (σ • X.pointsEquiv.symm x) := (map_smul X.points σ _).symm


/-- Base change of a model morphism to the chosen generic field. -/
def ModelHom.baseChange {X Y : FF R K} (f : ModelHom X Y) :
    K ⊗[R] Y.CoordinateRing →ₐc[K] K ⊗[R] X.CoordinateRing :=
  Bialgebra.TensorProduct.map (BialgHom.id K K) f

/-- Restriction of a model morphism to its equivariant map on geometric generic points. -/
def genericHom {X Y : FF R K} (f : ModelHom X Y) : GenericGaloisHom X Y :=
  Y.points.comp ((BialgHom.precompPoints f.baseChange).comp X.inversePoints)

/-- On a geometric point, restriction is precomposition with the base-changed map. -/
@[simp] theorem genericHom_points {X Y : FF R K} (f : ModelHom X Y)
    (p : Additive (K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K)) :
    genericHom f (X.points p) = Y.points (BialgHom.precompPoints f.baseChange p) := by
  change Y.points (BialgHom.precompPoints f.baseChange
    (X.pointsEquiv.symm (X.pointsEquiv p))) = _
  rw [X.pointsEquiv.symm_apply_apply]

/-- Flatness makes restriction of model morphisms to the generic Hopf algebra injective. -/
theorem ModelHom.baseChange_injective [IsFractionRing R K] (X Y : FF R K) :
    Function.Injective (ModelHom.baseChange (X := X) (Y := Y)) := by
  intro f g h
  ext y
  apply Algebra.TensorProduct.includeRight_injective (A := K)
    (IsFractionRing.injective R K)
  exact congrArg (fun a : K ⊗[R] Y.CoordinateRing →ₐc[K] K ⊗[R] X.CoordinateRing =>
    a (1 ⊗ₜ[R] y)) h

/-- Geometric generic restriction is faithful: finite flat models have at most one
extension of a given generic morphism. This does not require Raynaud's ramification bound. -/
theorem genericHom_injective [PerfectField K] [IsFractionRing R K] (X Y : FF R K) :
    Function.Injective (genericHom (X := X) (Y := Y)) := by
  intro f g h
  apply ModelHom.baseChange_injective X Y
  ext z
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing)).injective
  ext p
  have hp := congrArg (fun a : GenericGaloisHom X Y => a (X.points (Additive.ofMul p))) h
  rw [genericHom_points, genericHom_points] at hp
  exact congrArg (fun q : Additive (K ⊗[R] Y.CoordinateRing →ₐ[K] AlgebraicClosure K) =>
    q.toMul z) (Y.points_bijective.1 hp)

/-- The uniqueness part of Raynaud's theorem over `ℤ_[3]`. Neither the power-of-three
hypotheses nor the ramification inequality are needed for this part. -/
theorem raynaud_extend_generic_morphism_unique
    (X Y : FF ℤ_[3] ℚ_[3]) (f : GenericGaloisHom X Y)
    (fO gO : ModelHom X Y) (hf : genericHom fO = f) (hg : genericHom gO = f) :
    fO = gO :=
  genericHom_injective X Y (hf.trans hg.symm)

end ThreeAdicPlan
