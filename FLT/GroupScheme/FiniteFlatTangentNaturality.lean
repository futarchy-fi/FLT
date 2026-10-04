/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatCotangent
public import FLT.Mathlib.RingTheory.AugmentationTangentEquiv

/-! # Naturality of tangent-cotangent duality for the original integral models -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K M : Type} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup M] [Module R M]

/-- Actual Leibniz functionals on the original coordinate algebra. -/
abbrev FF.Tangent (X : FF R K) :=
  (Bialgebra.counitAlgHom R X.CoordinateRing).augmentationTangent (M := M)

/-- The cotangent quotient represents these original tangent functionals. -/
def FF.cotangentTangentEquiv (X : FF R K) :
    (X.Cotangent →ₗ[R] M) ≃ₗ[R] X.Tangent (M := M) :=
  AlgHom.augmentationTangentEquiv _

/-- Tangent maps are precomposition with the actual integral coordinate maps. -/
def ModelHom.tangentMap {X Y : FF R K} (f : ModelHom X Y) :
    X.Tangent (M := M) →ₗ[R] Y.Tangent (M := M) where
  toFun d := ⟨d.val.comp f.toAlgHom.toLinearMap, by
    intro a b
    change d.val (f (a * b)) = _
    rw [map_mul, d.property]
    change Coalgebra.counit (f a) • d.val (f b) +
      Coalgebra.counit (f b) • d.val (f a) = _
    rw [CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
    rfl⟩
  map_add' d e := by apply Subtype.ext; ext a; rfl
  map_smul' r d := by apply Subtype.ext; ext a; rfl

/-- Cotangent projection commutes with the original integral model map. -/
theorem ModelHom.cotangentMap_projection {X Y : FF R K} (f : ModelHom X Y)
    (a : Y.CoordinateRing) :
    f.cotangentMap ((Bialgebra.counitAlgHom R Y.CoordinateRing).augmentationCotangent a) =
      (Bialgebra.counitAlgHom R X.CoordinateRing).augmentationCotangent (f a) := by
  change X.cotangentIdeal.toCotangent
    ⟨f (a - algebraMap R Y.CoordinateRing (Coalgebra.counit a)), _⟩ =
      X.cotangentIdeal.toCotangent
        ⟨f a - algebraMap R X.CoordinateRing (Coalgebra.counit (f a)), _⟩
  apply congrArg X.cotangentIdeal.toCotangent
  apply Subtype.ext
  change f (a - algebraMap R Y.CoordinateRing (Coalgebra.counit a)) =
    f a - algebraMap R X.CoordinateRing (Coalgebra.counit (f a))
  rw [map_sub, AlgHomClass.commutes f, CoalgHomClass.counit_comp_apply]

/-- The tangent-cotangent equivalence is natural for the actual integral morphism. -/
theorem ModelHom.cotangentTangent_naturality {X Y : FF R K} (f : ModelHom X Y)
    (d : X.Cotangent →ₗ[R] M) :
    f.tangentMap (X.cotangentTangentEquiv d) =
      Y.cotangentTangentEquiv (d.comp f.cotangentMap) := by
  apply Subtype.ext
  ext a
  change d ((Bialgebra.counitAlgHom R X.CoordinateRing).augmentationCotangent (f a)) =
    d (f.cotangentMap ((Bialgebra.counitAlgHom R Y.CoordinateRing).augmentationCotangent a))
  rw [ModelHom.cotangentMap_projection]

/-- Tangent functoriality preserves the identity of the original model. -/
theorem ModelHom.tangentMap_id (X : FF R K) :
    ModelHom.tangentMap (M := M) (X := X) (Y := X) (BialgHom.id R X.CoordinateRing) =
      LinearMap.id := by ext d a; rfl

/-- Tangent functoriality preserves composition of the original model morphisms. -/
theorem ModelHom.tangentMap_comp {X Y Z : FF R K} (f : ModelHom X Y) (g : ModelHom Y Z) :
    ModelHom.tangentMap (M := M) (X := X) (Y := Z) (f.comp g) =
      g.tangentMap.comp f.tangentMap := by ext d a; rfl

end ThreeAdicPlan
