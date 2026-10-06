/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionNaturality
public import FLT.EllipticCurve.CubicTorsionFlat
public import FLT.GroupScheme.KummerPoints

/-! # Equivariant generic points of the actual torsion model -/
open scoped TensorProduct
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R K L : Type u} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsNoetherianRing R] [IsDomain R]
  (W : WeierstrassCurve R) [W.IsElliptic] [DecidableEq L]

/-- The generic convolution point group is the classical subgroup killed by n. -/
def torsionGenericPointsAddEquiv (n : ℕ) [NeZero n] :
    Additive (K ⊗[R] torsionCoordinateRing W n →ₐ[K] L) ≃+
      (nsmulAddMonoidHom n :
        (W.map (algebraMap R L)).toAffine.Point →+
        (W.map (algebraMap R L)).toAffine.Point).ker where
  toEquiv := (Equiv.refl _).trans
    ((Bialgebra.restrictPoints R K L (torsionCoordinateRing W n)).trans
      ((WithConv.equiv _).symm.trans
        (torsionCoordinateClassicalMulEquiv W L n).toEquiv))
  map_add' f g := by
    change (torsionCoordinateClassicalMulEquiv W L n
      (WithConv.toConv (Bialgebra.restrictPoints R K L _ (f.toMul * g.toMul)))).toAdd = _
    rw [Bialgebra.restrictPoints_mul]
    have hc (a b : torsionCoordinateRing W n →ₐ[R] L) :
        WithConv.toConv ((Algebra.TensorProduct.lift a b (fun _ _ ↦ .all _ _)).comp
          (Bialgebra.comulAlgHom R (torsionCoordinateRing W n))) =
        WithConv.toConv a * WithConv.toConv b := by
      apply WithConv.ext
      ext x
      exact (AlgHom.convMul_apply _ _ x).symm
    rw [hc]
    change (torsionCoordinateClassicalMulEquiv W L n
      (WithConv.toConv (Bialgebra.restrictPoints R K L _ f.toMul) *
        WithConv.toConv (Bialgebra.restrictPoints R K L _ g.toMul))).toAdd = _
    exact congrArg Multiplicative.toAdd ((torsionCoordinateClassicalMulEquiv W L n).map_mul _ _)

/-- The generic point comparison commutes with postcomposition over the generic field. -/
theorem torsionGenericPointsAddEquiv_postcomp (n : ℕ) [NeZero n]
    (σ : L →ₐ[K] L)
    (p : K ⊗[R] torsionCoordinateRing W n →ₐ[K] L) :
    (torsionGenericPointsAddEquiv W n (Additive.ofMul (σ.comp p))).val =
      Affine.Point.map (W' := W.toAffine) (σ.restrictScalars R)
        (torsionGenericPointsAddEquiv W n (Additive.ofMul p)).val := by
  exact torsionCoordinateClassicalMulEquiv_postcomp W
    (σ.restrictScalars R) n
      (WithConv.toConv (Bialgebra.restrictPoints R K L _ p))

/-- A field endomorphism acts on the classical subgroup killed by n. -/
def classicalTorsionMap (n : ℕ) (f : L →ₐ[R] L) :
    (nsmulAddMonoidHom n :
      (W.map (algebraMap R L)).toAffine.Point →+
      (W.map (algebraMap R L)).toAffine.Point).ker →+
    (nsmulAddMonoidHom n :
      (W.map (algebraMap R L)).toAffine.Point →+
      (W.map (algebraMap R L)).toAffine.Point).ker where
  toFun P := ⟨Affine.Point.map (W' := W.toAffine) f P.val, by
    change n • Affine.Point.map f P.val = 0
    rw [← map_nsmul, show n • P.val = 0 from P.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

/-- Transport the actual generic points through a specified equivariant classical comparison. -/
def torsionGenericPointsEquivariant (n : ℕ) [NeZero n]
    {X : Type u} [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]
    (e : (nsmulAddMonoidHom n :
      (W.map (algebraMap R L)).toAffine.Point →+
      (W.map (algebraMap R L)).toAffine.Point).ker ≃+ X)
    (he : ∀ (σ : L ≃ₐ[K] L) P,
      e (classicalTorsionMap W n (σ.toAlgHom.restrictScalars R) P) = σ • e P) :
    Additive (K ⊗[R] torsionCoordinateRing W n →ₐ[K] L) →+[L ≃ₐ[K] L] X :=
  { ((torsionGenericPointsAddEquiv W n).trans e).toAddMonoidHom with
    map_smul' := by
      intro σ p
      change e (torsionGenericPointsAddEquiv W n (σ • p)) =
        σ • e (torsionGenericPointsAddEquiv W n p)
      rw [← he]
      apply congrArg e
      apply Subtype.ext
      exact torsionGenericPointsAddEquiv_postcomp W n σ.toAlgHom p.toMul }

/-- The equivariant generic point comparison is bijective. -/
theorem torsionGenericPointsEquivariant_bijective (n : ℕ) [NeZero n]
    {X : Type u} [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]
    (e : (nsmulAddMonoidHom n :
      (W.map (algebraMap R L)).toAffine.Point →+
      (W.map (algebraMap R L)).toAffine.Point).ker ≃+ X)
    (he : ∀ (σ : L ≃ₐ[K] L) P,
      e (classicalTorsionMap W n (σ.toAlgHom.restrictScalars R) P) = σ • e P) :
    Function.Bijective (torsionGenericPointsEquivariant W n e he) :=
  ((torsionGenericPointsAddEquiv W n).trans e).bijective

/-- The actual integral torsion model proves finite flatness for invertible-order torsion. -/
theorem isFiniteFlat_of_unit_torsion (n : ℕ) [NeZero n] (hn : IsUnit (n : R))
    {X : Type u} [AddCommGroup X] [DistribMulAction (L ≃ₐ[K] L) X]
    (e : (nsmulAddMonoidHom n :
      (W.map (algebraMap R L)).toAffine.Point →+
      (W.map (algebraMap R L)).toAffine.Point).ker ≃+ X)
    (he : ∀ (σ : L ≃ₐ[K] L) P,
      e (classicalTorsionMap W n (σ.toAlgHom.restrictScalars R) P) = σ • e P) :
    GaloisModule.IsFiniteFlat R K L X := by
  have := torsionCoordinate_isFiniteFlat W n hn
  have : Algebra.Etale K (K ⊗[R] torsionCoordinateRing W n) :=
    torsionCoordinate_field_etale W n K (by simpa using hn.map (algebraMap R K))
  exact ⟨torsionCoordinateRing W n, inferInstance, inferInstance, inferInstance,
    inferInstance, torsionGenericPointsEquivariant W n e he,
      torsionGenericPointsEquivariant_bijective W n e he⟩

end WeierstrassCurve.CubicCharts
