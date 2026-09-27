/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionHopf
public import FLT.GroupScheme.ModelPoints

/-!
# Finite-flat odd torsion on short Weierstrass models

The explicit Hopf order and its equivariant point comparison give finite flatness
without using the general good-reduction flatness admission.
-/

@[expose] public section

open scoped TensorProduct
universe u
namespace WeierstrassCurve
variable {R k : Type u} [CommRing R] [Field k] [Algebra R k] [DecidableEq k]
    (W : WeierstrassCurve R) {n : ℕ} (hn : Odd n) (ξ : R)
    (hT : (W.map (algebraMap R k)).toAffine.Nonsingular
      (algebraMap R k ξ) (algebraMap R k 0))
    (htwo : 2 • Affine.Point.some _ _ hT = 0)
    [IsDedekindDomain R] [Module.IsTorsionFree R k]
    [(W.map (algebraMap R k)).IsElliptic] [W.IsShortNF]
    (K : Type u) [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K]
    [Algebra K k] [IsScalarTower R K k] [IsGalois K k] [IsSepClosed k]
include hn hT htwo in
/-- A short good-reduction model with integral two-torsion gives finite-flat odd torsion. -/
theorem isFiniteFlat_of_short_twoTorsion
    (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : R)) (ht : W.toAffine.Equation ξ 0)
    {X : Type u} [AddCommGroup X] [DistribMulAction (k ≃ₐ[K] k) X]
    (e : W.oddTorsionPointSet (k := k) n ≃+ X)
    (he : ∀ (σ : k ≃ₐ[K] k) P, e (W.oddTorsionPointMap (σ.toAlgHom.restrictScalars R) P) =
      σ • e P) : GaloisModule.IsFiniteFlat R K k X := by
  obtain ⟨d, hd⟩ := W.exists_oddTorsionCoaddition_short hn ξ hT htwo K hΔ h2 ht
  let H := W.oddTorsionCoordinateOrder hn ξ 0 hT htwo
  let := W.oddTorsionHopfOfCoaddition hn ξ 0 hT htwo K d hd
  let : HopfAlgebra.IsFiniteFlat R H := W.finiteFlat_oddTorsionCoordinateOrder hn ξ 0 hT htwo
  let : Algebra.Etale K (K ⊗[R] H) :=
    W.etale_oddTorsionCoordinateOrder_genericFiber hn ξ 0 hT htwo K
  let a := e.symm.toEquiv.trans (W.oddTorsionCoordinatePointsEquiv hn ξ 0 hT htwo)
  apply Bialgebra.isFiniteFlat_of_pointsEquiv R K k H X a
  · intro P Q
    apply AlgHom.ext
    intro f
    change Algebra.TensorProduct.lift
      (W.oddTorsionEvaluationPoint hn ξ 0 hT htwo (e.symm P))
      (W.oddTorsionEvaluationPoint hn ξ 0 hT htwo (e.symm Q))
      (fun _ _ ↦ .all _ _) (d f) = f.val (e.symm (P + Q))
    rw [map_add]
    rw [← hd]
    have hh (z : H ⊗[R] H) : Algebra.TensorProduct.lift
        (W.oddTorsionEvaluationPoint hn ξ 0 hT htwo (e.symm P))
        (W.oddTorsionEvaluationPoint hn ξ 0 hT htwo (e.symm Q))
        (fun _ _ ↦ .all _ _) z =
        W.oddTorsionTensorEvaluation hn ξ 0 hT htwo z (e.symm P, e.symm Q) := by
      induction z using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add a b ha hb => simp [ha, hb]
    exact hh _
  · intro σ P
    have h : e.symm (σ • P) = W.oddTorsionPointMap (σ.toAlgHom.restrictScalars R) (e.symm P) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    change W.oddTorsionEvaluationPoint hn ξ 0 hT htwo (e.symm (σ • P)) = _
    rw [h]
    exact W.oddTorsionEvaluationPoint_equivariant hn ξ 0 hT htwo (σ.restrictScalars R) _
end WeierstrassCurve
