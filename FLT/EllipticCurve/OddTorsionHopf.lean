/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionCoaddition
public import FLT.GroupScheme.CoordinateOrder
/-!
# The Hopf structure on the integral odd-torsion coordinate order

Integral coaddition, the augmentation at zero, and integral negation give
an actual Hopf algebra. The construction retains the original coefficient
algebra structure on the order.
-/

@[expose] public section

open scoped TensorProduct
universe u
namespace WeierstrassCurve
variable {R k : Type u} [CommRing R] [Field k] [Algebra R k] [DecidableEq k]
    (W : WeierstrassCurve R) {n : ℕ} (hn : Odd n) (ξ η : R)
    (hT : (W.map (algebraMap R k)).toAffine.Nonsingular
      (algebraMap R k ξ) (algebraMap R k η))
    (htwo : 2 • Affine.Point.some _ _ hT = 0)
    [IsDedekindDomain R] [Module.IsTorsionFree R k]
    [(W.map (algebraMap R k)).IsElliptic]
    (K : Type u) [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K]
    [Algebra K k] [IsScalarTower R K k] [IsGalois K k] [IsSepClosed k]
/-- Upgrade integral coaddition to a Hopf structure on the torsion coordinate order. -/
@[instance_reducible]
noncomputable def oddTorsionHopfOfCoaddition
    (d : W.oddTorsionCoordinateOrder hn ξ η hT htwo →ₐ[R]
      (W.oddTorsionCoordinateOrder hn ξ η hT htwo ⊗[R]
        W.oddTorsionCoordinateOrder hn ξ η hT htwo))
    (hd : ∀ f P Q, W.oddTorsionTensorEvaluation hn ξ η hT htwo (d f) (P, Q) = f.val (P + Q)) :
    HopfAlgebra R (W.oddTorsionCoordinateOrder hn ξ η hT htwo) := by
  let H := W.oddTorsionCoordinateOrder hn ξ η hT htwo
  have hf := W.finiteFlat_oddTorsionCoordinateOrder hn ξ η hT htwo
  let : Module.Flat R H := hf.toFlat
  let : Algebra.Etale K (K ⊗[R] H) :=
    W.etale_oddTorsionCoordinateOrder_genericFiber hn ξ η hT htwo K
  have hi : Function.Injective (algebraMap R k) := by
    rw [IsScalarTower.algebraMap_eq R K k]
    exact (algebraMap K k).injective.comp (IsFractionRing.injective R K)
  let c := Classical.choose (W.exists_oddTorsionCoordinateCounit hn ξ η hT htwo hi)
  have hc := Classical.choose_spec (W.exists_oddTorsionCoordinateCounit hn ξ η hT htwo hi)
  let S := W.oddTorsionCoordinateNegation hn ξ η hT htwo
  have he : Function.Surjective (CoordinateOrder.evaluation H) :=
    W.oddTorsionEvaluationPoint_surjective hn ξ η hT htwo
  have hp : ∀ f P Q, CoordinateOrder.pair H P Q (d f) = f.val (P + Q) := by
    intro f P Q
    have hh (z : H ⊗[R] H) : CoordinateOrder.pair H P Q z =
        W.oddTorsionTensorEvaluation hn ξ η hT htwo z (P, Q) := by
      induction z using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add a b ha hb => simp [ha, hb]
    rw [hh, hd]
  exact CoordinateOrder.hopf (K := K) H he d c S hp hc (fun _ _ => rfl)

/-- The constructed Hopf structure has exactly the supplied integral coaddition. -/
theorem oddTorsionHopfOfCoaddition_comul
    (d : W.oddTorsionCoordinateOrder hn ξ η hT htwo →ₐ[R]
      (W.oddTorsionCoordinateOrder hn ξ η hT htwo ⊗[R]
        W.oddTorsionCoordinateOrder hn ξ η hT htwo))
    (hd : ∀ f P Q, W.oddTorsionTensorEvaluation hn ξ η hT htwo (d f) (P, Q) = f.val (P + Q)) :
    letI := W.oddTorsionHopfOfCoaddition hn ξ η hT htwo K d hd
    Bialgebra.comulAlgHom R (W.oddTorsionCoordinateOrder hn ξ η hT htwo) = d := rfl
end WeierstrassCurve
