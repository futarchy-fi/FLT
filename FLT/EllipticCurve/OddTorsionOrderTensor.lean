/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.OddTorsionOrderPoints
public import FLT.GroupScheme.EtaleOrder

/-!
# Generic fibres and tensor evaluation of the odd-torsion coordinate order

The coordinate order is reduced because it is an algebra of functions into a
field. Localization and perfection imply that its generic fibre is finite étale.
These facts do not require an integral addition law.
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

/-- The odd-torsion coordinate order has finite étale generic fibre over a
perfect fraction field. This does not assume good reduction or coaddition. -/
theorem etale_oddTorsionCoordinateOrder_genericFiber
    [IsDedekindDomain R] [Module.IsTorsionFree R k]
    (K : Type u) [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K] :
    Algebra.Etale K (K ⊗[R] W.oddTorsionCoordinateOrder hn ξ η hT htwo) := by
  let H := W.oddTorsionCoordinateOrder hn ξ η hT htwo
  have hflat := W.finiteFlat_oddTorsionCoordinateOrder hn ξ η hT htwo
  let : Module.Finite R H := hflat.toFinite
  let : IsReduced H := isReduced_of_injective H.val Subtype.val_injective
  exact Algebra.etale_genericFiber_of_finite_reduced R K H

/-- Evaluate the tensor square on ordered pairs of geometric torsion points. -/
noncomputable def oddTorsionTensorEvaluation :
    (W.oddTorsionCoordinateOrder hn ξ η hT htwo ⊗[R]
      W.oddTorsionCoordinateOrder hn ξ η hT htwo) →ₐ[R]
        ((W.oddTorsionPointSet (k := k) n × W.oddTorsionPointSet (k := k) n) → k) :=
  Algebra.TensorProduct.lift
    (AlgHom.pi fun P => W.oddTorsionEvaluationPoint hn ξ η hT htwo P.1)
    (AlgHom.pi fun P => W.oddTorsionEvaluationPoint hn ξ η hT htwo P.2)
    (fun _ _ => Commute.all _ _)

/-- Tensor evaluation multiplies the evaluations of its two factors. -/
@[simp] theorem oddTorsionTensorEvaluation_tmul
    (f g : W.oddTorsionCoordinateOrder hn ξ η hT htwo)
    (P Q : W.oddTorsionPointSet (k := k) n) :
    W.oddTorsionTensorEvaluation hn ξ η hT htwo (f ⊗ₜ[R] g) (P, Q) =
      f.val P * g.val Q := by
  simp [oddTorsionTensorEvaluation, oddTorsionEvaluationPoint]

/-- Every geometric point of the tensor square is evaluation at a pair of torsion points. -/
theorem oddTorsionTensorEvaluation_points
    [(W.map (algebraMap R k)).IsElliptic]
    (f : (W.oddTorsionCoordinateOrder hn ξ η hT htwo ⊗[R]
      W.oddTorsionCoordinateOrder hn ξ η hT htwo) →ₐ[R] k) :
    ∃ P Q : W.oddTorsionPointSet (k := k) n,
      f = (Pi.evalAlgHom R _ (P, Q)).comp
        (W.oddTorsionTensorEvaluation hn ξ η hT htwo) := by
  obtain ⟨P, hP⟩ := W.oddTorsionEvaluationPoint_surjective hn ξ η hT htwo
    (f.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨Q, hQ⟩ := W.oddTorsionEvaluationPoint_surjective hn ξ η hT htwo
    (f.comp Algebra.TensorProduct.includeRight)
  refine ⟨P, Q, ?_⟩
  apply Algebra.TensorProduct.ext
  · ext a
    exact (DFunLike.congr_fun hP a).symm.trans (by
      simp [oddTorsionTensorEvaluation, oddTorsionEvaluationPoint])
  · ext a
    exact (DFunLike.congr_fun hQ a).symm.trans (by
      simp [oddTorsionTensorEvaluation, oddTorsionEvaluationPoint])

/-- The tensor square embeds in the functions on pairs of geometric torsion
points. Flatness controls the integral fibre, and étaleness separates generic points. -/
theorem oddTorsionTensorEvaluation_injective
    [IsDedekindDomain R] [Module.IsTorsionFree R k]
    [(W.map (algebraMap R k)).IsElliptic]
    (K : Type u) [Field K] [PerfectField K] [Algebra R K] [IsFractionRing R K]
    [Algebra K k] [IsScalarTower R K k] [IsGalois K k] [IsSepClosed k] :
    Function.Injective (W.oddTorsionTensorEvaluation hn ξ η hT htwo) := by
  let H := W.oddTorsionCoordinateOrder hn ξ η hT htwo
  have hf := W.finiteFlat_oddTorsionCoordinateOrder hn ξ η hT htwo
  let : Module.Flat R H := hf.toFlat
  let : Algebra.Etale K (K ⊗[R] H) :=
    W.etale_oddTorsionCoordinateOrder_genericFiber hn ξ η hT htwo K
  let : Algebra.Etale K (K ⊗[R] (H ⊗[R] H)) :=
    Algebra.etale_genericFiber_tensorSquare R K H
  intro x y hxy
  apply Algebra.eq_of_generic_points_eq R K k (H ⊗[R] H)
  intro f
  obtain ⟨P, Q, rfl⟩ := W.oddTorsionTensorEvaluation_points hn ξ η hT htwo f
  exact congrFun hxy (P, Q)

end WeierstrassCurve
