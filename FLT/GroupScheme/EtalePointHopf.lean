/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PointHopfLaws
public import FLT.GroupScheme.CoordinateOrder

/-!
# Hopf reconstruction from etale generic points

Flatness and generic etaleness discharge the point-separation requirements,
including separation on the tensor cube. The coordinate algebra need not
already be presented as a subalgebra of functions on a group.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace PointCoalgebra
universe u
variable {R K Ω H X : Type u} [CommRing R] [Field K] [Field Ω]
  [CommRing H] [Algebra R H] [Algebra R K] [Algebra R Ω] [Algebra K Ω]
  [IsScalarTower R K Ω] [IsFractionRing R K] [IsGalois K Ω] [IsSepClosed Ω]
  [AddGroup X] (e : X → H →ₐ[R] Ω) (he : Function.Surjective e)

omit [IsSepClosed Ω] [AddGroup X] in
include he in
/-- Every point of a tensor square is evaluation at a pair of original points. -/
theorem pair_surjective : Function.Surjective (fun pq : X × X ↦ pair e pq.1 pq.2) := by
  intro f
  obtain ⟨P, hp⟩ := he (f.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨Q, hq⟩ := he (f.comp Algebra.TensorProduct.includeRight)
  refine ⟨(P, Q), ?_⟩
  apply Algebra.TensorProduct.ext
  · ext a
    simpa [pair] using DFunLike.congr_fun hp a
  · ext a
    simpa [pair] using DFunLike.congr_fun hq a

omit [IsSepClosed Ω] [AddGroup X] in
include he in
/-- Every point of a tensor cube is evaluation at three original points. -/
theorem triple_surjective :
    Function.Surjective (fun pqr : X × X × X ↦ triple e pqr.1 pqr.2.1 pqr.2.2) := by
  intro f
  obtain ⟨P, hp⟩ := he (f.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨⟨Q, S⟩, hq⟩ := pair_surjective e he (f.comp Algebra.TensorProduct.includeRight)
  refine ⟨(P, Q, S), ?_⟩
  apply Algebra.TensorProduct.ext
  · ext a
    simpa [triple] using DFunLike.congr_fun hp a
  · apply AlgHom.ext
    intro a
    simpa [triple] using DFunLike.congr_fun hq a

variable [Module.Flat R H] [Algebra.Etale K (K ⊗[R] H)]
omit [AddGroup X] in
include K he in
/-- The prescribed complete set of generic points separates integral coordinates. -/
theorem points_separate {x y : H} (h : ∀ P, e P x = e P y) : x = y := by
  apply Algebra.eq_of_generic_points_eq R K Ω H
  intro f
  obtain ⟨P, rfl⟩ := he f
  exact h P

omit [AddGroup X] in
include K he in
/-- Generic points also separate the integral tensor cube. -/
theorem triple_separates {x y : H ⊗[R] (H ⊗[R] H)}
    (h : ∀ P Q S, triple e P Q S x = triple e P Q S y) : x = y := by
  let : Algebra.Etale K (K ⊗[R] (H ⊗[R] H)) := Algebra.etale_genericFiber_tensorSquare R K H
  let : Algebra.Etale K (K ⊗[R] (H ⊗[R] (H ⊗[R] H))) :=
    CoordinateOrder.etale_tensor (R := R) (K := K) H (H ⊗[R] H)
  apply Algebra.eq_of_generic_points_eq R K Ω (H ⊗[R] (H ⊗[R] H))
  intro f
  obtain ⟨⟨P, Q, S⟩, rfl⟩ := triple_surjective e he f
  exact h P Q S

/-- Integral operations with the specified generic point laws form a Hopf algebra. -/
@[instance_reducible]
def hopfOfEtalePoints (d : H →ₐ[R] H ⊗[R] H) (c : H →ₐ[R] R) (a : H →ₐ[R] H)
    (hd : ∀ f P Q, pair e P Q (d f) = e (P + Q) f)
    (hc : ∀ f, algebraMap R Ω (c f) = e 0 f)
    (ha : ∀ f P, e P (a f) = e (-P) f) : HopfAlgebra R H :=
  hopf e (points_separate (K := K) e he) (triple_separates (K := K) e he) d c a hd hc ha

end PointCoalgebra
