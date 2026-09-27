/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerPoints
public import FLT.GroupScheme.QuadraticTwistPoints

/-!
# Generic-fibre groups of quadratic twists

Restriction to integral coordinates upgrades the point comparison to an
isomorphism for the generic-fibre convolution groups.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

open scoped TensorProduct

namespace QuadraticTwist

universe v
variable {R H K Ω : Type v} [CommRing R] [CommRing H] [Field K] [Field Ω]
variable [HopfAlgebra R H] [Coalgebra.IsCocomm R H]
variable [Algebra R K] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
variable (u : Rˣ) (r : R) (hr : 2 * r = 1)
variable [Algebra (QuadraticAlgebra R (u : R) 0) Ω]
variable [IsScalarTower R (QuadraticAlgebra R (u : R) 0) Ω]

local notation "ι" => HopfAlgebra.antipodeAlgEquiv R H
local notation "D" => model (u : R) ι
local notation "s" => IsScalarTower.toAlgHom R (QuadraticAlgebra R (u : R) 0) Ω

/-- After choosing quadratic coefficients, generic-fibre points are isomorphic as groups. -/
noncomputable def genericPointsMulEquiv :
    letI := hopfAlgebra (H := H) u r hr
    (K ⊗[R] H →ₐ[K] Ω) ≃* (K ⊗[R] D →ₐ[K] Ω) := by
  letI := hopfAlgebra (H := H) u r hr
  let e : (K ⊗[R] H →ₐ[K] Ω) ≃ (K ⊗[R] D →ₐ[K] Ω) :=
    (Bialgebra.restrictPoints R K Ω H).trans
      ((pointsEquiv u ι (HopfAlgebra.antipode_involutive R H) r hr).trans
        (Bialgebra.restrictPoints R K Ω D).symm)
  have he (f : K ⊗[R] H →ₐ[K] Ω) :
      Bialgebra.restrictPoints R K Ω D (e f) =
        pointMap u ι s (Bialgebra.restrictPoints R K Ω H f) := by
    simpa only [e, Equiv.trans_apply, Equiv.apply_symm_apply] using
      pointsEquiv_apply (Ω := Ω) u ι (HopfAlgebra.antipode_involutive R H) r hr
      (Bialgebra.restrictPoints R K Ω H f)
  refine { toEquiv := e, map_mul' := ?_ }
  intro f g
  change e (f * g) = e f * e g
  apply (Bialgebra.restrictPoints R K Ω D).injective
  rw [he, Bialgebra.restrictPoints_mul R K Ω D, he, he,
    Bialgebra.restrictPoints_mul R K Ω H]
  exact (pointMap_convolution u r hr s _ _).symm

end QuadraticTwist
