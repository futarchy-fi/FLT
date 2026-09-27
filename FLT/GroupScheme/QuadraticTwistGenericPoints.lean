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

/-- Restricting the generic-fibre comparison gives evaluation at the chosen coefficients. -/
theorem genericPointsMulEquiv_restrict (f : K ⊗[R] H →ₐ[K] Ω) :
    let := hopfAlgebra (H := H) u r hr
    Bialgebra.restrictPoints R K Ω D (genericPointsMulEquiv u r hr f) =
      pointMap u ι s (Bialgebra.restrictPoints R K Ω H f) := by
  let := hopfAlgebra (H := H) u r hr
  change Bialgebra.restrictPoints R K Ω D
    ((Bialgebra.restrictPoints R K Ω D).symm
      (pointsEquiv u ι (HopfAlgebra.antipode_involutive R H) r hr
        (Bialgebra.restrictPoints R K Ω H f))) = _
  rw [Equiv.apply_symm_apply, pointsEquiv_apply]

omit [Coalgebra.IsCocomm R H] in
/-- Restriction of generic points commutes with automorphisms of the target field. -/
theorem restrictPoints_postcomp (f : K ⊗[R] H →ₐ[K] Ω) (σ : Ω →ₐ[K] Ω) :
    Bialgebra.restrictPoints R K Ω H (σ.comp f) =
      (σ.restrictScalars R).comp (Bialgebra.restrictPoints R K Ω H f) := rfl

/-- Generic-fibre comparison intertwines automorphisms fixing the quadratic coefficients. -/
theorem genericPointsMulEquiv_fixed (f : K ⊗[R] H →ₐ[K] Ω) (σ : Ω →ₐ[K] Ω)
    (hσ : (σ.restrictScalars R).comp s = s) :
    let := hopfAlgebra (H := H) u r hr
    genericPointsMulEquiv u r hr (σ.comp f) = σ.comp (genericPointsMulEquiv u r hr f) := by
  let := hopfAlgebra (H := H) u r hr
  apply (Bialgebra.restrictPoints R K Ω D).injective
  rw [genericPointsMulEquiv_restrict, restrictPoints_postcomp,
    restrictPoints_postcomp, genericPointsMulEquiv_restrict]
  exact (pointMap_postcomp_of_fixed u ι s _ (σ.restrictScalars R) hσ).symm

/-- Conjugating coefficients intertwines generic points after the original antipode. -/
theorem genericPointsMulEquiv_conjugated (f : K ⊗[R] H →ₐ[K] Ω) (σ : Ω →ₐ[K] Ω)
    (hσ : (σ.restrictScalars R).comp s = (s).comp (conjugation (u : R)).toAlgHom) :
    let := hopfAlgebra (H := H) u r hr
    genericPointsMulEquiv u r hr
      ((σ.comp f).comp (Algebra.TensorProduct.map (AlgHom.id K K) (ι).toAlgHom)) =
        σ.comp (genericPointsMulEquiv u r hr f) := by
  let := hopfAlgebra (H := H) u r hr
  apply (Bialgebra.restrictPoints R K Ω D).injective
  rw [genericPointsMulEquiv_restrict, restrictPoints_postcomp,
    genericPointsMulEquiv_restrict]
  have he : Bialgebra.restrictPoints R K Ω H
      ((σ.comp f).comp (Algebra.TensorProduct.map (AlgHom.id K K) (ι).toAlgHom)) =
      ((σ.restrictScalars R).comp (Bialgebra.restrictPoints R K Ω H f)).comp (ι).toAlgHom := by
    ext a
    rfl
  rw [he]
  exact (pointMap_postcomp_of_conjugation u ι (HopfAlgebra.antipode_involutive R H)
    s (Bialgebra.restrictPoints R K Ω H f) (σ.restrictScalars R) hσ).symm

end QuadraticTwist
