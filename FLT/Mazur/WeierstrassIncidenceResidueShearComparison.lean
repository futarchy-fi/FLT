/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceCoefficientTransport
public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.WeierstrassModificationXResidueNamedGenerators

/-!
# Root-zero shearing agrees with the full original incidence residue equation

The comparison is proved on both original tensor generators. It preserves the
entire incidence fiber and its conic, including all marked origins.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (D : SplitNodeDepth W π depth) (hk0 : 0 < k) (hk : 2 * k ≤ depth)
  (d : Data W π k)
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R d.b6
variable (hs : algebraMap R (ResidueField R) (π ^ k) = 0)
  (h3 : algebraMap R (ResidueField R) d.b3 = 0)
  (h4 : algebraMap R (ResidueField R) d.b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "E" => residueFiberEquiv D k hk0 hk d.b3 d.b4 d.b6 d.factor3 d.factor4
local notation "F" => tensorShearNormalEquiv W (π ^ k) d.b3 d.b4 d.b6 K 0 hs h3 h4 hr
local notation "H" => fiberCoefficientTransport c (Eq.symm (rootShearZero_tangent V))

/-- Root-zero shearing agrees on every function of the full tensor incidence equation. -/
theorem residueFiberEquiv_eq_shear : (E).trans H = F := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext_ring
  apply hom_ext
  · change H (E ((1 : K) ⊗ₜ[R] t W (π ^ k) d.b3 d.b4 d.b6)) =
      F ((1 : K) ⊗ₜ[R] t W (π ^ k) d.b3 d.b4 d.b6)
    rw [residueFiberEquiv_t, tensorShearNormalEquiv_t]
    exact fiberCoefficientTransport_t c _
  · change H (E ((1 : K) ⊗ₜ[R] v W (π ^ k) d.b3 d.b4 d.b6)) =
      F ((1 : K) ⊗ₜ[R] v W (π ^ k) d.b3 d.b4 d.b6)
    rw [residueFiberEquiv_v, tensorShearNormalEquiv_v, map_zero, add_zero]
    exact fiberCoefficientTransport_v c _

end FLT.Mazur.WeierstrassModificationX
