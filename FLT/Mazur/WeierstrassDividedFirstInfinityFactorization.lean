/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalInfinityIntersection
public import FLT.Mazur.PrincipalOpenIntersectionModels

/-!
# The full first retained infinity intersection factors through the initial chart

The original vertical function contains the entire horizontal factor. Its full
principal boundary therefore maps through the original common initial boundary.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, Nat.lt_succ_of_le h1⟩
local notation "u₀" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (e).b3 (e).b4 (e).b6 2
local notation "v₀" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (e).b3 (e).b4 (e).b6 1
local notation "x" => WeierstrassDilatation.x W (π ^ start) (d).b3 (d).b4 (d).b6
local notation "t" => WeierstrassModificationX.t W (π ^ start) (d).b3 (d).b4 (d).b6
local notation "y" => successiveOriginalY e
local notation "A" => PrincipalOpenTensor.transitionIso S x t
  (WeierstrassModificationX.overlapEquiv W (π ^ start) (d).b3 (d).b4 (d).b6)
local notation "B" => PrincipalOpenTensor.transitionIso S x u₀ (previousBoundaryEquiv hπ d e)

omit [IsDomain R] [IsBezout R] in
/-- The entire original vertical tensor open is contained in the horizontal tensor open. -/
theorem firstInfinityTensor_le_horizontal :
    PrimeSpectrum.basicOpen ((1 : S) ⊗ₜ[R] y) ≤
      PrimeSpectrum.basicOpen ((1 : S) ⊗ₜ[R] u₀) := by
  have H : (1 : S) ⊗ₜ[R] y =
      ((1 : S) ⊗ₜ[R] algebraMap R _ (π ^ start)) *
        (((1 : S) ⊗ₜ[R] u₀) * ((1 : S) ⊗ₜ[R] v₀)) := by
    simp only [successiveOriginalY, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [H]
  exact (PrimeSpectrum.basicOpen_mul_le_right _ _).trans
    (PrimeSpectrum.basicOpen_mul_le_left _ _)
local notation "h" => firstInfinityTensor_le_horizontal data S h1
local notation "k" => PrincipalLocalizationSquare.openInclusion h
local notation "initial" => globalInitialTensorChart hπ data S (1 + m) hm
local notation "retained" => olderGlobalTensorChart hπ data S 0 h1 m hm

/-- Every point and function of the full first infinity boundary maps to the initial chart. -/
def firstInfinityTensorToInitial :
    Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] y))) ⟶
      Spec (.of (S ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
        (d).b3 (d).b4 (d).b6)) :=
  k ≫ (B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion S t

/-- The factorization preserves the entire original retained chart projection. -/
@[reassoc] theorem firstInfinityTensorToInitial_comp :
    firstInfinityTensorToInitial hπ data S h1 ≫ initial =
      PrincipalOpenTensor.inclusion S y ≫ retained := by
  have H := (initialRetainedGlobalTensor_isPullback hπ data S h1 m hm).w
  have H' := congrArg (fun f => k ≫ (B).hom ≫ f) H
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at H'
  change _ = k ≫ PrincipalOpenTensor.inclusion S u₀ ≫ retained at H'
  have hk : k ≫ PrincipalOpenTensor.inclusion S u₀ = PrincipalOpenTensor.inclusion S y :=
    PrincipalLocalizationSquare.openInclusion_fac h
  rw [← Category.assoc k (PrincipalOpenTensor.inclusion S u₀) retained, hk] at H'
  simpa only [firstInfinityTensorToInitial, Category.assoc] using H'

end FLT.Mazur.WeierstrassDividedDepth
