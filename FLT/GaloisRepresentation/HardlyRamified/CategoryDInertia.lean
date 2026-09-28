/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import FLT.GaloisRepresentation.HardlyRamified.TameInertiaCyclic

/-!
# Inertia bounds for category-D objects

The full action on a finite abelian point group is an integral Galois
representation. This connects category D to the existing tame-inertia
theorem without selecting a constituent of the point action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

namespace FiniteContinuousGaloisModule

/-- The full point action as integral linear endomorphisms. -/
def integralAction (W : FiniteContinuousGaloisModule) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ W where
  toFun σ := AddMonoidHom.toIntLinearMap
    { toFun := fun w ↦ σ • w
      map_zero' := smul_zero σ
      map_add' := smul_add σ }
  map_one' := by ext w; exact one_smul _ w
  map_mul' σ τ := by ext w; exact mul_smul σ τ w

/-- The integral action has open fibers, since there are only finitely many points. -/
theorem integralAction_isLocallyConstant (W : FiniteContinuousGaloisModule) :
    IsLocallyConstant W.integralAction := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro f
  have he : W.integralAction ⁻¹' {f} =
      ⋂ w : W, {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ • w = f w} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact LinearMap.ext_iff
  rw [he]
  exact isOpen_iInter_of_finite fun w ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ w (f w)

/-- The continuous integral representation of the full point group. -/
def integralGaloisRep (W : FiniteContinuousGaloisModule) : GaloisRep ℚ ℤ W :=
  letI := moduleTopology ℤ (Module.End ℤ W)
  { W.integralAction with continuous_toFun := W.integralAction_isLocallyConstant.continuous }

/-- Evaluating the integral representation is the given action on points. -/
@[simp] theorem integralGaloisRep_apply (W : FiniteContinuousGaloisModule)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : W) :
    W.integralGaloisRep σ w = σ • w := rfl

/-- The integral representation cuts out exactly the full point field. -/
theorem integralGaloisRep_ker (W : FiniteContinuousGaloisModule) :
    W.integralGaloisRep.ker = W.pointActionKernel := by
  ext σ
  rw [mem_pointActionKernel]
  change W.integralGaloisRep σ = 1 ↔ _
  exact LinearMap.ext_iff

end FiniteContinuousGaloisModule

/-- The pointwise category-D condition is square-zero unipotence of the integral action. -/
theorem InCategoryD.inertiaTwo_sq_zero {H : FiniteFlatObject ZInvTwo} (hD : InCategoryD H)
    (σ : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ))
    (hσ : σ ∈ localInertiaGroup twoAdicPlace) :
    (H.points.integralGaloisRep.map (algebraMap ℚ (twoAdicPlace.adicCompletion ℚ)) σ - 1) ^ 2 =
      0 := by
  ext w
  exact hD.inertiaSquareZero σ hσ w

/-- For a category-D object killed by three, the full inertia image at two has order
dividing three. Here `e_two` is the image-order definition from `ResidualTameTwo`. -/
theorem InCategoryD.inertiaTwo_order_dvd_three {H : FiniteFlatObject ZInvTwo} (hD : InCategoryD H)
    (hk : KilledBy 3 H) : e_two H.points.integralGaloisRep ∣ 3 :=
  ramification_two_dvd_three H.points.integralGaloisRep hk hD.inertiaTwo_sq_zero

end ThreeAdicPlan
