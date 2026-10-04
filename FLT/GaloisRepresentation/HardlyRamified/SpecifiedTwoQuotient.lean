/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.BaseChangeUniverses

/-!
# A specified local quotient at two

The quotient representation is a parameter, so it cannot vary independently
from one deformation to another. This retains the datum required by KW II
§3.3.4. No existence of an integral lift of the residual character is asserted.
-/

@[expose] public noncomputable section
open scoped TensorProduct
open TensorProduct
namespace GaloisRepresentation

variable {R A V W : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Free R W]

/-- The local action at two has the specified rank-one quotient representation. -/
def HasSpecifiedQuotientAtTwo (ρ : GaloisRep ℚ R V) (δ : GaloisRep ℚ_[2] R R) : Prop :=
  ∃ π : V →ₗ[R] R, Function.Surjective π ∧
    ∀ g x, π (ρ.map (algebraMap ℚ ℚ_[2]) g x) = δ g (π x)

omit [IsTopologicalRing R] [Module.Finite R V] [Module.Free R V]
  [Module.Finite R W] [Module.Free R W] in
/-- A coordinate change preserves the same specified quotient. -/
theorem HasSpecifiedQuotientAtTwo.conj {ρ : GaloisRep ℚ R V}
    {δ : GaloisRep ℚ_[2] R R} (h : HasSpecifiedQuotientAtTwo ρ δ) (e : V ≃ₗ[R] W) :
    HasSpecifiedQuotientAtTwo (ρ.conj e) δ := by
  obtain ⟨π, hs, he⟩ := h
  refine ⟨π.comp e.symm.toLinearMap, hs.comp e.symm.surjective, ?_⟩
  intro g x
  simpa [GaloisRep.conj_apply_apply] using he g (e.symm x)

variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Algebra R A] [ContinuousSMul R A]

/-- The specified rank-one representation after coefficient extension. -/
def specifiedQuotientBaseChange (δ : GaloisRep ℚ_[2] R R) : GaloisRep ℚ_[2] A A :=
  (δ.baseChange A).conj (AlgebraTensorModule.rid R A A)

omit [IsTopologicalRing R] in
/-- Coefficient extension transports the fixed quotient along the same ring map. -/
theorem HasSpecifiedQuotientAtTwo.baseChange {ρ : GaloisRep ℚ R V}
    {δ : GaloisRep ℚ_[2] R R} (h : HasSpecifiedQuotientAtTwo ρ δ) :
    HasSpecifiedQuotientAtTwo (ρ.baseChange A) (specifiedQuotientBaseChange δ) := by
  obtain ⟨π, hs, he⟩ := h
  let e : A ⊗[R] R ≃ₗ[A] A := AlgebraTensorModule.rid R A A
  refine ⟨e.toLinearMap.comp (π.baseChange A),
    e.surjective.comp (π.baseChange_surjective A hs), ?_⟩
  intro g x
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    have hv := he g v
    have hd : δ g (π v) = π v • δ g 1 := by
      simpa using (δ g).map_smul (π v) (1 : R)
    simp only [GaloisRep.baseChange_map, GaloisRep.baseChange_tmul,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
      e, AlgebraTensorModule.rid_tmul, specifiedQuotientBaseChange,
      GaloisRep.conj_apply_apply, AlgebraTensorModule.rid_symm_apply]
    rw [hv, hd]
    simp [smul_smul, mul_comm]
  | add x y hx hy => simp_all

end GaloisRepresentation
