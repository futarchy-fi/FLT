/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudModelUpperBound
public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# Extending a scalar action from the generic fibre

Transport the actual scalar maps through a generic identification. Whenever
all endomorphisms extend, their integral lifts satisfy the scalar action laws
by generic faithfulness, including addition represented by convolution.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Semiring F]
  {X M : FF R K} [Module F X.Points]
  [SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points]

/-- Transport an actual scalar endomorphism through a specified generic bijection. -/
def GenericGaloisHom.transportScalar (f : GenericGaloisHom X M)
    (hf : Function.Bijective f) (a : F) : GenericGaloisHom M M where
  toFun x := f (a • f.inverse hf x)
  map_zero' := by simp
  map_add' x y := by simp [smul_add]
  map_smul' σ x := by simp only [map_smul, smul_comm a σ, MonoidHom.id_apply]

omit [PerfectField K] [IsFractionRing R K] in
/-- Transport retains the prescribed action on the original points. -/
@[simp] theorem GenericGaloisHom.transportScalar_apply (f : GenericGaloisHom X M)
    (hf : Function.Bijective f) (a : F) (x : X.Points) :
    f.transportScalar hf a (f x) = f (a • x) := by
  change f (a • f.inverse hf (f x)) = _
  rw [GenericGaloisHom.inverse_apply]

/-- The lifts of the actual generic scalars obey all integral action laws. -/
theorem exists_integral_scalar_action (f : GenericGaloisHom X M) (hf : Function.Bijective f)
    (hext : ∀ g : GenericGaloisHom M M, ∃ h : ModelHom M M, genericHom h = g) :
    ∃ lift : F → ModelHom M M,
      (∀ a x, genericHom (lift a) (f x) = f (a • x)) ∧
      lift 0 = ModelHom.zero M M ∧ lift 1 = BialgHom.id R M.CoordinateRing ∧
      (∀ a b, lift (a + b) = (lift a).add (lift b)) ∧
      (∀ a b, lift (a * b) = (lift b).comp (lift a)) := by
  choose lift hlift using fun a : F ↦ hext (f.transportScalar hf a)
  have h (a : F) (x : X.Points) : genericHom (lift a) (f x) = f (a • x) := by
    rw [hlift, GenericGaloisHom.transportScalar_apply]
  refine ⟨lift, h, ?_, ?_, ?_, ?_⟩
  · apply genericHom_injective
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [h, zero_smul, map_zero, ModelHom.genericHom_zero]
  · apply genericHom_injective
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [h, one_smul, genericHom_id]
  · intro a b
    apply genericHom_injective
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [ModelHom.genericHom_add, h, h, h, add_smul, map_add]
  · intro a b
    apply genericHom_injective
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [genericHom_comp, h, h, h, mul_smul]

end ThreeAdicPlan
