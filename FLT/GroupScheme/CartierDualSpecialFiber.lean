/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualKernelInclusion
public import FLT.GroupScheme.HopfSpecialFiberFreeness

/-!
# Special fibres of Cartier transposes

A surjection onto a projective coordinate module splits linearly. Its Cartier
transpose is therefore a split linear inclusion, even after nonflat base change.
Hopf-subalgebra freeness applies to every residue fibre of a dual extension.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.CartierDual

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- The transpose of a surjective Hopf map admits a linear retraction. -/
theorem bialgMap_exists_retraction (f : A →ₐc[R] B) (hf : Function.Surjective f) :
    ∃ g : CartierDual R A →ₗ[R] CartierDual R B,
      g.comp (bialgMap f).toLinearMap = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.toLinearMap
    (LinearMap.id : B →ₗ[R] B) hf
  refine ⟨linearEquiv.symm.toLinearMap.comp (s.dualMap.comp linearEquiv.toLinearMap), ?_⟩
  ext φ b
  change φ (f (s b)) = φ b
  exact congrArg φ (LinearMap.congr_fun hs b)

/-- Arbitrary tensoring preserves injectivity of the transpose of a surjection. -/
theorem bialgMap_lTensor_injective (f : A →ₐc[R] B) (hf : Function.Surjective f)
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective ((bialgMap f).toLinearMap.lTensor M) := by
  obtain ⟨g, hg⟩ := bialgMap_exists_retraction f hf
  apply Function.LeftInverse.injective (g := g.lTensor M)
  intro x
  change (g.lTensor M).comp ((bialgMap f).toLinearMap.lTensor M) x = x
  rw [← LinearMap.lTensor_comp, hg, LinearMap.lTensor_id]
  rfl

end HopfAlgebra.CartierDual

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]
  {A H Q : FiniteFlatObject R}

/-- A dual extension's quotient coordinates remain injective on every base change. -/
theorem FiniteFlatExtension.dualInclusion_baseChange_injective
    (E : FiniteFlatExtension A H Q) (S : Type) [CommRing S] [Algebra R S] :
    Function.Injective
      (Bialgebra.TensorProduct.map (BialgHom.id S S) E.inclusion.cartierDual) :=
  HopfAlgebra.CartierDual.bialgMap_lTensor_injective E.inclusion E.inclusion_surjective S

/-- Every residue fibre of the transposed inclusion is a free relative module. -/
theorem FiniteFlatExtension.dualInclusion_free_quotientFiber
    (E : FiniteFlatExtension A H Q) (I : Ideal R) [I.IsMaximal] :
    letI := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
    Module.Free
      (A.cartierDual.model.CoordinateRing ⧸
        I.map (algebraMap R A.cartierDual.model.CoordinateRing))
      ((A.cartierDual.model.CoordinateRing ⧸
        I.map (algebraMap R A.cartierDual.model.CoordinateRing))
        ⊗[A.cartierDual.model.CoordinateRing] H.cartierDual.model.CoordinateRing) := by
  let := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A.cartierDual.model.CoordinateRing
      H.cartierDual.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.inclusion.cartierDual.toAlgHom.comp_algebraMap.symm
  exact HopfAlgebra.free_quotientFiber_of_injective_baseChange E.inclusion.cartierDual
    rfl I (E.dualInclusion_baseChange_injective (R ⧸ I))

end ThreeAdicPlan
