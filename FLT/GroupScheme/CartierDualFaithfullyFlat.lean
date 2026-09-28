/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualSpecialFiber
public import FLT.GroupScheme.PrincipalFiberFlatness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithful flatness of Cartier transposes

A finite Hopf inclusion over a principal ideal domain which remains injective
on closed fibres is relatively faithfully flat. In particular, the transpose
of the kernel coordinate map in a finite-flat extension is faithfully flat.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

variable {R B A : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing B] [CommRing A] [HopfAlgebra R B] [HopfAlgebra R A]
  [Algebra B A] [IsScalarTower R B A]
  [Module.Finite R B] [Module.Finite R A] [Module.IsTorsionFree R A]

/-- A finite Hopf inclusion which stays injective on closed fibres is relatively flat. -/
theorem flat_of_injective_residueBaseChange
    (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
    (hinj : Function.Injective f)
    (hfib : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective
      (Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) f)) :
    Module.Flat B A := by
  by_cases hR : IsField R
  · let := hR.toField
    let := free_of_injective_bialgHom f hf hinj
    infer_instance
  · exact Module.flat_of_free_quotientFibers hR
      (fun I _ ↦ free_quotientFiber_of_injective_baseChange f hf I (hfib I))

/-- A finite Hopf inclusion which stays injective on closed fibres is faithfully flat. -/
theorem faithfullyFlat_of_injective_residueBaseChange
    (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
    (hinj : Function.Injective f)
    (hfib : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective
      (Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) f)) :
    Module.FaithfullyFlat B A := by
  let := flat_of_injective_residueBaseChange f hf hinj hfib
  let : Module.Finite B A := Module.Finite.of_restrictScalars_finite R B A
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr (by
    have he : (f : B → A) = algebraMap B A := congrArg DFunLike.coe hf
    rwa [← he])
  exact Module.FaithfullyFlat.of_comap_surjective (Algebra.IsIntegral.comap_surjective B A)

end HopfAlgebra

namespace ThreeAdicPlan

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]
  {A H Q : FiniteFlatObject R}

/-- The quotient in the reversed Cartier-dual extension is integrally faithfully flat. -/
theorem FiniteFlatExtension.dualQuotientFaithfullyFlat (E : FiniteFlatExtension A H Q) :
    letI := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
    Module.FaithfullyFlat A.cartierDual.model.CoordinateRing
      H.cartierDual.model.CoordinateRing := by
  let := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A.cartierDual.model.CoordinateRing
      H.cartierDual.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.inclusion.cartierDual.toAlgHom.comp_algebraMap.symm
  exact HopfAlgebra.faithfullyFlat_of_injective_residueBaseChange E.inclusion.cartierDual
    rfl E.dualInclusion_injective (fun I _ ↦ E.dualInclusion_baseChange_injective (R ⧸ I))

end ThreeAdicPlan
