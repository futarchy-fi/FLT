/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConvolutionBaseChange
public import FLT.GroupScheme.RaynaudEtaleExtension
public import FLT.GroupScheme.RaynaudModelArithmetic

/-!
# Extension into models with étale convolution dual

Generic coalgebra maps preserve integral lattices when the source convolution
dual is étale. Apply integral closedness to the transpose map and then recover
the original map from its coefficients in an integral basis.

For finite flat group schemes this proves extension into targets with étale
Cartier-dual coordinate algebra. Unlike the group-like spanning argument,
this does not require that the target split over the base ring.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace CoalgHom

variable {R K C D : Type*} [CommRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Coalgebra.IsCocomm R C]
  [Module.Free R C] [Module.Finite R C]
  [AddCommGroup D] [Module R D] [Coalgebra R D]
  [Module.Free R D] [Module.Finite R D]
  [Algebra.Etale R (WithConv (C →ₗ[R] R))]

/-- Transposing into an étale convolution dual makes every functional value integral. -/
theorem exists_algebraMap_eq_of_etale_convolutionDual
    (f : K ⊗[R] C →ₗc[K] K ⊗[R] D) (c : C) (φ : D →ₗ[R] R) :
    ∃ r : R, algebraMap R K r = Coalgebra.extendFunctional φ (f (1 ⊗ₜ[R] c)) := by
  let : Module.Finite R (WithConv (D →ₗ[R] R)) :=
    Module.Finite.equiv (WithConv.linearEquiv R (D →ₗ[R] R)).symm
  let e := Coalgebra.convolutionBaseChangeEquiv (R := R) (K := K) (C := C)
  let g : WithConv (D →ₗ[R] R) →ₐ[R] K ⊗[R] WithConv (C →ₗ[R] R) :=
    (e.symm.toAlgHom.restrictScalars R).comp
      ((f.convolutionDual.restrictScalars R).comp Coalgebra.extendConvolution)
  have hi : IsIntegral R (g (toConv φ)) :=
    (Algebra.IsIntegral.isIntegral (toConv φ)).map g
  obtain ⟨d, hd⟩ := Algebra.TensorProduct.exists_includeRight_eq_of_isIntegral
    (g (toConv φ)) hi
  have he : e (1 ⊗ₜ[R] d) =
      f.convolutionDual (Coalgebra.extendConvolution (K := K) (toConv φ)) := by
    rw [hd]
    exact e.apply_symm_apply _
  have hv := congrArg (fun q : WithConv (K ⊗[R] C →ₗ[K] K) ↦ q.ofConv (1 ⊗ₜ[R] c)) he
  simp only [e, Coalgebra.convolutionBaseChangeEquiv_apply,
    Coalgebra.convolutionBaseChange_tmul, one_smul] at hv
  change Coalgebra.extendFunctional d.ofConv (1 ⊗ₜ[R] c) =
    Coalgebra.extendFunctional φ (f (1 ⊗ₜ[R] c)) at hv
  rw [Coalgebra.extendFunctional_tmul, mul_one] at hv
  exact ⟨d c, hv⟩

/-- A generic coalgebra map preserves integral coordinates when the convolution dual
of its source coalgebra is étale. -/
theorem exists_tmul_eq_of_etale_convolutionDual
    (f : K ⊗[R] C →ₗc[K] K ⊗[R] D) (c : C) :
    ∃ d : D, (1 : K) ⊗ₜ[R] d = f (1 ⊗ₜ[R] c) := by
  classical
  let b := Module.Free.chooseBasis R D
  have hi (i : Module.Free.ChooseBasisIndex R D) :
      ∃ r : R, algebraMap R K r = (b.baseChange K).repr (f (1 ⊗ₜ[R] c)) i := by
    simpa only [Coalgebra.extendFunctional_coord, Module.Basis.coord_apply] using
      f.exists_algebraMap_eq_of_etale_convolutionDual c (b.coord i)
  choose r hr using hi
  refine ⟨∑ i, r i • b i, ?_⟩
  apply (b.baseChange K).repr.injective
  ext i
  simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Module.Basis.baseChange_repr_tmul, hr, Algebra.smul_def, Finsupp.single_apply]

end CoalgHom

namespace ThreeAdicPlan

/-- An étale convolution dual of the target makes all generic coordinates integral. -/
theorem GenericGaloisHom.integral_of_etale_convolutionDual
    {X Y : FF ℤ_[3] ℚ_[3]}
    [Algebra.Etale ℤ_[3] (WithConv (Y.CoordinateRing →ₗ[ℤ_[3]] ℤ_[3]))]
    (f : GenericGaloisHom X Y) (y : Y.CoordinateRing) :
    ∃ x : X.CoordinateRing, f.toBialgHom (1 ⊗ₜ[ℤ_[3]] y) = 1 ⊗ₜ[ℤ_[3]] x := by
  let : Module.Free ℤ_[3] X.CoordinateRing := Module.free_of_flat_of_isLocalRing
  let : Module.Free ℤ_[3] Y.CoordinateRing := Module.free_of_flat_of_isLocalRing
  obtain ⟨x, hx⟩ := f.toBialgHom.toCoalgHom.exists_tmul_eq_of_etale_convolutionDual y
  exact ⟨x, hx.symm⟩

/-- The graph projection is surjective for every target with étale convolution dual. -/
theorem GenericGaloisHom.graphFst_surjective_of_etale_convolutionDual
    {X Y : FF ℤ_[3] ℚ_[3]}
    [Algebra.Etale ℤ_[3] (WithConv (Y.CoordinateRing →ₗ[ℤ_[3]] ℤ_[3]))]
    (f : GenericGaloisHom X Y) : Function.Surjective f.graphFst :=
  f.graphFst_surjective_of_integral f.integral_of_etale_convolutionDual

/-- Every generic morphism into a target with étale convolution dual extends uniquely.
Neither the source nor the target needs an order or exponent bound. -/
theorem raynaud_extend_generic_morphism_of_etale_convolutionDual
    (X Y : FF ℤ_[3] ℚ_[3])
    [Algebra.Etale ℤ_[3] (WithConv (Y.CoordinateRing →ₗ[ℤ_[3]] ℤ_[3]))]
    (f : GenericGaloisHom X Y) : ∃! fO : ModelHom X Y, genericHom fO = f :=
  raynaud_extend_generic_morphism_of_graphFst_surjective X Y f
    f.graphFst_surjective_of_etale_convolutionDual

end ThreeAdicPlan
