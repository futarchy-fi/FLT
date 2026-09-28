/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualFaithfullyFlat
public import FLT.GroupScheme.CartierDualInvariants
public import FLT.GroupScheme.RaynaudFlatKernelExactness

/-!
# The augmentation quotient of a dual extension

The original quotient coordinates pair perfectly with the augmentation quotient
of the dual middle term. Relative flatness makes this quotient finite projective,
so double duality identifies it with the Cartier dual of the original quotient.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.FiniteFlatExtension

open HopfAlgebra.CartierDual

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]
  {A H Q : FiniteFlatObject R}

/-- The coordinate ring of the scheme-theoretic kernel of the dual quotient. -/
abbrev dualKernelRing (E : FiniteFlatExtension A H Q) :=
  H.cartierDual.model.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal E.inclusion.cartierDual

/-- The dual augmentation quotient is flat over the original integral base. -/
theorem dualKernelRing_flat (E : FiniteFlatExtension A H Q) :
    Module.Flat R E.dualKernelRing := by
  let := E.inclusion.cartierDual.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R A.cartierDual.model.CoordinateRing
      H.cartierDual.model.CoordinateRing := by
    apply IsScalarTower.of_algebraMap_eq'
    exact E.inclusion.cartierDual.toAlgHom.comp_algebraMap.symm
  let := E.dualQuotientFaithfullyFlat
  exact (Bialgebra.counitAlgHom R A.cartierDual.model.CoordinateRing).quotient_map_ker_flat

/-- The transposed quotient map kills the extended dual augmentation ideal. -/
theorem dualAugmentationIdeal_le_ker (E : FiniteFlatExtension A H Q) :
    HopfAlgebra.augmentationIdeal E.inclusion.cartierDual ≤
      RingHom.ker E.quotient.cartierDual.toAlgHom.toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro φ hφ
  change E.quotient.cartierDual (E.inclusion.cartierDual φ) = 0
  have he := AlgHom.congr_fun E.dualCompositionZero φ
  change E.quotient.cartierDual (E.inclusion.cartierDual φ) =
    algebraMap R Q.cartierDual.model.CoordinateRing
      (Bialgebra.counitAlgHom R A.cartierDual.model.CoordinateRing φ) at he
  change Bialgebra.counitAlgHom R A.cartierDual.model.CoordinateRing φ = 0 at hφ
  simpa only [hφ, map_zero] using he

/-- The transposed quotient factors through the scheme-theoretic dual kernel. -/
def dualKernelMap (E : FiniteFlatExtension A H Q) :
    E.dualKernelRing →ₐ[R] Q.cartierDual.model.CoordinateRing :=
  Ideal.Quotient.liftₐ _ E.quotient.cartierDual.toAlgHom E.dualAugmentationIdeal_le_ker

/-- The quotient pairing is induced by evaluation on original quotient coordinates. -/
def dualKernelPairing (E : FiniteFlatExtension A H Q) :
    Q.model.CoordinateRing →ₗ[R] Module.Dual R E.dualKernelRing :=
  E.dualKernelMap.toLinearMap.dualMap.comp
    ((linearEquiv (R := R) (A := Q.model.CoordinateRing)).toLinearMap.dualMap.comp
      (Module.Dual.eval R Q.model.CoordinateRing))

/-- Evaluation of the descended pairing on a representative. -/
@[simp] theorem dualKernelPairing_mk (E : FiniteFlatExtension A H Q)
    (q : Q.model.CoordinateRing) (φ : HopfAlgebra.CartierDual R H.model.CoordinateRing) :
    E.dualKernelPairing q
      (Ideal.Quotient.mk (HopfAlgebra.augmentationIdeal E.inclusion.cartierDual) φ) =
        φ (E.quotient q) := rfl

/-- The integral pairing with the dual augmentation quotient is perfect. -/
theorem dualKernelPairing_bijective (E : FiniteFlatExtension A H Q) :
    Function.Bijective E.dualKernelPairing := by
  let J := HopfAlgebra.augmentationIdeal E.inclusion.cartierDual
  let π := Ideal.Quotient.mkₐ R J
  constructor
  · intro q q' hq
    apply E.quotient_injective
    apply (Module.evalEquiv R H.model.CoordinateRing).injective
    ext φ
    exact congrArg (fun l : Module.Dual R E.dualKernelRing ↦ l (π (WithConv.toConv φ))) hq
  · intro l
    let lH : Module.Dual R (HopfAlgebra.CartierDual R H.model.CoordinateRing) :=
      l.comp π.toLinearMap
    obtain ⟨h, hh⟩ := (bidualLinearEquiv (R := R) (A := H.model.CoordinateRing)).surjective
      (WithConv.toConv lH)
    have heval (φ : HopfAlgebra.CartierDual R H.model.CoordinateRing) : φ h = l (π φ) :=
      congrArg (fun k : HopfAlgebra.CartierDual R
        (HopfAlgebra.CartierDual R H.model.CoordinateRing) ↦ k φ) hh
    obtain ⟨q, hq⟩ := E.exists_quotient_preimage_of_annihilates h (fun φ hφ ↦ by
      rw [heval]
      have hz : π (show H.cartierDual.model.CoordinateRing from φ) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr hφ
      rw [hz, map_zero])
    refine ⟨q, ?_⟩
    apply LinearMap.ext
    intro c
    obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective c
    change (show HopfAlgebra.CartierDual R H.model.CoordinateRing from φ) (E.quotient q) =
      l (π φ)
    rw [hq]
    exact heval φ

/-- Original quotient coordinates are the full linear dual of the dual kernel ring. -/
def dualKernelPairingEquiv (E : FiniteFlatExtension A H Q) :
    Q.model.CoordinateRing ≃ₗ[R] Module.Dual R E.dualKernelRing :=
  LinearEquiv.ofBijective E.dualKernelPairing E.dualKernelPairing_bijective

/-- The scheme-theoretic dual kernel is linearly isomorphic to the intended Cartier dual. -/
def dualKernelLinearEquiv (E : FiniteFlatExtension A H Q) :
    E.dualKernelRing ≃ₗ[R] HopfAlgebra.CartierDual R Q.model.CoordinateRing := by
  let := E.dualKernelRing_flat
  let : Module.FinitePresentation R E.dualKernelRing :=
    Module.finitePresentation_of_finite R E.dualKernelRing
  let : Module.Projective R E.dualKernelRing := Module.Flat.projective_of_finitePresentation
  exact (Module.evalEquiv R E.dualKernelRing).trans
    (E.dualKernelPairingEquiv.dualMap.trans linearEquiv.symm)

/-- The linear equivalence is the canonical transposed quotient map on representatives. -/
theorem dualKernelLinearEquiv_mk (E : FiniteFlatExtension A H Q)
    (φ : HopfAlgebra.CartierDual R H.model.CoordinateRing) :
    E.dualKernelLinearEquiv
      (Ideal.Quotient.mk (HopfAlgebra.augmentationIdeal E.inclusion.cartierDual) φ) =
        bialgMap E.quotient φ := rfl

/-- The dual augmentation quotient is canonically the Cartier dual of the original quotient. -/
def dualKernelEquiv (E : FiniteFlatExtension A H Q) :
    E.dualKernelRing ≃ₐ[R] Q.cartierDual.model.CoordinateRing :=
  AlgEquiv.ofBijective E.dualKernelMap (by
    have he : (E.dualKernelMap : E.dualKernelRing → Q.cartierDual.model.CoordinateRing) =
        E.dualKernelLinearEquiv := by
      funext c
      obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective c
      rfl
    rw [he]
    exact E.dualKernelLinearEquiv.bijective)

/-- The canonical algebra equivalence agrees with the given transposed quotient. -/
@[simp] theorem dualKernelEquiv_mk (E : FiniteFlatExtension A H Q)
    (φ : H.cartierDual.model.CoordinateRing) :
    E.dualKernelEquiv
      (Ideal.Quotient.mk (HopfAlgebra.augmentationIdeal E.inclusion.cartierDual) φ) =
        E.quotient.cartierDual φ := rfl

end ThreeAdicPlan.FiniteFlatExtension
