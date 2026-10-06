/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicGaloisDescent
public import FLT.EllipticCurve.CubicPrimeCyclicDegree
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Descent
/-! # Étale prime cyclic quotients over fields

The actual invariant algebra is finite étale over a field, with dimension
p+1 at prime level. The proof embeds its scalar extension into the étale
generator algebra, then descends étaleness from an algebraic closure.
No perfection assumption on the field or invertibility of p-1 is needed.
This does not yet establish quotient étaleness over integral bases.
-/

open AlgebraicGeometry CategoryTheory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u

/-- A finite reduced algebra over a perfect field is étale. -/
theorem finiteReduced_etale_perfect (K A : Type u) [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [IsReduced A] :
    Algebra.Etale K A := by
  let : IsArtinianRing A := .of_finite K A
  let (I : MaximalSpectrum A) : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
  have (I : MaximalSpectrum A) : Algebra.FormallyEtale K (A ⧸ I.asIdeal) :=
    Algebra.FormallyEtale.of_isSeparable K _
  have : Algebra.FormallyEtale K A :=
    .of_equiv ((IsArtinianRing.equivPi A).restrictScalars K).symm
  have : Algebra.FinitePresentation K A :=
    (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

/-- The coordinate algebra of actual nonzero torsion is étale when its order is a unit. -/
theorem nonzeroTorsionRing_etale : Algebra.Etale R (NonzeroTorsionRing W n) := by
  have := nonzeroTorsionModel_etale W n (Fact.out : IsUnit (n : R))
  have hf : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R (NonzeroTorsionRing W n)))) := by
    change Etale (Scheme.Spec.map (Spec.fullyFaithful.preimage
      ((nonzeroTorsionModel W n).left.isoSpec.inv ≫ (nonzeroTorsionModel W n).hom)))
    rw [Spec.fullyFaithful.map_preimage]
    infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Etale)] at hf
  exact (RingHom.etale_algebraMap).mp hf

open scoped TensorProduct in
/-- A finite subalgebra of an étale field algebra is étale, even over an imperfect field. -/
theorem finiteSubalgebra_etale_field (K A : Type u) [Field K]
    [CommRing A] [Algebra K A] [Algebra.Etale K A] (D : Subalgebra K A)
    [Module.Finite K D] : Algebra.Etale K D := by
  let Ω := AlgebraicClosure K
  let f : Ω ⊗[K] D →ₐ[Ω] Ω ⊗[K] A := Algebra.TensorProduct.lTensor Ω D.val
  have hf : Function.Injective f := by
    change Function.Injective (LinearMap.lTensor Ω D.val.toLinearMap)
    exact Module.Flat.lTensor_preserves_injective_linearMap D.val.toLinearMap
      Subtype.val_injective
  have : IsReduced (Ω ⊗[K] A) :=
    Algebra.FormallyUnramified.isReduced_of_field Ω _
  have : IsReduced (Ω ⊗[K] D) := isReduced_of_injective f hf
  have : Algebra.Etale Ω (Ω ⊗[K] D) := finiteReduced_etale_perfect Ω _
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Ω

/-- The actual scalar invariant algebra is étale over its coefficient field. -/
theorem scalarInvariantRing_etale_field
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    (m : ℕ) [NeZero m] [Fact (IsUnit (m : K))] :
    Algebra.Etale K (TorsionScalarInvariantRing E m) := by
  have := nonzeroTorsionRing_etale E m
  have := torsionScalarInvariantRing_finite E m
  exact finiteSubalgebra_etale_field K (NonzeroTorsionRing E m)
    (TorsionScalarInvariantRing E m)

/-- The actual scalar quotient scheme is étale over a field. -/
theorem scalarQuotientModel_etale_field
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    (m : ℕ) [NeZero m] [Fact (IsUnit (m : K))] :
    Etale (scalarQuotientModel E m).hom := by
  change Etale (Spec.map (CommRingCat.ofHom
    (algebraMap K (TorsionScalarInvariantRing E m))))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact (RingHom.etale_algebraMap).mpr (scalarInvariantRing_etale_field E m)


/-- At prime level, the actual invariant coordinate algebra has dimension p+1. -/
theorem scalarInvariantRing_finrank_field
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : K))] :
    Module.finrank K (TorsionScalarInvariantRing E p) = p + 1 := by
  have := scalarInvariantRing_etale_field E p
  calc
    Module.finrank K (TorsionScalarInvariantRing E p) =
        Nat.card (TorsionScalarInvariantRing E p →ₐ[K] AlgebraicClosure K) :=
      GaloisModule.finrank_eq_natCard_algHom K (AlgebraicClosure K) _
    _ = Nat.card (pointSource (R := K) (AlgebraicClosure K) ⟶ scalarQuotientModel E p) :=
      Nat.card_congr (scalarQuotientCoordinatePointEquiv E p)
    _ = p + 1 := scalarQuotientFieldPoints_card E p (AlgebraicClosure K)

/-- The finite map forgetting a generator is étale over a field. -/
theorem scalarQuotientMap_etale_field
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    (m : ℕ) [NeZero m] [Fact (IsUnit (m : K))] :
    Etale (scalarQuotientMap E m).left := by
  have := scalarQuotientModel_etale_field E m
  have : Etale ((scalarQuotientMap E m).left ≫ (scalarQuotientModel E m).hom) := by
    rw [(scalarQuotientMap E m).w]
    exact nonzeroTorsionModel_etale E m Fact.out
  exact Etale.of_comp (scalarQuotientMap E m).left (scalarQuotientModel E m).hom

end WeierstrassCurve.CubicCharts
