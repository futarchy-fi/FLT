/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicCyclicEtaleField
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalRing.Module
/-! # Integral cyclic parameters over Dedekind bases

The invariant algebra is flat over a Dedekind base. The invariant
inclusion remains injective after arbitrary base change: its cokernel
embeds into a torsion-free module of scalar differences. All field
fibers are therefore étale; finite differentials and Nakayama give
étaleness over the integral base. Prime-level fibers have dimension p+1.
-/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable (W : WeierstrassCurve R) [W.IsElliptic]
variable (n : ℕ) [NeZero n] [Fact (IsUnit (n : R))]

/-- The actual scalar invariant algebra is flat over a Dedekind base. -/
theorem scalarInvariantRing_flat_dedekind :
    Module.Flat R (TorsionScalarInvariantRing W n) := by
  have := nonzeroTorsionRing_etale W n
  have : Module.IsTorsionFree R (TorsionScalarInvariantRing W n) :=
    Function.Injective.moduleIsTorsionFree _ Subtype.val_injective
      (fun r x => (TorsionScalarInvariantRing W n).val.toLinearMap.map_smul r x)
  infer_instance

/-- The scalar invariant inclusion remains injective after any base change over Dedekind. -/
theorem scalarInvariantTensor_injective (S : Type u) [CommRing S] [Algebra R S] :
    Function.Injective (Algebra.TensorProduct.lTensor S (TorsionScalarInvariantRing W n).val :
      S ⊗[R] TorsionScalarInvariantRing W n →ₐ[S] S ⊗[R] NonzeroTorsionRing W n) := by
  let A := NonzeroTorsionRing W n
  let D := TorsionScalarInvariantRing W n
  have := nonzeroTorsionRing_etale W n
  let δ : A →ₗ[R] ((ZMod n)ˣ → A) := LinearMap.pi
    (fun σ => (nonzeroTorsionRingScalar W n σ).toLinearMap - LinearMap.id)
  have : Module.Flat R δ.range := inferInstance
  have he : Function.Exact D.val.toLinearMap δ.rangeRestrict := by
    intro a
    constructor
    · intro ha
      refine ⟨⟨a, ?_⟩, rfl⟩
      intro σ
      have h := congrArg (fun x : δ.range => (x.val σ)) ha
      exact sub_eq_zero.mp h
    · rintro ⟨d, rfl⟩
      apply Subtype.ext
      ext σ
      exact sub_eq_zero.mpr (d.property σ)
  change Function.Injective (LinearMap.lTensor S D.val.toLinearMap)
  exact LinearMap.lTensor_injective_of_exact_of_flat δ.rangeRestrict
    δ.surjective_rangeRestrict D.val.toLinearMap Subtype.val_injective he S

/-- A finite field algebra embedding in an étale algebra is étale. -/
theorem finiteAlgebra_etale_of_injective_field (K A B : Type u) [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Module.Finite K A]
    [Algebra.Etale K B] (f : A →ₐ[K] B) (hf : Function.Injective f) :
    Algebra.Etale K A := by
  have : Module.Finite K f.range :=
    Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  have := finiteSubalgebra_etale_field K B f.range
  exact Algebra.Etale.of_equiv (AlgEquiv.ofInjective f hf).symm

/-- Every field fiber of the integral scalar quotient is étale. -/
theorem scalarInvariantRing_fieldFiber_etale_dedekind
    (K : Type u) [Field K] [Algebra R K] :
    Algebra.Etale K (K ⊗[R] TorsionScalarInvariantRing W n) := by
  have := nonzeroTorsionRing_etale W n
  have := torsionScalarInvariantRing_finite W n
  exact finiteAlgebra_etale_of_injective_field K _ _
    (Algebra.TensorProduct.lTensor K (TorsionScalarInvariantRing W n).val)
    (scalarInvariantTensor_injective W n K)


/-- A finite flat algebra with étale field fibers over a noetherian base is étale. -/
theorem finiteFlat_etale_of_fieldFibers
    (S A : Type u) [CommRing S] [IsNoetherianRing S] [CommRing A] [Algebra S A]
    [Module.Finite S A] [Module.Flat S A]
    (h : ∀ (K : Type u) [Field K] [Algebra S K], Algebra.Etale K (K ⊗[S] A)) :
    Algebra.Etale S A := by
  have : Module.Finite S (KaehlerDifferential S A) := Module.Finite.trans A _
  have hs : Subsingleton (KaehlerDifferential S A) := by
    apply (Module.support_eq_empty_iff (R := S)).mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    let K := q.asIdeal.ResidueField
    have := h K
    let : Algebra A (K ⊗[S] A) := Algebra.TensorProduct.rightAlgebra
    have he := KaehlerDifferential.tensorKaehlerEquivBase S K A (K ⊗[S] A)
    have : Subsingleton (K ⊗[S] KaehlerDifferential S A) :=
      he.toEquiv.subsingleton_congr.mpr inferInstance
    exact not_nontrivial_iff_subsingleton.mpr this
  have : Algebra.FormallyUnramified S A := ⟨hs⟩
  have : Algebra.FinitePresentation S A :=
    (Algebra.FinitePresentation.of_finiteType (R := S)).mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- The actual invariant coordinate algebra is étale over a Dedekind base. -/
theorem scalarInvariantRing_etale_dedekind :
    Algebra.Etale R (TorsionScalarInvariantRing W n) := by
  have := torsionScalarInvariantRing_finite W n
  have := scalarInvariantRing_flat_dedekind W n
  exact finiteFlat_etale_of_fieldFibers R _ (scalarInvariantRing_fieldFiber_etale_dedekind W n)

/-- The actual scalar quotient scheme is finite étale over a Dedekind base. -/
theorem scalarQuotientModel_etale_dedekind :
    Etale (scalarQuotientModel W n).hom := by
  change Etale (Spec.map (CommRingCat.ofHom
    (algebraMap R (TorsionScalarInvariantRing W n))))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact (RingHom.etale_algebraMap).mpr (scalarInvariantRing_etale_dedekind W n)


/-- Forgetting a generator is étale over a Dedekind coefficient base. -/
theorem scalarQuotientMap_etale_dedekind :
    Etale (scalarQuotientMap W n).left := by
  have := scalarQuotientModel_etale_dedekind W n
  have : Etale ((scalarQuotientMap W n).left ≫ (scalarQuotientModel W n).hom) := by
    rw [(scalarQuotientMap W n).w]
    exact nonzeroTorsionModel_etale W n Fact.out
  exact Etale.of_comp (scalarQuotientMap W n).left (scalarQuotientModel W n).hom

/-- Every prime-level field fiber has dimension p+1 over a Dedekind base. -/
theorem scalarInvariantRing_field_finrank_dedekind
    (p : ℕ) [Fact p.Prime] [NeZero p] [Fact (IsUnit (p : R))]
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] TorsionScalarInvariantRing W p) = p + 1 := by
  have := scalarInvariantRing_fieldFiber_etale_dedekind W p K
  let Ω := AlgebraicClosure K
  calc
    Module.finrank K (K ⊗[R] TorsionScalarInvariantRing W p) =
        Nat.card ((K ⊗[R] TorsionScalarInvariantRing W p) →ₐ[K] Ω) :=
      GaloisModule.finrank_eq_natCard_algHom K Ω _
    _ = Nat.card (TorsionScalarInvariantRing W p →ₐ[R] Ω) :=
      Nat.card_congr (AlgHom.liftEquiv R K (TorsionScalarInvariantRing W p) Ω).symm
    _ = Nat.card (pointSource (R := R) Ω ⟶ scalarQuotientModel W p) :=
      Nat.card_congr (scalarQuotientCoordinatePointEquiv W p)
    _ = p + 1 := scalarQuotientFieldPoints_card W p Ω

end WeierstrassCurve.CubicCharts
