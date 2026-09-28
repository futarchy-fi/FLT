/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.DyadicThreeGroupInertia

/-!
# Three-group representations of the dyadic absolute Galois group

Every continuous finite three-group quotient of the absolute Galois group of
`ℚ₂` is unramified. The proof passes to the finite extension cut out by the
kernel and applies the DVR inertia theorem.
-/

@[expose] public noncomputable section

open IsLocalRing NumberField

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- The integral closure in a finite dyadic Galois three-extension has trivial inertia. -/
theorem finiteLocalInertia_eq_bot_of_threeGroup
    (C : IntermediateField (twoAdicPlace.adicCompletion ℚ)
      (AlgebraicClosure (twoAdicPlace.adicCompletion ℚ)))
    [FiniteDimensional (twoAdicPlace.adicCompletion ℚ) C]
    [IsGalois (twoAdicPlace.adicCompletion ℚ) C]
    (hG : IsPGroup 3 Gal(C/twoAdicPlace.adicCompletion ℚ)) :
    (maximalIdeal (IntegralClosure (twoAdicPlace.adicCompletionIntegers ℚ) C)).inertia
      Gal(C/twoAdicPlace.adicCompletion ℚ) = ⊥ := by
  let O := twoAdicPlace.adicCompletionIntegers ℚ
  let B := IntegralClosure O C
  let : IsFractionRing B C := by
    dsimp only [B]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_finite_extension
      (twoAdicPlace.adicCompletion ℚ) C
  let : IsDedekindDomain B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.isDedekindDomain O (twoAdicPlace.adicCompletion ℚ) C
      (integralClosure O C)
  have hO : O ≠ ⊤ := by
    intro h
    apply IsDiscreteValuationRing.not_isField O
    exact h ▸ (Subring.topEquiv (R := twoAdicPlace.adicCompletion ℚ)).isField
      (Semifield.toIsField (twoAdicPlace.adicCompletion ℚ))
  let : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B (not_isField_integralClosure _ hO)).out 3 1).mp
      (inferInstance : IsDedekindDomain B)
  let : SMulDistribClass Gal(C/twoAdicPlace.adicCompletion ℚ) B C := ⟨fun g b x ↦ by
    simp only [Algebra.smul_def, smul_mul', mul_eq_mul_right_iff]
    left
    rfl⟩
  let : IsGaloisGroup Gal(C/twoAdicPlace.adicCompletion ℚ) O B :=
    IsGaloisGroup.of_isFractionRing Gal(C/twoAdicPlace.adicCompletion ℚ) O B
      (twoAdicPlace.adicCompletion ℚ) C
  exact inertia_eq_bot_of_threeGroup_residue_two O B _ hG
    (rationalCompletion_residueField_card 2 Nat.prime_two)

/-- A homomorphism to a three-group with open kernel kills dyadic absolute inertia.
No hypothesis about a chosen residual constituent is used. -/
theorem localInertia_le_ker_of_threeGroup
    {H : Type*} [Group H] (hH : IsPGroup 3 H)
    (f : Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ) →* H)
    (hf : IsOpen (f.ker : Set (Field.absoluteGaloisGroup
      (twoAdicPlace.adicCompletion ℚ)))) :
    localInertiaGroup twoAdicPlace ≤ f.ker := by
  let D : ClosedSubgroup (Field.absoluteGaloisGroup (twoAdicPlace.adicCompletion ℚ)) :=
    ⟨f.ker, f.ker.isClosed_of_isOpen hf⟩
  let C := IntermediateField.fixedField D.toSubgroup
  have hfix : C.fixingSubgroup = D.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField D
  let : FiniteDimensional (twoAdicPlace.adicCompletion ℚ) C :=
    (InfiniteGalois.isOpen_iff_finite C).mp (hfix ▸ hf)
  let : D.Normal := inferInstanceAs f.ker.Normal
  let : IsGalois (twoAdicPlace.adicCompletion ℚ) C := inferInstance
  let e := (InfiniteGalois.normalAutEquivQuotient D).symm.trans
    (QuotientGroup.quotientKerEquivRange f)
  have hG : IsPGroup 3 Gal(C/twoAdicPlace.adicCompletion ℚ) :=
    (hH.to_subgroup f.range).of_injective e.toMonoidHom e.injective
  have hI : localInertiaGroup twoAdicPlace ≤ C.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker C, ← Subgroup.map_eq_bot_iff,
      map_localInertiaGroup_eq_inertia twoAdicPlace C]
    exact finiteLocalInertia_eq_bot_of_threeGroup C hG
  change localInertiaGroup twoAdicPlace ≤ D.toSubgroup
  rwa [hfix] at hI

end ThreeAdicPlan
