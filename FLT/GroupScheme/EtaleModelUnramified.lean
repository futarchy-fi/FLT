/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.Unramified
public import FLT.GaloisRepresentation.HardlyRamified.InertiaTwoSquareZero
public import FLT.GroupScheme.EtaleInertia
public import FLT.GroupScheme.PointFieldEvaluation
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Ramification of finite étale models away from two

Coordinate evaluation in the finite point field is embedded in a finite local
splitting field. Its integral values are fixed by inertia because the model is
formally unramified. Separation by integral coordinates recovers the point action.
-/

@[expose] public noncomputable section

open NumberField IsLocalRing NumberField.InertiaComparison

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- Any chain of algebra maps out of `ℤ[1/2]` is compatible. -/
theorem zInvTwo_scalarTower (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ZInvTwo A] [Algebra A B] [Algebra ZInvTwo B] :
    IsScalarTower ZInvTwo A B := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
  ext
  simp

/-- Two is a unit in the integer ring of an odd rational completion. -/
theorem two_isUnit_completionIntegers (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    IsUnit (2 : hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ) := by
  let O := hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ
  have hcard : Nat.card (ResidueField O) = q := rationalCompletion_residueField_card q hq
  let : Finite (ResidueField O) := Nat.finite_of_card_ne_zero (by
    simpa only [hcard] using hq.ne_zero)
  let : Fintype (ResidueField O) := Fintype.ofFinite _
  let : CharP (ResidueField O) q := (CharP.charP_iff_prime_eq_zero hq).mpr (by
    have hc := Nat.cast_card_eq_zero (ResidueField O)
    rw [← Nat.card_eq_fintype_card, hcard] at hc
    exact hc)
  by_contra h
  have hz : residue O (2 : O) = 0 := (residue_eq_zero_iff (2 : O)).mpr h
  rw [map_ofNat] at hz
  have hdiv : q ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField O) q 2).mp hz
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdiv)

/-- The localization at two maps to the integer ring at every odd rational prime. -/
def zInvTwoToCompletionIntegers (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    ZInvTwo →+* hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ :=
  IsLocalization.Away.lift (2 : ℤ)
    (show IsUnit ((algebraMap ℤ
      (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletionIntegers ℚ)) 2) by
      simpa only [map_ofNat] using two_isUnit_completionIntegers q hq hq2)

/-- The chosen embedding of a global field, with codomain its local compositum. -/
def localCompositumEmbedding
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) : L →ₐ[ℚ] localCompositum v L where
  toFun x := ⟨localEmbedding v L x, IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (localEmbedding v L))
  map_mul' x y := Subtype.ext (map_mul (localEmbedding v L) x y)
  map_zero' := Subtype.ext (map_zero (localEmbedding v L))
  map_add' x y := Subtype.ext (map_add (localEmbedding v L) x y)
  commutes' q := by
    apply Subtype.ext
    simp

/-- Local restriction commutes with the embedding into the finite local compositum. -/
theorem localCompositumEmbedding_equivariant
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ L]
    (σ : Field.absoluteGaloisGroup (v.adicCompletion ℚ)) (x : L) :
    AlgEquiv.restrictNormalHom (localCompositum v L) σ (localCompositumEmbedding v L x) =
      localCompositumEmbedding v L (localRestriction v L σ x) := by
  apply Subtype.ext
  exact (AlgEquiv.restrictNormalHom_apply (localCompositum v L) σ
    (localCompositumEmbedding v L x)).trans (localEmbedding_equivariant v L σ x).symm

/-- A finite étale model over `ℤ[1/2]` has unramified geometric point action at
every odd rational prime, including three. -/
theorem FiniteEtaleModel.unramifiedOutsideTwo {W : FiniteContinuousGaloisModule}
    (M : FiniteEtaleModel ZInvTwo W) : UnramifiedOutside {2} W := by
  constructor
  intro q hq hqS σ hσ w
  have hq2 : q ≠ 2 := by simpa using hqS
  let v := hq.toHeightOneSpectrumRingOfIntegersRat
  let O := v.adicCompletionIntegers ℚ
  let L := W.pointField
  let C := localCompositum v L
  let B := IntegralClosure O C
  let : Algebra ZInvTwo O := (zInvTwoToCompletionIntegers q hq hq2).toAlgebra
  let : Algebra ZInvTwo C := Algebra.compHom C (algebraMap ZInvTwo ℚ)
  let : Algebra ZInvTwo B := Algebra.compHom B (algebraMap ZInvTwo O)
  let : IsScalarTower ZInvTwo ℚ C := zInvTwo_scalarTower ℚ C
  let : IsScalarTower ZInvTwo O C := zInvTwo_scalarTower O C
  let : IsScalarTower ZInvTwo O B := zInvTwo_scalarTower O B
  let : IsScalarTower ZInvTwo B C := zInvTwo_scalarTower B C
  let : IsScalarTower ZInvTwo ZInvTwo C := zInvTwo_scalarTower ZInvTwo C
  let : IsFractionRing B C := by
    dsimp only [B]
    delta IntegralClosure
    exact integralClosure.isFractionRing_of_finite_extension (v.adicCompletion ℚ) C
  let : IsDedekindDomain B := by
    dsimp only [B]
    delta IntegralClosure
    exact IsIntegralClosure.isDedekindDomain O (v.adicCompletion ℚ) C (integralClosure O C)
  have hO : O ≠ ⊤ := by
    intro h
    apply IsDiscreteValuationRing.not_isField O
    exact h ▸ (Subring.topEquiv (R := v.adicCompletion ℚ)).isField
      (Semifield.toIsField (v.adicCompletion ℚ))
  let : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B (not_isField_integralClosure _ hO)).out 3 1).mp
      (inferInstance : IsDedekindDomain B)
  let : SMulCommClass Gal(C/v.adicCompletion ℚ) ZInvTwo B := ⟨fun g r b ↦ by
    have he : (MulSemiringAction.toRingHom Gal(C/v.adicCompletion ℚ) B g).comp
        (algebraMap ZInvTwo B) = algebraMap ZInvTwo B := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
      exact Subsingleton.elim _ _
    have hr : g • algebraMap ZInvTwo B r = algebraMap ZInvTwo B r :=
      DFunLike.congr_fun he r
    simp only [Algebra.smul_def, smul_mul', hr]⟩
  let fC : M.CoordinateRing →ₐ[ZInvTwo] C :=
    ((localCompositumEmbedding v L).restrictScalars ZInvTwo).comp
      (M.toHasFiniteFlatModel.pointFieldPoint w)
  let f : M.CoordinateRing →ₐ[ZInvTwo] B :=
    { toFun := fun a ↦ ⟨fC a, IsIntegral.tower_top (A := O)
        ((Algebra.IsIntegral.isIntegral (R := ZInvTwo) a).map fC)⟩
      map_one' := Subtype.ext (map_one fC)
      map_mul' a b := Subtype.ext (map_mul fC a b)
      map_zero' := Subtype.ext (map_zero fC)
      map_add' a b := Subtype.ext (map_add fC a b)
      commutes' r := by
        apply Subtype.ext
        exact (fC.commutes r).trans (IsScalarTower.algebraMap_apply ZInvTwo B C r) }
  let g := AlgEquiv.restrictNormalHom C σ
  have hg : g ∈ (maximalIdeal B).inertia Gal(C/v.adicCompletion ℚ) := by
    rw [← map_localInertiaGroup_eq_inertia v C]
    exact ⟨σ, hσ, rfl⟩
  have hw : Field.absoluteGaloisGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) σ • w = w := by
    apply M.toHasFiniteFlatModel.pointFieldPoint_injective
    apply AlgHom.ext
    intro a
    rw [M.toHasFiniteFlatModel.pointFieldPoint_smul]
    change localRestriction v L σ (M.toHasFiniteFlatModel.pointFieldPoint w a) = _
    apply (localCompositumEmbedding v L).injective
    change localCompositumEmbedding v L
      (localRestriction v L σ (M.toHasFiniteFlatModel.pointFieldPoint w a)) =
      localCompositumEmbedding v L (M.toHasFiniteFlatModel.pointFieldPoint w a)
    rw [← localCompositumEmbedding_equivariant]
    exact congrArg Subtype.val
      (Algebra.FormallyUnramified.inertia_smul_algHom_apply f g hg a)
  convert hw using 1
  congr 4
  exact Subsingleton.elim _ _

end ThreeAdicPlan
