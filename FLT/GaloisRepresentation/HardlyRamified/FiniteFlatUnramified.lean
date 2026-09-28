/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryD
public import FLT.GroupScheme.IntegralHopfPoints
public import FLT.FreyCurve.Serre.LocalInertia

/-!
# Unramifiedness of finite-flat three-torsion away from two and three

Finite-flat models give integral-valued geometric points. At a prime other than
three, reduction is injective on their three-torsion by the convolution/Nakayama
argument. Inertia fixes every residue, and therefore every geometric point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
attribute [local instance 100000] Algebra.toSMul Algebra.toModule
open scoped TensorProduct
open WithConv
namespace ThreeAdicPlan

/-- Algebra structures out of the integer localization have compatible scalar towers. -/
theorem zInvTwo_scalarTower (S T : Type) [CommRing S] [CommRing T]
    [Algebra ZInvTwo S] [Algebra S T] [Algebra ZInvTwo T] :
    IsScalarTower ZInvTwo S T := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (Submonoid.powers (2 : ℤ))
  ext
  simp

/-- A finite-flat model over `ℤ[1/2]` killed by three is unramified outside two and three. -/
theorem FiniteFlatObject.unramifiedOutside_of_killedBy_three
    (H : FiniteFlatObject ZInvTwo) (hk : KilledBy 3 H) :
    UnramifiedOutside {2, 3} H.points := by
  constructor
  intro p hp hpS σ hσ w
  have hp2 : p ≠ 2 := by intro h; exact hpS (by simp [h])
  have hp3 : p ≠ 3 := by intro h; exact hpS (by simp [h])
  let v := hp.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let O := v.adicCompletionIntegers ℚ
  let Ω := AlgebraicClosure K
  let B := integralClosure O Ω
  let : IsLocalRing B := inferInstanceAs (IsLocalRing
    (IntegralClosure (v.adicCompletionIntegers ℚ) (AlgebraicClosure (v.adicCompletion ℚ))))
  let : Algebra ZInvTwo O := (IsLocalization.Away.lift (2 : ℤ)
    (show IsUnit (algebraMap ℤ O 2) by
      simpa only [map_ofNat, Nat.cast_ofNat] using
        NumberField.prime_isUnit_adicCompletionIntegers Nat.prime_two hp hp2)).toAlgebra
  let : Algebra ZInvTwo K := Algebra.compHom K (algebraMap ZInvTwo ℚ)
  let : Algebra ZInvTwo Ω := Algebra.compHom Ω (algebraMap ZInvTwo K)
  let : IsScalarTower ZInvTwo ℚ K := zInvTwo_scalarTower _ _
  let : IsScalarTower ZInvTwo ℚ Ω := zInvTwo_scalarTower _ _
  let : IsScalarTower ZInvTwo O Ω := zInvTwo_scalarTower _ _
  let j : AlgebraicClosure ℚ →ₐ[ℚ] Ω :=
    { __ := AlgebraicClosure.map (algebraMap ℚ K)
      commutes' := fun r ↦ (AlgebraicClosure.map_algebraMap (algebraMap ℚ K) r).trans
        (IsScalarTower.algebraMap_apply ℚ K Ω r).symm }
  let A := H.model.CoordinateRing
  let F : (ℚ ⊗[ZInvTwo] A →ₐ[ℚ] AlgebraicClosure ℚ) →*
      WithConv (A →ₗ[ZInvTwo] B) :=
    convolutionLinearMap.comp ((integralPointConvolution O).comp
      ((convolutionPostcomp (j.restrictScalars ZInvTwo)).comp
        (genericPointConvolution ZInvTwo ℚ (AlgebraicClosure ℚ) A)))
  have hcube (f : ℚ ⊗[ZInvTwo] A →ₐ[ℚ] AlgebraicClosure ℚ) : f ^ 3 = 1 := by
    apply Additive.ofMul.injective
    apply H.model.points_bijective.1
    change H.model.points (3 • Additive.ofMul f) = H.model.points 0
    rw [map_nsmul, map_zero]
    exact hk _
  have h3B : IsUnit (3 : B) := by
    simpa only [map_ofNat, Nat.cast_ofNat] using
      (NumberField.prime_isUnit_adicCompletionIntegers Nat.prime_three hp hp3).map
        (algebraMap O B)
  obtain ⟨f, rfl⟩ := H.model.points_bijective.2 w
  let τ := Field.absoluteGaloisGroup.map (algebraMap ℚ K) σ
  have he : F (τ • f.toMul) = F f.toMul := by
    refine convolution_eq_of_cube_eq_one _ _ ?_ ?_ h3B ?_
    · rw [← map_pow, hcube, map_one]
    · rw [← map_pow, hcube, map_one]
    · intro a
      have h := hσ ((F f.toMul) a)
      change σ • (F f.toMul) a - (F f.toMul) a ∈ IsLocalRing.maximalIdeal B at h
      change (F (τ • f.toMul)) a - (F f.toMul) a ∈ IsLocalRing.maximalIdeal B
      have heq : (F (τ • f.toMul)) a = σ • (F f.toMul) a := by
        apply Subtype.ext
        exact Field.absoluteGaloisGroup.lift_map (algebraMap ℚ K) σ
          (f.toMul ((1 : ℚ) ⊗ₜ[ZInvTwo] a))
      rw [heq]
      exact h
  have hfix : τ • H.model.points f = H.model.points f := by
    rw [← map_smul H.model.points]
    apply congrArg H.model.points
    apply Additive.toMul.injective
    apply (Bialgebra.restrictPoints ZInvTwo ℚ (AlgebraicClosure ℚ) A).injective
    ext a
    apply j.injective
    exact congrArg (fun t : WithConv (A →ₗ[ZInvTwo] B) ↦ (t a : Ω)) he
  convert hfix using 1
  congr 4
  exact Subsingleton.elim _ _

end ThreeAdicPlan
