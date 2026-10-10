/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrimeSmoothFiniteFlatCartier

/-!
# Prime-local equations through smooth principal charts

A finite flat family on a finitely presented ambient retains its regular
local equations when smooth coordinates exist only on a principal neighborhood.
Coefficient localization and the intermediate chart are both constructed;
no finiteness of the quotient on that smaller chart is needed.
-/

@[expose] public noncomputable section
open TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FinitePresentation R B]

/-- A smooth principal chart supplies the regular equation at the original ambient prime. -/
theorem regular_generator_smooth_away_finite_flat_atPrime
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (q : Ideal B) [q.IsPrime] (s : B) (hs : s ∉ q)
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Localization.Away s)] :
    ∃ a : Localization.AtPrime q, IsRegular a ∧
      I.map (algebraMap B (Localization.AtPrime q)) = Ideal.span {a} := by
  let p := q.under R
  let S := Localization.AtPrime p
  let T := S ⊗[R] B
  let A := Localization.AtPrime q
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  let _ := (primeCoefficientLift p q).toAlgebra
  let _ := primeCoefficientLift_tower_right p q
  let _ := primeCoefficientLift_tower_left p q
  let _ := primeCoefficient_localHom p q
  let N := q.primeCompl.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  let _ : IsLocalization N A := primeCoefficientLift_isLocalization p q
  let t : T := 1 ⊗ₜ[R] s
  let D := Localization.Away t
  have hN : Submonoid.powers t ≤ N :=
    Submonoid.powers_le.mpr ⟨s, hs, rfl⟩
  let _ := IsLocalization.localizationAlgebraOfSubmonoidLe D A (.powers t) N hN
  let _ := IsLocalization.localization_isScalarTower_of_submonoid_le D A (.powers t) N hN
  let _ : IsScalarTower S D A := .to₁₃₄ S T D A
  let L := N.map (algebraMap T D)
  let _ : IsLocalization L A :=
    IsLocalization.isLocalization_of_submonoid_le D A (.powers t) N hN
  let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 S D :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (IsLocalization.Away.tensorProductEquivTMulRight R S s (Localization.Away s))
  let J := I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  let _ := finite_coefficient_ideal_quotient (R := R) (S := S) I
  let _ := flat_coefficient_ideal_quotient (R := R) (S := S) I
  obtain ⟨a, ha, hJa⟩ := regular_generator_through_localized_smooth_chart
    (R := S) (B := T) (D := D) (A := A) (.powers t) N L J
  refine ⟨a, ha, ?_⟩
  change (I.map (algebraMap B T)).map (algebraMap T A) = _ at hJa
  rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq B T A] at hJa

end FLT.Mazur.FCurve
