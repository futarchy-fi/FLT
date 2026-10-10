/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatCoefficientIdeal
public import FLT.Mazur.LocalizedSmoothLocalEquation
public import FLT.Mazur.PrimeCoefficientLocalization

/-!
# Prime-local Cartier equations over arbitrary coefficient rings

Localizing the coefficient ring at the contracted prime supplies the local
base required for lifting residue equations. The resulting equation is in the
original ambient local ring; neither a local original base nor a prescribed
local map from that base is required.
-/

@[expose] public noncomputable section
open TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]

/-- Finite flat quotients on standard smooth curves have regular equations at every prime. -/
theorem regular_generator_standardSmooth_finite_flat_atPrime
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (q : Ideal B) [q.IsPrime] :
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
  let _ : IsLocalization (⊥ : Submonoid T) T := IsLocalization.self bot_le
  let _ : Algebra.IsStandardSmooth S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let J := I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  let _ := finite_coefficient_ideal_quotient (R := R) (S := S) I
  let _ := flat_coefficient_ideal_quotient (R := R) (S := S) I
  obtain ⟨a, ha, hJa⟩ := regular_generator_through_localized_smooth_chart
    (R := S) (B := T) (D := T) (A := A) ⊥ N N J
  refine ⟨a, ha, ?_⟩
  change (I.map (algebraMap B T)).map (algebraMap T A) = _ at hJa
  rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq B T A] at hJa

end FLT.Mazur.FCurve
