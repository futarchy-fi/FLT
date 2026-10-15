/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNilpotentNodeChart
public import FLT.Mazur.PolygonArithmeticStageCoefficients
public import FLT.Mazur.WeierstrassSuccessiveXCoefficients

/-!
# Constructed original node charts at every arithmetic order

Divisibility of the original non-tangent coefficients by π constructs a node
open in the original successive equation over R/(π^(m+1)). The coefficient
ring need not contain its residue field, and no comparison is an input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)

/-- The original parameter ideal on the actual arithmetic quotient is nilpotent. -/
theorem arithmeticParameterIdeal_nilpotent :
    IsNilpotent (ideal (Quotient R π m) (parameter R π m)) := by
  refine ⟨m + 1, ?_⟩
  change Ideal.span {parameter R π m} ^ (m + 1) = (0 : Ideal (Quotient R π m))
  rw [Ideal.span_singleton_pow, parameter_pow]
  simp only [Ideal.span_singleton_zero, Ideal.zero_eq_bot]

/-- Original divisibility gives membership in the actual arithmetic parameter ideal. -/
theorem arithmeticCoefficient_mem {c : R} (hc : π ∣ c) :
    algebraMap R (Quotient R π m) c ∈ ideal (Quotient R π m) (parameter R π m) :=
  Ideal.mem_span_singleton.mpr (map_dvd (algebraMap R (Quotient R π m)) hc)

variable (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- The actual polygon node chart in the original arithmetic successive equation. -/
def arithmeticNodeChart : Spec (.of (PolygonSmoothing.ChartRing (parameter R π m))) ⟶
    Spec (.of (ExtendedCoordinate W s π b3 b4 b6 Q)) :=
  nilpotentPolygonChart (W.map q) (q s) (q π) (q b3) (q b4) (q b6) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
    (arithmeticCoefficient_mem π m hs) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6)

/-- Every arithmetic node comparison is an actual open immersion. -/
theorem arithmeticNodeChart_isOpenImmersion :
    IsOpenImmersion (arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6) :=
  nilpotentPolygonChart_isOpenImmersion ..

/-- The constructed arithmetic open preserves the original quotient coefficients. -/
@[reassoc] theorem arithmeticNodeChart_structure :
    arithmeticNodeChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap Q (ExtendedCoordinate W s π b3 b4 b6 Q))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (PolygonSmoothing.ChartRing (parameter R π m)))) :=
  nilpotentPolygonChart_structure ..

end FLT.Mazur.WeierstrassSuccessiveX
