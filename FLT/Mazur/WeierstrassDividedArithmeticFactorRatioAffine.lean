/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCanonicalFactorRatioTransport
public import FLT.Mazur.WeierstrassModificationXArithmeticFactorRatioNilpotence

/-!
# Full corrected affine polygon maps in the arithmetic quotient system

The original parameter ideal supplies nilpotence. Every quotient order uses
its own canonical root and the original entire initial affine coordinate ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m

local notation "hn" => Fact.mk (arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π m hs)

/-- The full polygon with the exact constructed arithmetic smoothing. -/
def arithmeticFactorRatioPolygon (k : ℕ) : Scheme :=
  @PolygonInfinitesimal.scheme Q _ τ hn (2 * k + 3) (by omega)

/-- The original entire initial affine chart maps into the corrected arithmetic polygon. -/
def arithmeticFactorRatioAffinePolygonMap (k : ℕ) :
    Spec (.of (ExtendedCoordinate W s b3 b4 b6 Q)) ⟶
      arithmeticFactorRatioPolygon π m W s ha hs k := by
  let _ := hn
  let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q) (ha.map q) (q s))) := hn
  exact canonicalFactorRatioAffinePolygonMap (W.map q) (ha.map q) (q s) (q b3) (q b4) (q b6)
    J (arithmeticParameterIdeal_nilpotent π m) (arithmeticCoefficient_mem π m h2)
    (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
    (arithmeticCoefficient_mem π m h6) k

/-- Both original entire node charts retain their corrected original cyclic labels. -/
@[reassoc] theorem arithmeticFactorRatioAffinePolygonMap_chart (k : ℕ) (b : Bool) :
    (if b then arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
      else arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) ≫
        arithmeticFactorRatioAffinePolygonMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k =
      arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
        (if b then (branchSwapIso Q τ).hom else 𝟙 _) ≫
          @PolygonInfinitesimal.chart Q _ τ hn (2 * k + 3) (by omega) (initialPolygonIndex k b) :=
  by
    let _ := hn
    let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q) (ha.map q) (q s))) := hn
    exact canonicalFactorRatioAffinePolygonMap_chart ..

/-- The complete arithmetic affine comparison preserves its actual quotient coefficients. -/
@[reassoc] theorem arithmeticFactorRatioAffinePolygonMap_structure (k : ℕ) :
    arithmeticFactorRatioAffinePolygonMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k ≫
      @PolygonInfinitesimal.toBase Q _ τ (2 * k + 3) hn (by omega) =
        Spec.map (CommRingCat.ofHom (algebraMap Q (ExtendedCoordinate W s b3 b4 b6 Q))) :=
  by
    let _ := hn
    let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q) (ha.map q) (q s))) := hn
    exact canonicalFactorRatioAffinePolygonMap_structure ..

/-- The polygon restriction uses the original quotient homomorphism and exact normalized scale. -/
def arithmeticFactorRatioPolygonRestriction (k : ℕ) :
    arithmeticFactorRatioPolygon π m W s ha hs k ⟶
      arithmeticFactorRatioPolygon π (m + 1) W s ha hs k := by
  let _ := hn
  let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q) (ha.map q) (q s))) := hn
  let _ : Fact (IsNilpotent (arithmeticInitialMobiusSmoothing W ha s π (m + 1))) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π (m + 1) hs⟩
  exact PolygonInfinitesimal.parameterProjection (restriction R π m).toRingHom
    (arithmeticInitialMobiusSmoothing W ha s π (m + 1)) τ
    (arithmeticInitialMobiusSmoothing_restriction W ha s π m) (2 * k + 3) (by omega)

attribute [local irreducible] canonicalFactorRatioAffinePolygonMap

/-- The complete original initial affine quotient square commutes at every arithmetic order. -/
@[reassoc] theorem arithmeticFactorRatioAffinePolygonMap_restriction (k : ℕ) :
    arithmeticFactorRatioAffinePolygonMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k ≫
      arithmeticFactorRatioPolygonRestriction π m W s ha hs k =
        arithmeticInitialRestriction R π m W s b3 b4 b6 ≫
          arithmeticFactorRatioAffinePolygonMap π (m + 1) W s b3 b4 b6
            ha hs h2 h3 h4 h6 k := by
  let _ := hn
  let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q) (ha.map q) (q s))) := hn
  let _ : Fact (IsNilpotent (arithmeticInitialMobiusSmoothing W ha s π (m + 1))) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π (m + 1) hs⟩
  unfold arithmeticFactorRatioAffinePolygonMap arithmeticFactorRatioPolygonRestriction
    arithmeticInitialRestriction arithmeticInitialCoefficientRingMap
    arithmeticInitialMobiusSmoothing
  let q₁ := algebraMap R (Quotient R π (m + 1))
  let _ : Fact (IsNilpotent (initialTangentSmoothing (W.map q₁) (ha.map q₁) (q₁ s))) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π (m + 1) hs⟩
  apply canonicalFactorRatioAffinePolygonMap_coefficient_of_eq
  exact arithmeticParameterIdeal_restriction R π m

end FLT.Mazur.WeierstrassDividedDepth
