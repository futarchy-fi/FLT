/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.WeierstrassModificationXNodeIncidenceOpen
public import FLT.Mazur.WeierstrassModificationXStandardPunctureRange
public import FLT.Mazur.WeierstrassModificationXArithmeticPuncture

/-!
# The exact initial puncture in the original arithmetic tensor chart

Both full initial labels pull back the original tensor incidence open to
standard D(p), retaining the complete original coefficient comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "r₀" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hr₀" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)
local notation "hm₀" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q)
  (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3)
  (arithmeticCoefficient_mem π m h4) (arithmeticCoefficient_mem π m h6)



local notation "A" => Coordinate W s b3 b4 b6
local notation "L" => PolynomialNodeOpen (W.map q) (q s)
local notation "e" => arithmeticInitialTensorIso π m W s b3 b4 b6
local notation "T" => (1 : Q) ⊗ₜ[R] t W s b3 b4 b6
local notation "p" => algebraMap (NodalFiber.Coordinate (q s)) L (NodalFiber.p (q s))

/-- The original tensor coefficient comparison preserves the entire incidence principal open. -/
theorem arithmeticInitialTensorIso_t_preimage :
    (e).hom ⁻¹' (PrimeSpectrum.basicOpen T : Set (PrimeSpectrum (Q ⊗[R] A))) =
      (PrimeSpectrum.basicOpen (t (W.map q) (q s) (q b3) (q b4) (q b6)) :
        Set (PrimeSpectrum (ExtendedCoordinate W s b3 b4 b6 Q))) := by
  ext z
  change (baseChangeEquiv W s b3 b4 b6 Q T ∉ z.asIdeal) ↔ _
  rw [baseChangeEquiv_t]
  rfl

variable (label : Bool)
local notation "F" => ite (label = true)
  (arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6)
  (arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6)

/-- Both full initial tensor labels have the same standard incidence preimage D(p). -/
theorem arithmeticInitialTensorNodes_incidence_preimage :
    F ⁻¹' (PrimeSpectrum.basicOpen T : Set (PrimeSpectrum (Q ⊗[R] A))) =
      (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum L)) := by
  have hf := polynomialNodeChart_incidence_preimage (W.map q) (q s) (q b3) (q b4) (q b6)
    r₀ hr₀ J (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)
  have hg := polynomialOppositeNodeChart_incidence_preimage
    (W.map q) (q s) (q b3) (q b4) (q b6) r₀ hr₀ J
      (arithmeticParameterIdeal_nilpotent π m) hm₀ (arithmeticCoefficient_mem π m h3)
  cases label
  · exact (congrArg (fun U =>
      (arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) ⁻¹' U)
        (arithmeticInitialTensorIso_t_preimage π m W s b3 b4 b6)).trans hf
  · exact (congrArg (fun U =>
      (arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) ⁻¹' U)
        (arithmeticInitialTensorIso_t_preimage π m W s b3 b4 b6)).trans hg

variable (hs : π ∣ s)

/-- The actual arithmetic puncture inclusion has exactly the full standard D(p) image. -/
theorem arithmeticInitialPunctureInclusion_range :
    Set.range (arithmeticInitialPunctureInclusion π m W s ha hs) =
      (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum L)) :=
  initialNodeStandardPuncture_spec_range (W.map q) (q s) J
    (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m hs)

/-- The full original tensor overlap pulls back to precisely the constructed puncture. -/
theorem arithmeticInitialTensorNodes_puncture_preimage :
    F ⁻¹' Set.range (PrincipalOpenTensor.inclusion Q (t W s b3 b4 b6)) =
      Set.range (arithmeticInitialPunctureInclusion π m W s ha hs) := by
  rw [arithmeticInitialPunctureInclusion_range]
  change F ⁻¹' Set.range (PrimeSpectrum.comap
    (algebraMap (Q ⊗[R] A) (Localization.Away T))) = _
  rw [PrimeSpectrum.localization_away_comap_range _ T]
  exact arithmeticInitialTensorNodes_incidence_preimage π m W s b3 b4 b6 ha h2 h3 h4 h6 label

end FLT.Mazur.WeierstrassModificationX
