/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapDenominator

/-!
# The full initial-node intersection is the standard D(q)

The original two initial charts intersect along D(q) in the first full
node D(q+a₁). The opposite leg is the unique restriction of the actual map.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s : R)
local notation "N" => NodalFiber.Coordinate s
local notation "L" => PolynomialNodeOpen W s
local notation "Q" => algebraMap N L (NodalFiber.q s)

/-- The full other puncture of the initial node, with both q and q+a₁ invertible. -/
abbrev PolynomialNodeOverlap := Localization.Away Q

/-- The standard D(q) inclusion in the full initial node. -/
def polynomialNodeOverlapInclusion : Spec (.of (PolynomialNodeOverlap W s)) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L (PolynomialNodeOverlap W s)))

instance polynomialNodeOverlapInclusion_isOpenImmersion :
    IsOpenImmersion (polynomialNodeOverlapInclusion W s) :=
  IsOpenImmersion.of_isLocalization Q

/-- The standard overlap retains the entire q-principal open. -/
theorem polynomialNodeOverlapInclusion_range :
    Set.range (polynomialNodeOverlapInclusion W s) =
      (PrimeSpectrum.basicOpen Q : Set (PrimeSpectrum L)) :=
  PrimeSpectrum.localization_away_comap_range _ _

variable (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "f" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "g" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "i" => polynomialNodeOverlapInclusion W s

/-- The whole standard D(q) maps to the original opposite full node. -/
theorem polynomialNodeOverlap_range_subset : Set.range (i ≫ f) ⊆ Set.range g := by
  rintro _ ⟨z, rfl⟩
  have hz : i z ∈ Set.range i := ⟨z, rfl⟩
  rw [polynomialNodeOverlapInclusion_range,
    ← polynomialNodeChart_opposite_preimage W s b3 b4 b6 r hr I hI hrI h3] at hz
  exact hz

/-- The actual opposite-node restriction on the full initial-node intersection. -/
def polynomialNodeOverlapOpposite :
    Spec (.of (PolynomialNodeOverlap W s)) ⟶ Spec (.of L) :=
  IsOpenImmersion.lift g (i ≫ f)
    (polynomialNodeOverlap_range_subset W s b3 b4 b6 r hr I hI hrI h3)

/-- The opposite restriction preserves every original initial-chart function. -/
@[reassoc] theorem polynomialNodeOverlapOpposite_global :
    polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3 ≫ g = i ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The standard D(q) with its two original restrictions is the full scheme intersection. -/
theorem polynomialNodeOverlap_isPullback :
    IsPullback i (polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3) f g := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact (polynomialNodeOverlapOpposite_global W s b3 b4 b6 r hr I hI hrI h3).symm
  · apply TopologicalSpace.Opens.ext
    change f ⁻¹' Set.range g = Set.range i
    rw [polynomialNodeChart_opposite_preimage, polynomialNodeOverlapInclusion_range]

/-- The opposite restriction of the standard overlap is itself an open immersion. -/
instance polynomialNodeOverlapOpposite_isOpenImmersion :
    IsOpenImmersion (polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3) :=
  MorphismProperty.of_isPullback
    (polynomialNodeOverlap_isPullback W s b3 b4 b6 r hr I hI hrI h3) inferInstance

/-- The standard puncture is canonically the categorical pullback of the two full initial nodes. -/
def polynomialNodeOverlapIso :=
  (polynomialNodeOverlap_isPullback W s b3 b4 b6 r hr I hI hrI h3).isoPullback

end FLT.Mazur.WeierstrassModificationX
