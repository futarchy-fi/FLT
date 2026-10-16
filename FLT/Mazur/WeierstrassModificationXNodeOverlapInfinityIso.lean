/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlap
public import FLT.Mazur.WeierstrassModificationXNodeInfinityDenominators

/-!
# The full original infinity boundary is the standard node overlap

An actual scheme isomorphism identifies PolynomialNodeOverlap with the
original y-principal open. Both maps commute with the original inclusion
in the initial affine scheme over an arbitrary nilpotent coefficient ideal.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "F" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "i" => polynomialNodeOverlapInclusion W s
local notation "j" => polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3

/-- The original y-principal-open inclusion, retaining all original affine coordinates. -/
def polynomialInitialInfinityInclusion : Spec (.of Y) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A Y))

instance polynomialInitialInfinityInclusion_isOpenImmersion :
    IsOpenImmersion (polynomialInitialInfinityInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (y W s b3 b4 b6)

/-- The full node intersection has exactly the original infinity boundary as its image. -/
theorem polynomialNodeOverlap_infinity_range :
    Set.range (i ≫ F) = Set.range (polynomialInitialInfinityInclusion W s b3 b4 b6) := by
  change Set.range (i ≫ F) = Set.range (PrimeSpectrum.comap (algebraMap A Y))
  rw [PrimeSpectrum.localization_away_comap_range _ (y W s b3 b4 b6),
    polynomialInitialY_node_intersection W s b3 b4 b6 r hr I hI hrI h3]
  have pb := polynomialNodeOverlap_isPullback W s b3 b4 b6 r hr I hI hrI h3
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨i x, rfl⟩, ⟨j x, congrArg (fun f ↦ f x) pb.w.symm⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨w, hw⟩⟩
    obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback pb x w (hx.trans hw.symm)
    exact ⟨v, (congrArg F hv).trans hx⟩

/-- The actual full standard overlap is the original infinity-boundary scheme. -/
def polynomialNodeOverlapInfinityIso :
    Spec (.of (PolynomialNodeOverlap W s)) ≅ Spec (.of Y) :=
  IsOpenImmersion.isoOfRangeEq (i ≫ F) (polynomialInitialInfinityInclusion W s b3 b4 b6)
    (polynomialNodeOverlap_infinity_range W s b3 b4 b6 r hr I hI hrI h3)

/-- The forward comparison retains the original inclusion in the full initial affine chart. -/
@[reassoc] theorem polynomialNodeOverlapInfinityIso_hom_inclusion :
    (polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3).hom ≫
      polynomialInitialInfinityInclusion W s b3 b4 b6 = i ≫ F :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse comparison also retains the original full affine inclusion. -/
@[reassoc] theorem polynomialNodeOverlapInfinityIso_inv_inclusion :
    (polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3).inv ≫ i ≫ F =
      polynomialInitialInfinityInclusion W s b3 b4 b6 :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

end FLT.Mazur.WeierstrassModificationX
