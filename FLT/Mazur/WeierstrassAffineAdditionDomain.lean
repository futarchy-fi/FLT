/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionSchemeCover
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# The regular affine addition domain in arbitrary reduction

The union of the four explicit addition charts is an open subscheme of the
actual affine input product. Every pair whose first residue-field point is
nonsingular lies in this domain, without assuming a unit discriminant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The union of the actual domains of the four regular affine addition formulas. -/
def affineAdditionDomain : (Spec (.of (AffineProduct W))).Opens :=
  ⨆ i, (additionChartInclusion W i).opensRange

/-- Membership means that one of the original addition charts contains the point. -/
theorem mem_affineAdditionDomain (p : PrimeSpectrum (AffineProduct W)) :
    p ∈ affineAdditionDomain W ↔ ∃ i, p ∈ Set.range (additionChartInclusion W i) := by
  simp only [affineAdditionDomain, TopologicalSpace.Opens.mem_iSup]
  rfl

/-- A nonsingular first input suffices for coverage by the actual addition chart spectra. -/
theorem additionChartInclusion_covers_nonsingular (p : PrimeSpectrum (AffineProduct W))
    (hs : (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
      (algebraMap _ p.asIdeal.ResidueField (productX₁ W))
      (algebraMap _ p.asIdeal.ResidueField (productY₁ W))) :
    ∃ i, p ∈ Set.range (PrimeSpectrum.comap (additionChartRestriction W i)) := by
  let f : AffineProduct W →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (AffineProduct W) p.asIdeal.ResidueField
  rcases addition_denominators_cover W f hs with hs | ht | hs | ht
  · refine ⟨.secant, mem_range_comap_of_residue_lift p _
      (ratioLift W f (secantDenominator W) hs).toRingHom ?_⟩
    exact ratioLift_restriction W f (secantDenominator W) hs
  · refine ⟨.tangent, mem_range_comap_of_residue_lift p _
      (ratioLift W f (tangentDenominator W) ht).toRingHom ?_⟩
    exact ratioLift_restriction W f (tangentDenominator W) ht
  · refine ⟨.verticalSecant, mem_range_comap_of_residue_lift p _
      (reciprocalRatioLift W f (verticalSecantDenominator W)
        (secantDenominator W) hs.1 hs.2).toRingHom ?_⟩
    exact reciprocalRatioLift_restriction W f _ _ hs.1 hs.2
  · refine ⟨.verticalTangent, mem_range_comap_of_residue_lift p _
      (reciprocalRatioLift W f (tangentNumerator W)
        (tangentDenominator W) ht.1 ht.2).toRingHom ?_⟩
    exact reciprocalRatioLift_restriction W f _ _ ht.1 ht.2

/-- Every residue-field nonsingular first input belongs to the regular addition domain. -/
theorem mem_affineAdditionDomain_of_nonsingular (p : PrimeSpectrum (AffineProduct W))
    (hs : (W.map (algebraMap R p.asIdeal.ResidueField)).toAffine.Nonsingular
      (algebraMap _ p.asIdeal.ResidueField (productX₁ W))
      (algebraMap _ p.asIdeal.ResidueField (productY₁ W))) :
    p ∈ affineAdditionDomain W :=
  (mem_affineAdditionDomain W p).mpr (additionChartInclusion_covers_nonsingular W p hs)

/-- The original addition chart regarded as an open chart of the regular addition domain. -/
def additionChartToDomain (i : AdditionChartIndex) :
    Spec (additionChartRing W i) ⟶ (affineAdditionDomain W).toScheme :=
  IsOpenImmersion.lift (affineAdditionDomain W).ι (additionChartInclusion W i) (by
    rw [Scheme.Opens.range_ι]
    intro p hp
    exact (mem_affineAdditionDomain W p).mpr ⟨i, hp⟩)

/-- The lifted chart has exactly its original inclusion in the input product. -/
@[reassoc (attr := simp)] theorem additionChartToDomain_inclusion (i : AdditionChartIndex) :
    additionChartToDomain W i ≫ (affineAdditionDomain W).ι = additionChartInclusion W i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original charts remain open immersions into their union. -/
instance additionChartToDomain_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (additionChartToDomain W i) :=
  inferInstanceAs (IsOpenImmersion (IsOpenImmersion.lift _ _ _))

/-- The four regular addition charts cover their union, in every reduction type. -/
def affineAdditionDomainCover : (affineAdditionDomain W).toScheme.OpenCover where
  I₀ := AdditionChartIndex
  X i := Spec (additionChartRing W i)
  f := additionChartToDomain W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro p
    obtain ⟨i, x, hx⟩ := (mem_affineAdditionDomain W p.val).mp p.property
    refine ⟨i, x, ?_⟩
    apply (affineAdditionDomain W).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f x) (additionChartToDomain_inclusion W i)).trans hx

/-- Good reduction recovers the entire affine input product as this domain. -/
theorem affineAdditionDomain_eq_top (hΔ : IsUnit W.Δ) : affineAdditionDomain W = ⊤ := by
  apply top_unique
  intro p _
  exact (mem_affineAdditionDomain W p).mpr (additionChartInclusion_covers W hΔ p)

end FLT.Mazur.WeierstrassIntegralChart
