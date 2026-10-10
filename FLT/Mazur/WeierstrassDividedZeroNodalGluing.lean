/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalZeroBoundary
public import FLT.Mazur.WeierstrassDividedInitialZeroInfinity
public import FLT.Mazur.WeierstrassCoefficientChartPreimage

/-!
# Full nodal affine gluing at zero start and stage

The full terminal nodal affine chart and retained infinity chart cover the
actual residue model. Their entire intersection is the original nodal Y-open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
  (j : ℕ) (hj : j ≤ n) (hzero : start + j = 0)
open WeierstrassIntegralChart WeierstrassDilatation
local notation "K" => ResidueField R
local notation "N" => splitNodalEquation (residueTangentUnit D)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "l" => finiteInfinityTensorChart hπ data K j hj
local notation "r" => terminalZeroNodalChart hπ data D hdepth j hj hzero
local notation "e" => terminalZeroBoundaryToInfinity D hdepth

/-- The entire preimage of infinity in the terminal chart is exactly its nodal Y-open. -/
theorem terminalZeroBoundary_preimage :
    r ⁻¹' Set.range l = Set.range (overlapInclusion N 2 1) := by
  have hi : Set.range (finiteInfinityChart hπ data j hj) =
      finiteGlobalContraction hπ data j hj ⁻¹' Set.range (integralCurveChart W 1) := by
    have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (finiteInfinity_isPullback hπ data j hj) ⊤
    simpa using congrArg SetLike.coe h
  rw [finiteInfinityTensorChart_range, hi]
  change (r ≫ pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
    finiteGlobalContraction hπ data j hj) ⁻¹' Set.range (integralCurveChart W 1) = _
  rw [terminalZeroNodalChart_toCurve]
  change (Spec.map (CommRingCat.ofHom (zeroResidueOriginalMap D hdepth).toRingHom)) ⁻¹'
    (integralCurveChart W 2 ⁻¹' Set.range (integralCurveChart W 1)) = _
  rw [show integralCurveChart W 2 ⁻¹' Set.range (integralCurveChart W 1) =
      (↑(PrimeSpectrum.basicOpen (coord W 2 1)) : Set (PrimeSpectrum _)) from
        by simpa only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange] using
          congrArg SetLike.coe (integralCurveChart_preimage_chart W 2 1)]
  rw [show (Spec.map (CommRingCat.ofHom (zeroResidueOriginalMap D hdepth).toRingHom)) ⁻¹'
      (↑(PrimeSpectrum.basicOpen (coord W 2 1)) : Set (PrimeSpectrum _)) =
        (↑(PrimeSpectrum.basicOpen (coord N 2 1)) : Set (PrimeSpectrum _)) from by
    change (Spec.map _ ⁻¹ᵁ PrimeSpectrum.basicOpen _).carrier = _
    rw [SpecMap_preimage_basicOpen]
    exact congrArg (fun f : WeierstrassIntegralChart.Coordinate N 2 =>
      (PrimeSpectrum.basicOpen f).carrier) (zeroResidueOriginalMap_coord D hdepth 1)]
  exact (PrincipalAffineRefinement.range_inclusion (coord N 2 1)).symm

/-- The nodal boundary is the full cartesian intersection in the actual global residue model. -/
theorem terminalZeroBoundary_isPullback : IsPullback e (overlapInclusion N 2 1) l r := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (terminalZeroBoundary_overlap hπ data D hdepth j hj hzero).symm
  exact TopologicalSpace.Opens.ext (terminalZeroBoundary_preimage hπ data D hdepth j hj hzero)

/-- At start+stage zero, the infinity and nodal affine charts cover every point. -/
theorem zeroNodal_charts_cover (z : finiteGlobalTensorModel hπ data K j hj) :
    (∃ x, l x = z) ∨ ∃ x, r x = z := by
  have hs : start = 0 := by omega
  have hj0 : j = 0 := by omega
  subst j
  obtain ⟨i, x, hi, hx⟩ := zeroStartAtlas_cover_without_initial
    hπ data D hdepth hs 0 hj z
  by_cases hi0 : i.val = 0
  · have he : i = 0 := Fin.ext hi0
    subst i
    exact Or.inl ⟨x, hx⟩
  · have he : i = 1 := Fin.ext (show i.val = 1 by omega)
    subst i
    right
    have hsurj := (terminalZeroNodalAtlasIso hπ data D hdepth 0 hj hzero).hom.homeomorph.surjective
    obtain ⟨y, hy⟩ := hsurj x
    change (terminalZeroNodalAtlasIso hπ data D hdepth 0 hj hzero).hom y = x at hy
    refine ⟨y, ?_⟩
    rw [← terminalZeroNodalAtlasIso_map]
    change globalTensorAtlasMap hπ data K 0 hj 1
      ((terminalZeroNodalAtlasIso hπ data D hdepth 0 hj hzero).hom y) = z
    rw [hy]
    exact hx

/-- Gluing the whole nodal Y-open recovers the entire original projective residue model. -/
def zeroNodalGluingIso : pushout e (overlapInclusion N 2 1) ≅
    finiteGlobalTensorModel hπ data K j hj :=
  SchemeOpenPushout.coverIso _ _ _ _ (terminalZeroBoundary_isPullback hπ data D hdepth j hj hzero)
    (zeroNodal_charts_cover hπ data D hdepth j hj hzero)

/-- The full gluing retains the original infinity tensor inclusion. -/
@[reassoc] theorem zeroNodalGluingIso_infinity :
    pushout.inl e (overlapInclusion N 2 1) ≫
      (zeroNodalGluingIso hπ data D hdepth j hj hzero).hom = l :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The full gluing retains the exact terminal nodal affine inclusion. -/
@[reassoc] theorem zeroNodalGluingIso_terminal :
    pushout.inr e (overlapInclusion N 2 1) ≫
      (zeroNodalGluingIso hπ data D hdepth j hj hzero).hom = r :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
