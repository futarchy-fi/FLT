/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedNodalIntermediateBranchCoverage
public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegation

/-!
# Smooth complementary outputs at intermediate nodal depth

Negate the actual divided inputs, construct their normalized smooth branch
output, and negate it in the same entire finite model. This constructs an
output over every point of the complementary original branch domain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalIntermediateBranchCommonOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ}
  (D : SplitNodeDepth W π m) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W (π ^ k) (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W (π ^ k) (d).b3 (d).b4 (d).b6 c
local notation "O" => DividedShearBranchOverlap W (π ^ k) (d).b3 (d).b4 (d).b6 σ a' c'
local notation "f" =>
  dividedShearBranchOverlapOriginal W (π ^ k) (d).b3 (d).b4 (d).b6 σ a' c'
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "N" => finiteGlobalNegationIso hπ (start := 0) data (k + r) hj

/-- The complementary branch has an actual output in the same original finite model. -/
def nodalIntermediateNegativeBranchOutput :
    Spec (.of O) ⟶ finiteGlobalModel hπ (start := 0) data (k + r) hj :=
  nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d a' c' ≫ (N).hom

/-- The complementary output has the unchanged original coefficient structure. -/
@[reassoc] theorem nodalIntermediateNegativeBranchOutput_structure :
    nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [nodalIntermediateNegativeBranchOutput, Category.assoc]
  change nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d a' c' ≫
    finiteGlobalNegation hπ (start := 0) data (k + r) hj ≫ base = _
  rw [finiteGlobalNegation_structure, nodalIntermediateBranchCommonOutput_structure]

/-- Its original cubic contraction is the negative of the constructed negative-input sum. -/
@[reassoc] theorem nodalIntermediateNegativeBranchOutput_contraction :
    nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c ≫
      finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) (d).b3 (d).b4 (d).b6 a' c'
          (d).factor3 (d).factor4 (d).factor6 ≫ integralCurveNegation W := by
  rw [nodalIntermediateNegativeBranchOutput, Category.assoc]
  change nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d a' c' ≫
    finiteGlobalNegation hπ (start := 0) data (k + r) hj ≫ _ = _
  rw [finiteGlobalNegation_contraction, nodalIntermediateBranchCommonOutput_contraction_assoc]

variable [IsNoetherianRing R]

/-- Every complementary source point over the closed fiber has smooth output. -/
theorem nodalIntermediateNegativeBranchOutput_smooth
    (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum O)
    (hp : algebraMap R O π ∈ p.asIdeal) :
    nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c p ∈
      (base).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (N).hom base
  have he : (N).hom ≫ base = base := finiteGlobalNegation_structure hπ (start := 0) data (k + r) hj
  simp only [he] at h
  rw [nodalIntermediateNegativeBranchOutput, Scheme.Hom.comp_apply]
  apply h.ge
  exact nodalIntermediateBranchCommonOutput_smooth D hdepth hrk hrm data hj d a' c' hm hr p hp

/-- The complementary reversed-tangent branch is covered by actual smooth outputs. -/
theorem nodalIntermediateNegativeBranchOutput_covers
    (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hb : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 c a *
        a (y W (π ^ k) (d).b3 (d).b4 (d).b6))) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        nodalIntermediateNegativeBranchOutput D hdepth hrk hrm data hj d a c q ∈
          (base).smoothLocus := by
  have hb' : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a' c' *
        dividedTangentBranchFactor W (π ^ k) (d).b3 (d).b4 (d).b6 a') := by
    simpa only [branchNegativeInput_branchProduct] using hb
  obtain ⟨q, hq, hqπ, _⟩ := nodalIntermediateBranchCommonOutput_covers
    D hdepth hrk hrm data hj d a' c' hm hr p hp hb'
  exact ⟨q, hq, hqπ,
    nodalIntermediateNegativeBranchOutput_smooth D hdepth hrk hrm data hj d a c hm hr q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
