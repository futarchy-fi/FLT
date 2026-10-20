/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedNodalShallowBranchCoverage
public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegation

/-!
# Smooth complementary outputs at shallow nodal depth

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
  nodalShallowBranchCommonOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m) (hdepth : 2 * k ≤ m)
  (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W (π ^ k) (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W (π ^ k) (d).b3 (d).b4 (d).b6 c
local notation "O" => DividedShearBranchOverlap W (π ^ k) (d).b3 (d).b4 (d).b6 σ a' c'
local notation "f" =>
  dividedShearBranchOverlapOriginal W (π ^ k) (d).b3 (d).b4 (d).b6 σ a' c'
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "N" => finiteGlobalNegationIso hπ (start := 0) data (m - 2 * k) hj

/-- The complementary branch has an actual output in the same original finite model. -/
def nodalShallowNegativeBranchOutput :
    Spec (.of O) ⟶ finiteGlobalModel hπ (start := 0) data (m - 2 * k) hj :=
  nodalShallowBranchCommonOutput D hdepth hm data hj d a' c' ≫ (N).hom

/-- The complementary output has the unchanged original coefficient structure. -/
@[reassoc] theorem nodalShallowNegativeBranchOutput_structure :
    nodalShallowNegativeBranchOutput D hdepth hm data hj d a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [nodalShallowNegativeBranchOutput, Category.assoc]
  change nodalShallowBranchCommonOutput D hdepth hm data hj d a' c' ≫
    finiteGlobalNegation hπ (start := 0) data (m - 2 * k) hj ≫ base = _
  rw [finiteGlobalNegation_structure, nodalShallowBranchCommonOutput_structure]

/-- Its original cubic contraction is the negative of the constructed negative-input sum. -/
@[reassoc] theorem nodalShallowNegativeBranchOutput_contraction :
    nodalShallowNegativeBranchOutput D hdepth hm data hj d a c ≫
      finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) (d).b3 (d).b4 (d).b6 a' c'
          (d).factor3 (d).factor4 (d).factor6 ≫ integralCurveNegation W := by
  rw [nodalShallowNegativeBranchOutput, Category.assoc]
  change nodalShallowBranchCommonOutput D hdepth hm data hj d a' c' ≫
    finiteGlobalNegation hπ (start := 0) data (m - 2 * k) hj ≫ _ = _
  rw [finiteGlobalNegation_contraction, nodalShallowBranchCommonOutput_contraction_assoc]

variable [IsNoetherianRing R]

/-- Every complementary source point over the closed fiber has smooth output. -/
theorem nodalShallowNegativeBranchOutput_smooth
    (hlo : 2 * k < m) (hhi : m < 3 * k) (p : PrimeSpectrum O)
    (hp : algebraMap R O π ∈ p.asIdeal) :
    nodalShallowNegativeBranchOutput D hdepth hm data hj d a c p ∈
      (base).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (N).hom base
  have he : (N).hom ≫ base = base :=
    finiteGlobalNegation_structure hπ (start := 0) data (m - 2 * k) hj
  simp only [he] at h
  rw [nodalShallowNegativeBranchOutput, Scheme.Hom.comp_apply]
  apply h.ge
  exact nodalShallowBranchCommonOutput_smooth D hdepth hm data hj d a' c' hlo hhi p hp

/-- The complementary reversed-tangent branch is covered by actual smooth outputs. -/
theorem nodalShallowNegativeBranchOutput_covers
    (hlo : 2 * k < m) (hhi : m < 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hb : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 c a *
        a (y W (π ^ k) (d).b3 (d).b4 (d).b6))) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        nodalShallowNegativeBranchOutput D hdepth hm data hj d a c q ∈
          (base).smoothLocus := by
  have hb' : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a' c' *
        dividedTangentBranchFactor W (π ^ k) (d).b3 (d).b4 (d).b6 a') := by
    simpa only [branchNegativeInput_branchProduct] using hb
  obtain ⟨q, hq, hqπ, _⟩ := nodalShallowBranchCommonOutput_covers
    D hdepth hm data hj d a' c' hlo hhi p hp hb'
  exact ⟨q, hq, hqπ,
    nodalShallowNegativeBranchOutput_smooth D hdepth hm data hj d a c hlo hhi q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
