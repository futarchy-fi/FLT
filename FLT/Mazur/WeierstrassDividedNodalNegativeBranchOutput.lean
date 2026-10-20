/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedNodalBranchCommonOutput
public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegation

/-!
# Smooth complementary strict-branch outputs in the original finite model

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
  nodalBranchCommonOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))
  (d : Data W π k)
  (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "r" => nodalSecondShear D k
local notation "a'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "c'" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 c
local notation "O" => DividedShearBranchOverlap W (π ^ k) d.b3 d.b4 d.b6 r a' c'
local notation "f" => dividedShearBranchOverlapOriginal W (π ^ k) d.b3 d.b4 d.b6 r a' c'
local notation "data" => splitNodeDoubledFamily D
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) le_rfl
local notation "N" => finiteGlobalNegationIso hπ data (k + k) le_rfl

/-- The complementary branch has an actual output in the same original finite model. -/
def nodalNegativeBranchOutput : Spec (.of O) ⟶ finiteGlobalModel hπ data (k + k) le_rfl :=
  nodalBranchCommonOutput D d a' c' ≫ (N).hom

/-- The complementary output has the unchanged original coefficient structure. -/
@[reassoc] theorem nodalNegativeBranchOutput_structure :
    nodalNegativeBranchOutput D d a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [nodalNegativeBranchOutput, Category.assoc]
  change nodalBranchCommonOutput D d a' c' ≫
    finiteGlobalNegation hπ data (k + k) le_rfl ≫ base = _
  rw [finiteGlobalNegation_structure, nodalBranchCommonOutput_structure]

/-- Its original cubic contraction is the negative of the constructed negative-input sum. -/
@[reassoc] theorem nodalNegativeBranchOutput_contraction :
    nodalNegativeBranchOutput D d a c ≫ finiteGlobalContraction hπ data (k + k) le_rfl =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a' c'
          d.factor3 d.factor4 d.factor6 ≫ integralCurveNegation W := by
  rw [nodalNegativeBranchOutput, Category.assoc]
  change nodalBranchCommonOutput D d a' c' ≫
    finiteGlobalNegation hπ data (k + k) le_rfl ≫ _ = _
  rw [finiteGlobalNegation_contraction, nodalBranchCommonOutput_contraction_assoc]

variable [IsNoetherianRing R]

/-- Every complementary source point over the closed fiber has smooth output. -/
theorem nodalNegativeBranchOutput_smooth (p : PrimeSpectrum O)
    (hp : algebraMap R O π ∈ p.asIdeal) :
    nodalNegativeBranchOutput D d a c p ∈ (base).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (N).hom base
  have he : (N).hom ≫ base = base := finiteGlobalNegation_structure hπ data (k + k) le_rfl
  simp only [he] at h
  rw [nodalNegativeBranchOutput, Scheme.Hom.comp_apply]
  apply h.ge
  exact nodalBranchCommonOutput_smooth D d a' c' p hp

/-- The complementary reversed-tangent branch is covered by actual smooth outputs. -/
theorem nodalNegativeBranchOutput_covers (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hb : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 c a *
        a (y W (π ^ k) d.b3 d.b4 d.b6))) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        nodalNegativeBranchOutput D d a c q ∈ (base).smoothLocus := by
  have hb' : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a' c' *
        dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a') := by
    simpa only [branchNegativeInput_branchProduct] using hb
  obtain ⟨q, hq, hqπ, _⟩ := nodalBranchCommonOutput_covers D d a' c' p hp hb'
  exact ⟨q, hq, hqπ, nodalNegativeBranchOutput_smooth D d a c q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
