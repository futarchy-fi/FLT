/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNegativeBranchSource
public import FLT.Mazur.WeierstrassDividedTripleBranchCommonOutput
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
  tripleBranchCommonOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : WeierstrassDilatation.Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "r" => nodalSecondShear D (start + k)
local notation "a'" => branchNegativeInput W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a
local notation "c'" => branchNegativeInput W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 c
local notation "O" => DividedShearBranchOverlap W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a' c'
local notation "f" =>
  dividedShearBranchOverlapOriginal W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a' c'
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "N" => finiteGlobalNegationIso hπ data k hk

/-- The complementary branch has an actual output in the same original finite model. -/
def tripleNegativeBranchOutput : Spec (.of O) ⟶ finiteGlobalModel hπ data k hk :=
  tripleBranchCommonOutput D data hk a' c' ≫ (N).hom

/-- The complementary output has the unchanged original coefficient structure. -/
@[reassoc] theorem tripleNegativeBranchOutput_structure :
    tripleNegativeBranchOutput D data hk a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [tripleNegativeBranchOutput, Category.assoc]
  change tripleBranchCommonOutput D data hk a' c' ≫
    finiteGlobalNegation hπ data k hk ≫ base = _
  rw [finiteGlobalNegation_structure, tripleBranchCommonOutput_structure]

/-- Its original cubic contraction is the negative of the constructed negative-input sum. -/
@[reassoc] theorem tripleNegativeBranchOutput_contraction :
    tripleNegativeBranchOutput D data hk a c ≫ finiteGlobalContraction hπ data k hk =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        dividedTangentToCurve W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a' c'
          (d).factor3 (d).factor4 (d).factor6 ≫ integralCurveNegation W := by
  rw [tripleNegativeBranchOutput, Category.assoc]
  change tripleBranchCommonOutput D data hk a' c' ≫
    finiteGlobalNegation hπ data k hk ≫ _ = _
  rw [finiteGlobalNegation_contraction, tripleBranchCommonOutput_contraction_assoc]

variable [IsNoetherianRing R]

/-- Every complementary source point over the closed fiber has smooth output. -/
theorem tripleNegativeBranchOutput_smooth (p : PrimeSpectrum O)
    (hp : algebraMap R O π ∈ p.asIdeal) :
    tripleNegativeBranchOutput D data hk a c p ∈ (base).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (N).hom base
  have he : (N).hom ≫ base = base := finiteGlobalNegation_structure hπ data k hk
  simp only [he] at h
  rw [tripleNegativeBranchOutput, Scheme.Hom.comp_apply]
  apply h.ge
  exact tripleBranchCommonOutput_smooth D data hk a' c' p hp

/-- The complementary reversed-tangent branch is covered by actual smooth outputs. -/
theorem tripleNegativeBranchOutput_covers (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hb : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 c a *
        a (y W (π ^ (start + k)) (d).b3 (d).b4 (d).b6))) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        tripleNegativeBranchOutput D data hk a c q ∈ (base).smoothLocus := by
  have hb' : p ∈ PrimeSpectrum.basicOpen
      (dividedTangentDenominator W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a' c' *
        dividedTangentBranchFactor W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a') := by
    simpa only [branchNegativeInput_branchProduct] using hb
  obtain ⟨q, hq, hqπ, _⟩ := tripleBranchCommonOutput_covers D data hk a' c' p hp hb'
  exact ⟨q, hq, hqπ, tripleNegativeBranchOutput_smooth D data hk a c q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
