/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateBranchOutput
public import FLT.Mazur.WeierstrassDividedShearBranchOverlapCoverage

/-!
# Intermediate outputs on actual original branch neighborhoods

The original and normalized strict branches have a constructed common open.
Its refined output preserves the coefficient point and the entire original
tangent sum. Every original nodal strict-branch point lifts to this source;
smoothness of the intermediate output is a separate remaining condition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalIntermediateBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "O" => DividedShearBranchOverlap W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c
local notation "e" =>
  dividedShearBranchOverlapNormalized W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c
local notation "f" =>
  dividedShearBranchOverlapOriginal W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "old" => dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a c *
  dividedTangentBranchFactor W (π ^ k) (d).b3 (d).b4 (d).b6 a

/-- The refined normalized output on a constructed domain of the original tangent formula. -/
def nodalIntermediateBranchCommonOutput :
    Spec (.of O) ⟶ finiteGlobalModel hπ (start := 0) data (k + r) hj :=
  Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
    nodalIntermediateBranchOutput D hdepth hrk hrm data hj d a c

/-- The common-domain output retains the original coefficient structure. -/
@[reassoc] theorem nodalIntermediateBranchCommonOutput_structure :
    nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [nodalIntermediateBranchCommonOutput, Category.assoc, nodalIntermediateBranchOutput_structure,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (e).comp_algebraMap

/-- The entire actual output contracts to unsheared tangent addition on this common source. -/
@[reassoc] theorem nodalIntermediateBranchCommonOutput_contraction :
    nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d a c ≫
      finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 := by
  rw [nodalIntermediateBranchCommonOutput, Category.assoc]
  apply nodalIntermediateBranchOutput_original_contraction
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext z
  exact (dividedShearBranchOverlapNormalized_source W (π ^ k)
      (d).b3 (d).b4 (d).b6 σ a c z).trans
    (dividedShearBranchOverlapOriginal_source W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c z).symm

omit [IsDomain R] [IsBezout R] [Module.Flat R S] in
/-- Every original nodal strict-branch point lifts to the constructed intermediate source. -/
theorem nodalIntermediateBranchCommonOutput_source_covers
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hb : p ∈ PrimeSpectrum.basicOpen old) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal :=
  nodalShearBranchOverlap_covers W (π ^ k) d.b3 d.b4 d.b6 a c D k p hp hb

end FLT.Mazur.WeierstrassDividedDepth
