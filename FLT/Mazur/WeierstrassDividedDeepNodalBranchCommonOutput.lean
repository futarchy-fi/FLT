/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepNormalizedBranchContraction
public import FLT.Mazur.WeierstrassDividedShearBranchOverlapCoverage

/-!
# Smooth original branch outputs with the original tangent contraction

The constructed common source covers every original strict-branch
special-fiber point. Its actual output in the original finite model is
smooth there for m > 4*k with k > 0, and its contraction is the original
unsheared tangent formula on the whole common source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  deepNodalBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "r" => nodalSecondShear D k
local notation "O" => DividedShearBranchOverlap W (π ^ k) d.b3 d.b4 d.b6 r a c
local notation "e" => dividedShearBranchOverlapNormalized W (π ^ k) d.b3 d.b4 d.b6 r a c
local notation "f" => dividedShearBranchOverlapOriginal W (π ^ k) d.b3 d.b4 d.b6 r a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data (k + k) hj
local notation "old" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c *
  dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a

/-- The smooth normalized output on a constructed domain of the original tangent formula. -/
def deepNodalBranchCommonOutput : Spec (.of O) ⟶ finiteGlobalModel hπ data (k + k) hj :=
  Spec.map (CommRingCat.ofHom (e).toRingHom) ≫ deepNodalBranchOutput D data hj d a c

/-- The common-domain output retains the original coefficient structure. -/
@[reassoc] theorem deepNodalBranchCommonOutput_structure :
    deepNodalBranchCommonOutput D data hj d a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [deepNodalBranchCommonOutput, Category.assoc, deepNodalBranchOutput_structure, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (e).comp_algebraMap

/-- The entire actual output contracts to unsheared tangent addition on this common source. -/
@[reassoc] theorem deepNodalBranchCommonOutput_contraction :
    deepNodalBranchCommonOutput D data hj d a c ≫ finiteGlobalContraction hπ data (k + k) hj =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
          d.factor3 d.factor4 d.factor6 := by
  rw [deepNodalBranchCommonOutput, Category.assoc]
  apply deepNodalBranchOutput_original_contraction
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext z
  exact (dividedShearBranchOverlapNormalized_source W (π ^ k) d.b3 d.b4 d.b6 r a c z).trans
    (dividedShearBranchOverlapOriginal_source W (π ^ k) d.b3 d.b4 d.b6 r a c z).symm

variable [IsNoetherianRing R]

/-- Every special-fiber point of the common source has a smooth actual output. -/
theorem deepNodalBranchCommonOutput_smooth (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum O)
    (hp : algebraMap R O π ∈ p.asIdeal) :
    deepNodalBranchCommonOutput D data hj d a c p ∈ (base).smoothLocus := by
  rw [deepNodalBranchCommonOutput, Scheme.Hom.comp_apply]
  apply deepNodalBranchOutput_smooth D data hj d a c hk hm
  change (e) (algebraMap R _ π) ∈ p.asIdeal
  simpa only [AlgHom.commutes] using hp

/-- Every original branch special-fiber point lifts to this compatible smooth output. -/
theorem deepNodalBranchCommonOutput_covers (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hb : p ∈ PrimeSpectrum.basicOpen old) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        deepNodalBranchCommonOutput D data hj d a c q ∈ (base).smoothLocus := by
  obtain ⟨q, hq, hqπ⟩ := nodalShearBranchOverlap_covers
    W (π ^ k) d.b3 d.b4 d.b6 a c D k p hp hb
  exact ⟨q, hq, hqπ, deepNodalBranchCommonOutput_smooth D data hj d a c hk hm q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
