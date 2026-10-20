/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalFirstBranchOutput
public import FLT.Mazur.WeierstrassDividedShearBranchOverlapCoverage

/-!
# Common original branch outputs at every node depth at least three input depths

The actual common branch source preserves the original tangent formula
and coefficient map. Its finite-model output is constructed from the node
depth inequality. At exact triple depth it covers every original strict
branch point by a smooth output; deeper nodes retain their actual first
output for subsequent refinement.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalFirstBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * (start + k) ≤ m)
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "r" => nodalSecondShear D (start + k)
local notation "O" => DividedShearBranchOverlap W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a c
local notation "e" =>
  dividedShearBranchOverlapNormalized W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a c
local notation "f" =>
  dividedShearBranchOverlapOriginal W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "old" => dividedTangentDenominator W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c *
  dividedTangentBranchFactor W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a

/-- The smooth normalized output on a constructed domain of the original tangent formula. -/
def nodalFirstBranchCommonOutput : Spec (.of O) ⟶ finiteGlobalModel hπ data k hk :=
  Spec.map (CommRingCat.ofHom (e).toRingHom) ≫ nodalFirstBranchOutput D hdepth data hk a c

/-- The common-domain output retains the original coefficient structure. -/
@[reassoc] theorem nodalFirstBranchCommonOutput_structure :
    nodalFirstBranchCommonOutput D hdepth data hk a c ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) := by
  rw [nodalFirstBranchCommonOutput, Category.assoc, nodalFirstBranchOutput_structure,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (e).comp_algebraMap

/-- The entire actual output contracts to unsheared tangent addition on this common source. -/
@[reassoc] theorem nodalFirstBranchCommonOutput_contraction :
    nodalFirstBranchCommonOutput D hdepth data hk a c ≫ finiteGlobalContraction hπ data k hk =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫
        dividedTangentToCurve W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c
          (d).factor3 (d).factor4 (d).factor6 := by
  rw [nodalFirstBranchCommonOutput, Category.assoc]
  apply nodalFirstBranchOutput_original_contraction
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext z
  exact (dividedShearBranchOverlapNormalized_source W (π ^ (start + k))
      (d).b3 (d).b4 (d).b6 r a c z).trans
    (dividedShearBranchOverlapOriginal_source W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 r a c z).symm

variable [IsNoetherianRing R]

/-- Every special-fiber point of the common source has a smooth actual output. -/
theorem nodalFirstBranchCommonOutput_smooth (hterminal : m = 3 * (start + k))
    (p : PrimeSpectrum O)
    (hp : algebraMap R O π ∈ p.asIdeal) :
    nodalFirstBranchCommonOutput D hdepth data hk a c p ∈ (base).smoothLocus := by
  rw [nodalFirstBranchCommonOutput, Scheme.Hom.comp_apply]
  apply nodalFirstBranchOutput_smooth D hdepth data hk a c hterminal
  change (e) (algebraMap R _ π) ∈ p.asIdeal
  simpa only [AlgHom.commutes] using hp

/-- Every original branch special-fiber point lifts to this compatible smooth output. -/
theorem nodalFirstBranchCommonOutput_covers (hterminal : m = 3 * (start + k))
    (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hb : p ∈ PrimeSpectrum.basicOpen old) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        nodalFirstBranchCommonOutput D hdepth data hk a c q ∈ (base).smoothLocus := by
  obtain ⟨q, hq, hqπ⟩ := nodalShearBranchOverlap_covers
    W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c D (start + k) p hp hb
  exact ⟨q, hq, hqπ, nodalFirstBranchCommonOutput_smooth D hdepth data hk a c hterminal q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
