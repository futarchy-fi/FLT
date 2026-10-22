/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowPositivePairCover

/-!
# Smooth outputs cover negative equal-depth shallow pairs

Apply the complete positive three-source construction to the negated inputs,
then negate each actual smooth output. The same sources cover the entire
negative punctured pair locus, including the diagonal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsNoetherianRing R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hlo : 2 * k < m) (hhi : m < 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "na" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 a
local notation "nc" => branchNegativeInput W (π ^ k) d.b3 d.b4 d.b6 c
local notation "base" => finiteGlobalStructure hπ data (m - 2 * k) hj
local notation "U" => (base).smoothLocus
local notation "src" => nodalShallowPositivePairSource D hlo hhi data hj d na nc
local notation "inc" => nodalShallowPositivePairInclusion D hlo hhi data hj d na nc

/-- Negate each constructed smooth output on the complete negative pair cover. -/
def nodalShallowNegativePairOutput (i : Option Bool) : src i ⟶ (U).toScheme :=
  nodalShallowPositivePairOutput D hlo hhi data hj d na nc i ≫
    finiteResolvedNegation hπ data (m - 2 * k) hj

/-- The complete negative pair output preserves the original coefficient point. -/
@[reassoc] theorem nodalShallowNegativePairOutput_structure (i : Option Bool) :
    nodalShallowNegativePairOutput D hlo hhi data hj d a c i ≫ (U).ι ≫ base =
      inc i ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [nodalShallowNegativePairOutput, Category.assoc, finiteResolvedNegation_structure,
    nodalShallowPositivePairOutput_structure]

/-- All negative punctured pairs have an actual local smooth output, including the diagonal. -/
theorem nodalShallowNegativePair_covers (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (hx : a (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hu : c (x W (π ^ k) d.b3 d.b4 d.b6) ∉ p.asIdeal)
    (hy : dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a ∈ p.asIdeal)
    (hv : dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 c ∈ p.asIdeal) :
    ∃ i : Option Bool, p ∈ Set.range (inc i) := by
  apply nodalShallowPositivePair_covers D hlo hhi data hj d na nc p hp
  · simpa only [branchNegativeInput_x] using hx
  · simpa only [branchNegativeInput_x] using hu
  · have he : na (y W (π ^ k) d.b3 d.b4 d.b6) =
        -dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 a := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hy
  · have he : nc (y W (π ^ k) d.b3 d.b4 d.b6) =
        -dividedTangentBranchFactor W (π ^ k) d.b3 d.b4 d.b6 c := by
      rw [branchNegativeInput_y, dividedTangentBranchFactor]
      ring
    rw [he]
    exact p.asIdeal.neg_mem hv

end FLT.Mazur.WeierstrassDividedDepth
