/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowBranchCommonOutput
public import FLT.Mazur.WeierstrassDividedNodalShallowBranchOutput

/-!
# Smooth outputs cover the original shallow nodal branch

Every original strict-branch point on the closed fiber lifts to the
constructed common source, and its actual shallow output in the
original finite model lies in the full relative smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalShallowBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "O" => DividedShearBranchOverlap W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c
local notation "e" =>
  dividedShearBranchOverlapNormalized W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c
local notation "f" =>
  dividedShearBranchOverlapOriginal W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj
local notation "old" => dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a c *
  dividedTangentBranchFactor W (π ^ k) (d).b3 (d).b4 (d).b6 a

variable [IsNoetherianRing R]

/-- Every nodal point of the original common branch source has a smooth actual output. -/
theorem nodalShallowBranchCommonOutput_smooth
    (hlo : 2 * k < m) (hhi : m < 3 * k)
    (p : PrimeSpectrum O) (hp : algebraMap R O π ∈ p.asIdeal) :
    nodalShallowBranchCommonOutput D hdepth hm data hj d a c p ∈
      (base).smoothLocus := by
  rw [nodalShallowBranchCommonOutput, Scheme.Hom.comp_apply]
  apply nodalShallowBranchOutput_smooth D hdepth hm data hj d a c hlo hhi
  change (e) (algebraMap R _ π) ∈ p.asIdeal
  simpa only [AlgHom.commutes] using hp

/-- The original strict nodal branch is covered by actual compatible smooth shallow outputs. -/
theorem nodalShallowBranchCommonOutput_covers
    (hlo : 2 * k < m) (hhi : m < 3 * k)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hb : p ∈ PrimeSpectrum.basicOpen old) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        nodalShallowBranchCommonOutput D hdepth hm data hj d a c q ∈
          (base).smoothLocus := by
  obtain ⟨q, hq, hqπ⟩ := nodalShallowBranchCommonOutput_source_covers D d a c p hp hb
  exact ⟨q, hq, hqπ,
    nodalShallowBranchCommonOutput_smooth D hdepth hm data hj d a c hlo hhi q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
