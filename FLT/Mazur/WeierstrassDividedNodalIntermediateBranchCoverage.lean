/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateBranchCommonOutput
public import FLT.Mazur.WeierstrassDividedNodalIntermediateBranchSmooth

/-!
# Smooth outputs cover the original intermediate nodal branch

Every original strict-branch point on the closed fiber lifts to the
constructed common source, and its actual intermediate output in the
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

variable [IsNoetherianRing R]

/-- Every nodal point of the original common branch source has a smooth actual output. -/
theorem nodalIntermediateBranchCommonOutput_smooth
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    (p : PrimeSpectrum O) (hp : algebraMap R O π ∈ p.asIdeal) :
    nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d a c p ∈
      (base).smoothLocus := by
  rw [nodalIntermediateBranchCommonOutput, Scheme.Hom.comp_apply]
  apply nodalIntermediateBranchOutput_smooth D hdepth hrk hrm data hj d a c hm hr
  change (e) (algebraMap R _ π) ∈ p.asIdeal
  simpa only [AlgHom.commutes] using hp

/-- The original strict nodal branch is covered by actual compatible smooth intermediate outputs. -/
theorem nodalIntermediateBranchCommonOutput_covers
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    (p : PrimeSpectrum S) (hp : algebraMap R S π ∈ p.asIdeal)
    (hb : p ∈ PrimeSpectrum.basicOpen old) :
    ∃ q : PrimeSpectrum O, PrimeSpectrum.comap (algebraMap S O) q = p ∧
      algebraMap R O π ∈ q.asIdeal ∧
        nodalIntermediateBranchCommonOutput D hdepth hrk hrm data hj d a c q ∈
          (base).smoothLocus := by
  obtain ⟨q, hq, hqπ⟩ := nodalIntermediateBranchCommonOutput_source_covers D d a c p hp hb
  exact ⟨q, hq, hqπ,
    nodalIntermediateBranchCommonOutput_smooth D hdepth hrk hrm data hj d a c hm hr q hqπ⟩

end FLT.Mazur.WeierstrassDividedDepth
