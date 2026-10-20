/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateBranchOutput
public import FLT.Mazur.WeierstrassDividedFiniteNodalRefinedBranchTerminal

/-!
# Smooth intermediate outputs in the original unsheared model

The finite shear supplies normalization and preserves the relative smooth
locus. Thus the actual returned intermediate output is smooth above every
nodal branch point, without an original second-coefficient factor assumption.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "V" => rootShearCurve W σ
local notation "sd" => shearData d σ
local notation "a'" => branchShearInput W (π ^ k) (d).b3 (d).b4 (d).b6 σ a
local notation "c'" => branchShearInput W (π ^ k) (d).b3 (d).b4 (d).b6 σ c
local notation "B" => DividedTangentBranchRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "T" => DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c
local notation "T'" => DividedTangentRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "res" => dividedTangentBranchRestriction
  V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "hπ" => D.uniformizer_ne_zero

local notation "dat" => fun i => shearData (data i) σ
local notation "g" => finiteNodalRefinedBranchLift (nodalSecondShear_depth D k)
  hdepth hrk hrm dat hj sd (nodalSecondQuotient D k)
  (nodalSecondQuotient_factor D k) a' c'
local notation "iso" => shearFiniteGlobalIso hπ (start := 0) data σ (k + r) hj
local notation "cur" => WeierstrassIntegralChart.integralVariableChangeIso W V (⟨1, 0, σ, 0⟩)
  (by unfold rootShearCurve; rfl)

variable [IsNoetherianRing R]

/-- Returning the normalized intermediate output preserves smoothness on the whole nodal fiber. -/
theorem nodalIntermediateBranchOutput_smooth
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    nodalIntermediateBranchOutput D hdepth hrk hrm data hj d a c p ∈
      (finiteGlobalStructure hπ (start := 0) data (k + r) hj).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (iso).hom
    (finiteGlobalStructure hπ (start := 0) data (k + r) hj)
  simp only [shearFiniteGlobalIso_structure] at h
  rw [nodalIntermediateBranchOutput, Scheme.Hom.comp_apply]
  apply h.ge
  exact finiteNodalRefinedBranch_terminal_smooth (nodalSecondShear_depth D k)
    hdepth hrk hrm dat hj sd (nodalSecondQuotient D k)
    (nodalSecondQuotient_factor D k) a' c' hm hr p hp

end FLT.Mazur.WeierstrassDividedDepth
