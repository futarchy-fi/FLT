/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalRefinedBranchReindex
public import FLT.Mazur.WeierstrassDividedNodalRefinedBranchTerminal

/-!
# Intermediate derivative coverage with independently indexed targets

Transport the proved derivative coverage along the target-depth equality.
The target family may use its own index and chosen divided coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {m k r l : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k) (e : Data W π l) (hl : l = k + r)
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S) [Module.Flat R S]
local notation "B" => DividedTangentBranchRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "res" => dividedTangentBranchRestriction W (π ^ k) d.b3 d.b4 d.b6 a c

/-- Reindexing the target preserves coverage of the whole nodal fiber by the derivative open. -/
theorem nodalRefinedBranchReindexedOutput_terminal_mem
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen
      ((nodalRefinedBranchReindexedOutput D d hdepth hrk hrm e hl a2 h2 a c)
        (verticalDerivative W (π ^ l) e.b3 e.b4 e.b6)) := by
  subst l
  exact nodalRefinedBranchOutput_terminal_mem D d hdepth hrk hrm e a2 h2 a c hm hr p hp

end FLT.Mazur.WeierstrassDividedDepth
