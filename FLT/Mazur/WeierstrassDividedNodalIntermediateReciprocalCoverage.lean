/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateAdditionSourceCoverage
public import FLT.Mazur.WeierstrassDividedReciprocalPrimeCoverage

/-!
# Complete intermediate nodal coverage for vertical-smooth contracted inputs

The reciprocal output fills the equal-abscissa complement of the two slope
opens. No formula-denominator hypothesis remains. This covers the stated
contracted-input locus, not all smooth points of the retained older charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalIntermediateBranchCommonOutput nodalIntermediateNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalIntermediateTangentBranchOutputOpen D hdepth hrk hrm data hj d a c
local notation "Os" => ⨆ i, nodalIntermediateSecantLocalOpen D hdepth hrk hrm data hj d a c i
local notation "ft" => nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c
local notation "fs" => nodalIntermediateSecantGluedOutput D hdepth hrk hrm data hj d a c

local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hj d a c
local notation "dx" => a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6)
local notation "E" => dividedTangentDenominator W s d.b3 d.b4 d.b6 a c
local notation "δ" => verticalDerivative W s d.b3 d.b4 d.b6

/-- Intermediate and reciprocal outputs cover all vertical-smooth closed-fiber inputs. -/
theorem nodalIntermediate_or_reciprocal_cover
    (hk : 0 < k) (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ha : a δ ∉ p.asIdeal) (hc : c δ ∉ p.asIdeal) :
    p ∈ O ∨ p ∈ suppliedReciprocalDomain d a c := by
  by_cases hx : dx ∈ p.asIdeal
  · by_cases he : E ∈ p.asIdeal
    · exact Or.inr (suppliedReciprocalDomain_mem_of_denominators d a c p hx he ha)
    · exact Or.inl (nodalIntermediateAdditionOpen_source_tangent
        D hdepth hrk hrm data hj d a c hm hr p hp hx he)
  · exact Or.inl (nodalIntermediateAdditionOpen_source_secant
      D hdepth hrk hrm data hj d a c hk hm hr p hp ha hc hx)

/-- Any point missed by both constructed domains has a singular vertical input. -/
theorem nodalIntermediate_reciprocal_missing_input
    (hk : 0 < k) (hm : m < 4 * k) (hr : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal)
    (ho : p ∉ O) (hq : p ∉ suppliedReciprocalDomain d a c) :
    a δ ∈ p.asIdeal ∨ c δ ∈ p.asIdeal := by
  by_contra h
  push Not at h
  exact (nodalIntermediate_or_reciprocal_cover
    D hdepth hrk hrm data hj d a c hk hm hr p hp h.1 h.2).elim ho hq

end FLT.Mazur.WeierstrassDividedDepth
