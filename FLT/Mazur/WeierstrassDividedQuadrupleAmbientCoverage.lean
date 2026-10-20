/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedQuadrupleAmbientAddition
public import FLT.Mazur.WeierstrassDividedQuadrupleRelativeSmoothCoverage

/-!
# Ambient coverage supplied by the universal quadruple-depth extension

The old ambient domain is preserved. Every full relatively smooth nodal tensor
input in either constructed quadruple-depth formula open belongs to the new ambient law.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure rootShearCurve
  nodalSecondShear nodalSecondQuotient
variable {R : Type} [CommRing R] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (4 * k)) (d : Data W π k)
local notation "data" => splitNodeDoubledFamily D
local notation "j" => k + k
local notation "hj" => (le_rfl : k + k ≤ k + k)
local notation "a" => dividedPairLeft W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalQuadrupleAdditionOpen D d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => quadrupleSmoothSourceOpen D d a c
local notation "pair" => quadrupleCommonInput D d a c
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

local notation "inc" => quadrupleAmbientInput D d
local notation "Ambient" => quadrupleAmbientOpen D d
local notation "S" => DividedPairRing W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "dx" => a (x W (π ^ k) (d).b3 (d).b4 (d).b6) -
  c (x W (π ^ k) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a c

/-- The ambient domain is exactly the old open union the actual universal quadruple-depth image. -/
theorem quadrupleAmbientOpen_eq : Ambient = Old ⊔ (pair).opensRange := by
  simp only [quadrupleAmbientOpen, openImageUnion, iSup_bool_eq,
    quadrupleAmbientInput, Scheme.Opens.opensRange_ι]
  exact sup_comm _ _

/-- No point of the previous ambient law is lost. -/
theorem quadrupleAmbientOpen_old_le : Old ≤ Ambient := by
  rw [quadrupleAmbientOpen_eq]
  exact le_sup_left

/-- The whole constructed universal quadruple-depth domain is included in the ambient law. -/
theorem quadrupleAmbientOpen_quadruple_le : (pair).opensRange ≤ Ambient := by
  rw [quadrupleAmbientOpen_eq]
  exact le_sup_right

/-- Full relative smoothness supplies ambient coverage at every quadruple-depth nodal
formula input. -/
theorem quadrupleAmbientOpen_covers
    (hpos : 0 < k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    finiteSuppliedSmoothPair hπ data k (by omega) d (Nat.zero_add k)
      j (by omega) hj a c ⟨p, hs⟩ ∈ Ambient := by
  have hv := quadrupleSmoothSourceOpen_covers D d a c
    hpos p hp hs hformula
  apply quadrupleAmbientOpen_quadruple_le D d
  refine ⟨⟨p, hv⟩, ?_⟩
  simp only [quadrupleCommonInput, Scheme.Hom.comp_apply, Scheme.homOfLE_apply']

end FLT.Mazur.WeierstrassDividedDepth
