/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleAmbientAddition
public import FLT.Mazur.WeierstrassDividedTripleRelativeSmoothCoverage

/-!
# Ambient coverage supplied by the universal exact-triple extension

The old ambient domain is preserved. Every full relatively smooth nodal tensor
input in either constructed exact-triple formula open belongs to the new ambient law.
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
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
variable (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j)
local notation "a" => dividedPairLeft W (π ^ (start + k)) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ (start + k)) (d).b3 (d).b4 (d).b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => tripleAdditionOpen D data hk a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => tripleSmoothSourceOpen D data hk a c
local notation "pair" => tripleCommonInput D data hk a c j hj hkj
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

local notation "inc" => tripleAmbientInput D data hk j hj hkj
local notation "Ambient" => tripleAmbientOpen D data hk j hj hkj
local notation "S" => DividedPairRing W (π ^ (start + k)) (d).b3 (d).b4 (d).b6
local notation "dx" => a (x W (π ^ (start + k)) (d).b3 (d).b4 (d).b6) -
  c (x W (π ^ (start + k)) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ (start + k)) (d).b3 (d).b4 (d).b6 a c

/-- The ambient domain is exactly the old open union the actual universal exact-triple image. -/
theorem tripleAmbientOpen_eq : Ambient = Old ⊔ (pair).opensRange := by
  simp only [tripleAmbientOpen, openImageUnion, iSup_bool_eq,
    tripleAmbientInput, Scheme.Opens.opensRange_ι]
  exact sup_comm _ _

/-- No point of the previous ambient law is lost. -/
theorem tripleAmbientOpen_old_le : Old ≤ Ambient := by
  rw [tripleAmbientOpen_eq]
  exact le_sup_left

/-- The whole constructed universal exact-triple domain is included in the ambient law. -/
theorem tripleAmbientOpen_triple_le : (pair).opensRange ≤ Ambient := by
  rw [tripleAmbientOpen_eq]
  exact le_sup_right

/-- Full relative smoothness supplies ambient coverage at every exact-triple nodal formula input. -/
theorem tripleAmbientOpen_covers
    (hpos : 0 < start + k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    finiteSuppliedSmoothPair hπ data k hk d rfl
      j hkj hj a c ⟨p, hs⟩ ∈ Ambient := by
  have hv := tripleSmoothSourceOpen_covers D data hk a c
    hpos p hp hs hformula
  apply tripleAmbientOpen_triple_le D data hk j hj hkj
  refine ⟨⟨p, hv⟩, ?_⟩
  simp only [tripleCommonInput, Scheme.Hom.comp_apply, Scheme.homOfLE_apply']

end FLT.Mazur.WeierstrassDividedDepth
