/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateAmbientAddition
public import FLT.Mazur.WeierstrassDividedNodalIntermediateRelativeSmoothCoverage

/-!
# Ambient coverage supplied by the universal intermediate extension

The old ambient domain is preserved. Every full relatively smooth nodal tensor
input in either constructed intermediate formula open belongs to the new ambient law.
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
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : k + r ≤ n)
  (d : Data W π k)
  (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j) (hrj : k + r ≤ j)
local notation "a" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalIntermediateAdditionOpen D hdepth hrk hrm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => nodalIntermediateSmoothSourceOpen D hdepth hrk hrm data hr d a c
local notation "pair" => nodalIntermediateCommonInput D hdepth hrk hrm data hr d a c j hj hkj
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

local notation "inc" => nodalIntermediateAmbientInput D hdepth hrk hrm data hr d j hj hkj
local notation "Ambient" => nodalIntermediateAmbientOpen D hdepth hrk hrm data hr d j hj hkj
local notation "S" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) -
  c (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "E" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c

/-- The ambient domain is exactly the old open union the actual universal intermediate image. -/
theorem nodalIntermediateAmbientOpen_eq : Ambient = Old ⊔ (pair).opensRange := by
  simp only [nodalIntermediateAmbientOpen, openImageUnion, iSup_bool_eq,
    nodalIntermediateAmbientInput, Scheme.Opens.opensRange_ι, sup_comm]

/-- No point of the previous ambient law is lost. -/
theorem nodalIntermediateAmbientOpen_old_le : Old ≤ Ambient := by
  rw [nodalIntermediateAmbientOpen_eq]
  exact le_sup_left

/-- The whole constructed universal intermediate domain is included in the ambient law. -/
theorem nodalIntermediateAmbientOpen_intermediate_le : (pair).opensRange ≤ Ambient := by
  rw [nodalIntermediateAmbientOpen_eq]
  exact le_sup_right

/-- Full relative smoothness supplies ambient coverage at every intermediate nodal formula input. -/
theorem nodalIntermediateAmbientOpen_covers
    (hk : 0 < k) (hhi : m < 4 * k) (heq : r = m - 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    finiteSuppliedSmoothPair hπ data k (hkj.trans hj) d (Nat.zero_add k)
      j hkj hj a c ⟨p, hs⟩ ∈ Ambient := by
  have hv := nodalIntermediateSmoothSourceOpen_covers D hdepth hrk hrm data hr d a c
    hk hhi heq p hp hs hformula
  apply nodalIntermediateAmbientOpen_intermediate_le D hdepth hrk hrm data hr d j hj hkj
  refine ⟨⟨p, hv⟩, ?_⟩
  simp only [nodalIntermediateCommonInput, Scheme.Hom.comp_apply, Scheme.homOfLE_apply']

end FLT.Mazur.WeierstrassDividedDepth
