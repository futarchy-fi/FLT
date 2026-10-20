/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalShallowAmbientAddition
public import FLT.Mazur.WeierstrassDividedNodalShallowRelativeSmoothCoverage

/-!
# Ambient coverage supplied by the universal shallow extension

The old ambient domain is preserved. Every full relatively smooth nodal tensor
input in either constructed shallow formula open belongs to the new ambient law.
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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hr : m - 2 * k ≤ n)
  (d : Data W π k)
  (j : ℕ) (hj : j ≤ n) (hkj : k ≤ j) (hrj : m - 2 * k ≤ j)
local notation "a" => dividedPairLeft W (π ^ k) d.b3 d.b4 d.b6
local notation "c" => dividedPairRight W (π ^ k) d.b3 d.b4 d.b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalShallowAdditionOpen D hdepth hm data hr d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => nodalShallowSmoothSourceOpen D hdepth hm data hr d a c
local notation "pair" => nodalShallowCommonInput D hdepth hm data hr d a c j hj hkj
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

local notation "inc" => nodalShallowAmbientInput D hdepth hm data hr d j hj hkj
local notation "Ambient" => nodalShallowAmbientOpen D hdepth hm data hr d j hj hkj
local notation "S" => DividedPairRing W (π ^ k) d.b3 d.b4 d.b6
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) -
  c (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "E" => dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c

/-- The ambient domain is exactly the old open union the actual universal shallow image. -/
theorem nodalShallowAmbientOpen_eq : Ambient = Old ⊔ (pair).opensRange := by
  simp only [nodalShallowAmbientOpen, openImageUnion, iSup_bool_eq,
    nodalShallowAmbientInput, Scheme.Opens.opensRange_ι, sup_comm]

/-- No point of the previous ambient law is lost. -/
theorem nodalShallowAmbientOpen_old_le : Old ≤ Ambient := by
  rw [nodalShallowAmbientOpen_eq]
  exact le_sup_left

/-- The whole constructed universal shallow domain is included in the ambient law. -/
theorem nodalShallowAmbientOpen_shallow_le : (pair).opensRange ≤ Ambient := by
  rw [nodalShallowAmbientOpen_eq]
  exact le_sup_right

/-- Full relative smoothness supplies ambient coverage at every shallow nodal formula input. -/
theorem nodalShallowAmbientOpen_covers
    (hk : 0 < k) (hlo : 2 * k < m) (hhi : m < 3 * k) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    finiteSuppliedSmoothPair hπ data k (hkj.trans hj) d (Nat.zero_add k)
      j hkj hj a c ⟨p, hs⟩ ∈ Ambient := by
  have hv := nodalShallowSmoothSourceOpen_covers D hdepth hm data hr d a c
    hk hlo hhi p hp hs hformula
  apply nodalShallowAmbientOpen_shallow_le D hdepth hm data hr d j hj hkj
  refine ⟨⟨p, hv⟩, ?_⟩
  simp only [nodalShallowCommonInput, Scheme.Hom.comp_apply, Scheme.homOfLE_apply']

end FLT.Mazur.WeierstrassDividedDepth
