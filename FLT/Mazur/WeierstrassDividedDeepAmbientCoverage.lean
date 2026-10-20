/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDeepAmbientAddition
public import FLT.Mazur.WeierstrassDividedDeepRelativeSmoothCoverage

/-!
# Ambient coverage supplied by the universal deep-node extension

The old ambient domain is preserved. Every full relatively smooth nodal tensor
input in either constructed deep-node formula open belongs to the new ambient law.
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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ}
  (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hkk : k + k ≤ n)
  (d : Data W π k)
variable (j : ℕ) (hj : j ≤ n) (hkj : k + k ≤ j)
local notation "a" => dividedPairLeft W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "c" => dividedPairRight W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "O" => nodalDeepAdditionOpen D data hkk d a c
local notation "P" => suppliedDividedSmoothInputOpen d a c

local notation "V" => deepSmoothSourceOpen D data hkk d a c
local notation "pair" => deepCommonInput D data hkk d a c j hj hkj
local notation "Old" => finiteResolvedReciprocalExtendedOpen hπ data j hj
local notation "i" => finiteResolvedReciprocalExtendedInput hπ data j hj

local notation "inc" => deepAmbientInput D data hkk d j hj hkj
local notation "Ambient" => deepAmbientOpen D data hkk d j hj hkj
local notation "S" => DividedPairRing W (π ^ k) (d).b3 (d).b4 (d).b6
local notation "dx" => a (x W (π ^ k) (d).b3 (d).b4 (d).b6) -
  c (x W (π ^ k) (d).b3 (d).b4 (d).b6)
local notation "E" => dividedTangentDenominator W (π ^ k) (d).b3 (d).b4 (d).b6 a c

/-- The ambient domain is exactly the old open union the actual universal deep-node image. -/
theorem deepAmbientOpen_eq : Ambient = Old ⊔ (pair).opensRange := by
  simp only [deepAmbientOpen, openImageUnion, iSup_bool_eq,
    deepAmbientInput, Scheme.Opens.opensRange_ι]
  exact sup_comm _ _

/-- No point of the previous ambient law is lost. -/
theorem deepAmbientOpen_old_le : Old ≤ Ambient := by
  rw [deepAmbientOpen_eq]
  exact le_sup_left

/-- The whole constructed universal deep-node domain is included in the ambient law. -/
theorem deepAmbientOpen_deep_le : (pair).opensRange ≤ Ambient := by
  rw [deepAmbientOpen_eq]
  exact le_sup_right

/-- Full relative smoothness supplies ambient coverage at every deep-node nodal formula input. -/
theorem deepAmbientOpen_covers
    (hpos : 0 < k) (hm : 4 * k < m) (p : PrimeSpectrum S)
    (hp : algebraMap R S π ∈ p.asIdeal) (hs : p ∈ P)
    (hformula : dx ∉ p.asIdeal ∨ E ∉ p.asIdeal) :
    finiteSuppliedSmoothPair hπ data k (by omega) d (Nat.zero_add k)
      j (by omega) hj a c ⟨p, hs⟩ ∈ Ambient := by
  have hv := deepSmoothSourceOpen_covers D data hkk d a c
    hpos hm p hp hs hformula
  apply deepAmbientOpen_deep_le D data hkk d j hj hkj
  refine ⟨⟨p, hv⟩, ?_⟩
  simp only [deepCommonInput, Scheme.Hom.comp_apply, Scheme.homOfLE_apply']

end FLT.Mazur.WeierstrassDividedDepth
