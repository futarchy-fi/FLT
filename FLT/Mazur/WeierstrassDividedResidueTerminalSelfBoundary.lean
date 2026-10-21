/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueTerminalAnyDepthCoverage
public import FLT.Mazur.SchemePairDoubleBoundaryRange

/-!
# Nonpunctured smooth self-pairs on the terminal chart

Both original inputs may have zero horizontal coordinate, including at creation
depth zero. Their full incidence intersection carries a scheme-valued transfer
with both new abscissas nonzero. The original two ambient inputs are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX IsLocalRing
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => ResidueField R
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "a" => PrincipalOpenTensor.inclusion Q t
local notation "b" => (A).hom ≫ PrincipalOpenTensor.inclusion Q x
local notation "old" => globalSuccessiveTensorChart hπ data Q j hj
local notation "next" => globalDividedTensorChart hπ data Q (j + 1) hj
local notation "s" => pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
  (finiteGlobalStructure hπ data (j + 1) hj)
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => (globalTensor_depthOverlap_isPullback hπ data Q j hj).flip

local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "hb" => (show a ≫ f = b ≫ f' from by
  simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w)

/-- The intersection of the two original incidence opens in the complete self-pair. -/
def residueTerminalSelfBoundaryOpen : (pullback f f).Opens :=
  SchemePairDoubleBoundary.domain f f a a

local notation "O" => residueTerminalSelfBoundaryOpen hπ data j hj

/-- The double domain is exactly the two original incidence nonvanishing conditions. -/
theorem residueTerminalSelfBoundaryOpen_mem (p : (pullback f f : Scheme)) :
    p ∈ O ↔ tt ∉ (pullback.fst f f p).asIdeal ∧ tt ∉ (pullback.snd f f p).asIdeal := by
  change pullback.fst f f p ∈ Set.range a ∧ pullback.snd f f p ∈ Set.range a ↔ _
  exact and_congr (PrincipalOpenTensor.mem_inclusion_range Q t _)
    (PrincipalOpenTensor.mem_inclusion_range Q t _)

/-- Change both inputs on the entire original incidence intersection. -/
def residueTerminalSelfBoundaryTransfer : (O).toScheme ⟶ pullback f' f' :=
  SchemePairDoubleBoundary.transfer f f' f f' a b a b hb hb

local notation "tr" => residueTerminalSelfBoundaryTransfer hπ data j hj

/-- The first original ambient input survives both boundary changes. -/
@[reassoc] theorem residueTerminalSelfBoundaryTransfer_first :
    tr ≫ pullback.fst f' f' ≫ next = (O).ι ≫ pullback.fst f f ≫ old :=
  SchemePairDoubleBoundary.transfer_first_ambient f f' f f' a b a b hb hb old next (H).w

/-- The second original ambient input survives both boundary changes. -/
@[reassoc] theorem residueTerminalSelfBoundaryTransfer_second :
    tr ≫ pullback.snd f' f' ≫ next = (O).ι ≫ pullback.snd f f ≫ old :=
  SchemePairDoubleBoundary.transfer_second_ambient f f' f f' a b a b hb hb old next (H).w

/-- Both new abscissas are nonzero throughout the actual double boundary domain. -/
theorem residueTerminalSelfBoundaryTransfer_punctured (p : (O).toScheme) :
    tu ∉ (pullback.fst f' f' (tr p)).asIdeal ∧
      tu ∉ (pullback.snd f' f' (tr p)).asIdeal := by
  have h₁ := SchemePairDoubleBoundary.transfer_fst_mem_range f f' f f' a b a b hb hb p
  have h₂ := SchemePairDoubleBoundary.transfer_snd_mem_range f f' f f' a b a b hb hb p
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  have hv' : tu ∉ (b v).asIdeal :=
    (PrincipalOpenTensor.mem_inclusion_range Q x _).mp ⟨_, rfl⟩
  have hw' : tu ∉ (b w).asIdeal :=
    (PrincipalOpenTensor.mem_inclusion_range Q x _).mp ⟨_, rfl⟩
  exact ⟨hv ▸ hv', hw ▸ hw'⟩

include D in
/-- Two smooth zero-abscissa inputs belong to the full simultaneous transfer domain. -/
theorem residueTerminalSelfBoundaryOpen_anyDepth_zero_mem
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f f : Scheme))
    (hs₁ : old (pullback.fst f f p) ∈ (s).smoothLocus)
    (hs₂ : old (pullback.snd f f p) ∈ (s).smoothLocus)
    (hz₁ : oldU ∈ (pullback.fst f f p).asIdeal)
    (hz₂ : oldU ∈ (pullback.snd f f p).asIdeal) : p ∈ O := by
  apply (residueTerminalSelfBoundaryOpen_mem hπ data j hj p).mpr
  have h₁ := residueTerminalPairOpen_anyDepth_zero_mem hπ data D j hj f hk p hs₁ hz₁
  have h₂ := residueTerminalPairOpen_anyDepth_zero_mem hπ data D j hj f hk
    ((pullbackSymmetry f f).hom p)
  rw [residueTerminalPairOpen_mem] at h₁ h₂
  have he := congrArg (fun k => k p) (pullbackSymmetry_hom_comp_fst f f)
  change pullback.fst f f ((pullbackSymmetry f f).hom p) = pullback.snd f f p at he
  rw [he] at h₂
  exact ⟨h₁, h₂ hs₂ hz₂⟩

end FLT.Mazur.WeierstrassDividedDepth
