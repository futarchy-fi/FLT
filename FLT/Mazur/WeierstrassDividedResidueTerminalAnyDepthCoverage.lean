/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueTerminalPairCoverage
public import FLT.Mazur.WeierstrassDividedTerminalZeroAbscissa
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer

public import FLT.Mazur.WeierstrassSuccessiveXAnyDepthSmoothCover

/-!
# Actual terminal pair coverage including zero creation depth

Smoothness is exactly membership in the horizontal puncture or the original
incidence transfer domain. A nonpunctured smooth input acquires punctured
coordinates without changing either actual input of its relative pair.
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
variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of (ResidueField R)))


local notation "O" => residueTerminalPairOpen hπ data j hj g
local notation "transfer" => residueTerminalPairTransfer hπ data j hj g
local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

include D in
/-- The two full original pair opens test precisely smoothness at every creation depth. -/
theorem residueTerminalPairOpen_anyDepth_smooth_iff
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme)) :
    old (pullback.fst f g p) ∈ (s).smoothLocus ↔
      oldU ∉ (pullback.fst f g p).asIdeal ∨ p ∈ O := by
  rw [residueTerminalPairOpen_mem]
  exact (residueAnyDepth_mem_smooth_iff D (start + j) hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) old s
    (globalSuccessiveTensorChart_structure hπ data Q j hj) _).trans or_comm

include D in
/-- Zero abscissa forces the actual boundary condition, also for zero-depth inputs. -/
theorem residueTerminalPairOpen_anyDepth_zero_mem
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) : p ∈ O := by
  have h := (residueTerminalPairOpen_anyDepth_smooth_iff hπ data D j hj g hk p).mp hs
  exact h.resolve_left (not_not.mpr hz)

include D in
/-- The transferred point is an actual relative pair with the same two ambient inputs. -/
theorem residueTerminalPair_anyDepth_zero_coordinates
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) :
    ∃ q : (pullback f' g : Scheme),
      next (pullback.fst f' g q) = old (pullback.fst f g p) ∧
      pullback.snd f' g q = pullback.snd f g p ∧
      tu ∉ (pullback.fst f' g q).asIdeal := by
  let v : (O).toScheme :=
    ⟨p, residueTerminalPairOpen_anyDepth_zero_mem hπ data D j hj g hk p hs hz⟩
  refine ⟨transfer v, ?_, ?_, residueTerminalPairTransfer_punctured hπ data j hj g v⟩
  · exact congrArg (fun k => k v) (residueTerminalPairTransfer_first hπ data j hj g)
  · exact congrArg (fun k => k v) (residueTerminalPairTransfer_second hπ data j hj g)

end FLT.Mazur.WeierstrassDividedDepth
