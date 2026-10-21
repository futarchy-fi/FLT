/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalResidueOverlap
public import FLT.Mazur.WeierstrassSuccessiveXResidueSmoothCover
public import FLT.Mazur.PrincipalOpenTensorRange

/-!
# Zero-abscissa inputs at the terminal adjacent chart

When there is no further retained chart, the original divided chart is the
neighbor. Every smooth zero-abscissa point of the newest successive chart
has divided coordinates with nonzero abscissa, at the same global point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "F" => ResidueField R
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F
local notation "TNext" => WeierstrassDilatation.ScalarExtension W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 2
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 0
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R F))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 1) hj)
local notation "g" => globalSuccessiveTensorChart hπ data F j hj
local notation "gNext" => globalDividedTensorChart hπ data F (j + 1) hj
local notation "m" => residueMiddleTransition D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "b" => Spec.map (CommRingCat.ofHom (AlgEquiv.toRingEquiv m).toRingHom) ≫
  PrincipalOpenTensor.inclusion F x

include D hk0 hk

/-- The terminal incidence coordinate is nonzero at every smooth zero-abscissa input. -/
theorem terminalZeroAbscissa_incidence_nonzero (z : Spec (.of T))
    (hs : g z ∈ (p).smoothLocus) (hz : u ∈ z.asIdeal) : tt ∉ z.asIdeal := by
  have h := (residueMiddle_mem_smooth_iff D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) g p
    (globalSuccessiveTensorChart_structure hπ data F j hj) z).mp hs
  exact h.resolve_right (not_not.mpr hz)

/-- The last successive input transfers to actual punctured divided coordinates. -/
theorem terminalZeroAbscissa_next_coordinates (z : Spec (.of T))
    (hs : g z ∈ (p).smoothLocus) (hz : u ∈ z.asIdeal) :
    ∃ w : Spec (.of TNext), gNext w = g z ∧ tx ∉ w.asIdeal := by
  have ht := terminalZeroAbscissa_incidence_nonzero hπ data D j hj hk0 hk z hs hz
  obtain ⟨v, hv⟩ := (PrincipalOpenTensor.mem_inclusion_range F t z).mpr ht
  refine ⟨b v, ?_, ?_⟩
  · have he := congrArg (fun k => k v)
      (globalResidue_middleOverlap hπ data D j hj hk0 hk)
    change gNext (b v) = g (PrincipalOpenTensor.inclusion F t v) at he
    exact he.trans (congrArg g hv)
  · exact (PrincipalOpenTensor.mem_inclusion_range F x _).mp ⟨_, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
