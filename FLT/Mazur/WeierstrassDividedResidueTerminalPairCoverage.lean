/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.WeierstrassDividedTerminalZeroAbscissa
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer

/-!
# Smooth zero-abscissa terminal inputs in actual residue pair domains

At the last successive chart, every smooth first input is punctured or
belongs to the full pair domain transferring it to the original divided
chart. This changes neither ambient input of the actual relative pair.
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

/-- The whole incidence-open domain in the original older residue relative pair. -/
def residueTerminalPairOpen : (pullback f g).Opens :=
  SchemePairBoundaryTransfer.domain f g a

local notation "O" => residueTerminalPairOpen hπ data j hj g

/-- The pair domain is exactly the nonvanishing locus of the first incidence coordinate. -/
theorem residueTerminalPairOpen_mem (p : (pullback f g : Scheme)) :
    p ∈ O ↔ tt ∉ (pullback.fst f g p).asIdeal := by
  change pullback.fst f g p ∈ Set.range a ↔ _
  exact PrincipalOpenTensor.mem_inclusion_range Q t _

/-- The original common boundary gives a scheme map to the terminal residue pair. -/
def residueTerminalPairTransfer : (O).toScheme ⟶ pullback f' g :=
  SchemePairBoundaryTransfer.transfer f f' g a b (by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w)

local notation "transfer" => residueTerminalPairTransfer hπ data j hj g

/-- Both actual first inputs agree in the resolved residue stage. -/
@[reassoc] theorem residueTerminalPairTransfer_first :
    transfer ≫ pullback.fst f' g ≫ next = (O).ι ≫ pullback.fst f g ≫ old :=
  SchemePairBoundaryTransfer.transfer_first_ambient f f' g a b _ old next (H).w

/-- The second input retains its entire original morphism. -/
@[reassoc] theorem residueTerminalPairTransfer_second :
    transfer ≫ pullback.snd f' g = (O).ι ≫ pullback.snd f g :=
  SchemePairBoundaryTransfer.transfer_snd f f' g a b _

/-- The new coordinates stay in the full divided puncture on the whole pair domain. -/
theorem residueTerminalPairTransfer_punctured (p : (O).toScheme) :
    tu ∉ (pullback.fst f' g (transfer p)).asIdeal := by
  have he := congrArg (fun k => k p)
    (SchemePairBoundaryTransfer.transfer_fst f f' g a b (by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w))
  change pullback.fst f' g (transfer p) = b _ at he
  rw [he]
  exact (PrincipalOpenTensor.mem_inclusion_range Q x _).mp ⟨_, rfl⟩

include D in
/-- Every smooth zero-abscissa first input lies in the actual terminal pair domain. -/
theorem residueTerminalPairOpen_zero_mem
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : tensorCoord W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2 ∈ (pullback.fst f g p).asIdeal) :
    p ∈ O := by
  apply (residueTerminalPairOpen_mem hπ data j hj g p).mpr
  exact terminalZeroAbscissa_incidence_nonzero hπ data D j hj hk0 hk _ hs hz

include D in
/-- The punctured first input and terminal transfer domain cover all smooth first inputs. -/
theorem residueTerminalPairOpen_smooth_cover
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus) :
    tensorCoord W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2 ∉ (pullback.fst f g p).asIdeal ∨ p ∈ O := by
  by_cases hz : tensorCoord W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2 ∈ (pullback.fst f g p).asIdeal
  · exact Or.inr (residueTerminalPairOpen_zero_mem hπ data D j hj g hk0 hk p hs hz)
  · exact Or.inl hz

end FLT.Mazur.WeierstrassDividedDepth
