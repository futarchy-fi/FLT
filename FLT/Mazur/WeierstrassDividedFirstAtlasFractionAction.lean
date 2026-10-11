/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionComparison
public import FLT.Mazur.WeierstrassDividedFirstFractionOverlap

/-!
# Actual action maps on fraction branches of the complete input atlas

Transport the glued fraction-domain actions through their full pullback
comparisons. This constructs maps on the three fraction branches of the
complete divided-output cover and on all of their affine refinements.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => previousOriginalMap hπ d e
local notation "g" => WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "hg" => WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "D" => firstDividedInputCover hπ data hn

/-- The actual lift on each entire fraction branch of the complete divided-output atlas. -/
def firstDividedFractionAction (i : Fin 3) : (D).X (some (some i)) ⟶
    finiteGlobalModel hπ data 1 hn :=
  (firstFractionDomainIso hπ data hn (g i) (hg i)).inv ≫
    firstFractionDomainAction hπ data hn (g i) (hg i)

/-- The whole branch action has exactly the prescribed normalized divided output. -/
@[reassoc] theorem firstDividedFractionAction_step (i : Fin 3) :
    firstDividedFractionAction hπ data hn i ≫ finiteGlobalStep hπ data 0 hn =
      (D).f (some (some i)) ≫ pullback.snd _ _ ≫ v := by
  rw [firstDividedFractionAction, Category.assoc, firstFractionDomainAction_step]
  rw [← firstFractionToDividedOutput_snd hπ data hn (g i) (hg i),
    Category.assoc, firstFractionDomainIso_inv_fst_assoc]
  rfl

/-- Each branch contracts to the existing initial action on the whole prescribed source. -/
@[reassoc] theorem firstDividedFractionAction_output (i : Fin 3) :
    firstDividedFractionAction hπ data hn i ≫ finiteGlobalStep hπ data 0 hn =
      (D).f (some (some i)) ≫ pullback.fst _ _ ≫ firstActionOutput hπ data hn := by
  rw [firstDividedFractionAction_step, ← pullback.condition]

/-- Every affine refinement of a fraction branch carries its actual successor action. -/
def firstDividedFractionAffineAction (i : Fin 3)
    (a : ((D).X (some (some i))).affineCover.I₀) :
    ((D).X (some (some i))).affineCover.X a ⟶ finiteGlobalModel hπ data 1 hn :=
  ((D).X (some (some i))).affineCover.f a ≫ firstDividedFractionAction hπ data hn i

/-- Affine branch maps retain the exact output prescribed by the full simultaneous cover. -/
@[reassoc] theorem firstDividedFractionAffineAction_step (i : Fin 3)
    (a : ((D).X (some (some i))).affineCover.I₀) :
    firstDividedFractionAffineAction hπ data hn i a ≫ finiteGlobalStep hπ data 0 hn =
      (firstDividedAffineCover hπ data hn).f ⟨some (some i), a⟩ ≫
        pullback.snd _ _ ≫ v := by
  rw [firstDividedFractionAffineAction, Category.assoc, firstDividedFractionAction_step]
  exact (Category.assoc _ _ _).symm

end FLT.Mazur.WeierstrassDividedDepth
