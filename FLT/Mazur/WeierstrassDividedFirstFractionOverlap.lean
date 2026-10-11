/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionFlatGluing
public import FLT.Mazur.WeierstrassDividedFirstFractionOpen

/-!
# Compatibility of different first-successor fraction action domains

Actual fraction domains are open in the same whole source. Their glued
actions have the same initial contraction on every full intersection,
so flat uniqueness identifies them there, including exceptional outputs.
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
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "C" => BlowupFractionChart.chart I f
local notation "c" => finiteSuccessiveFractionChart hπ data 0 hn f hf
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "U" => firstFractionCover hπ data hn f hf


local notation "E" => initialExterior d

/-- The glued map contracts to the initial action of its actual whole-source inclusion. -/
@[reassoc] theorem firstFractionDomainAction_inclusion :
    firstFractionDomainAction hπ data hn f hf ≫ finiteGlobalStep hπ data 0 hn =
      firstFractionDomainInclusion hπ data hn f hf ≫ firstActionOutput hπ data hn := by
  rw [firstFractionDomainAction_output]
  exact (Category.assoc _ _ _).symm

variable
  (g : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hg : g ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)

/-- Distinct fraction directions agree on any common source flat over the first domain. -/
theorem firstFractionDomainAction_common {X : Scheme.{u}}
    (p : X ⟶ firstFractionDomain hπ data hn f hf) [Flat p]
    (q : X ⟶ firstFractionDomain hπ data hn g hg)
    (hpq : p ≫ firstFractionDomainInclusion hπ data hn f hf =
      q ≫ firstFractionDomainInclusion hπ data hn g hg) :
    p ≫ firstFractionDomainAction hπ data hn f hf =
      q ≫ firstFractionDomainAction hπ data hn g hg := by
  symm
  apply firstFractionDomainAction_flat_unique hπ data hn f hf p
  simp only [Category.assoc, firstFractionDomainAction_inclusion]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ firstActionOutput hπ data hn) hpq.symm

/-- The full categorical intersection identifies the glued actions of any two fractions. -/
theorem firstFractionDomainAction_overlap :
    pullback.fst (firstFractionDomainInclusion hπ data hn f hf)
        (firstFractionDomainInclusion hπ data hn g hg) ≫
        firstFractionDomainAction hπ data hn f hf =
      pullback.snd (firstFractionDomainInclusion hπ data hn f hf)
        (firstFractionDomainInclusion hπ data hn g hg) ≫
        firstFractionDomainAction hπ data hn g hg :=
  firstFractionDomainAction_common hπ data hn f hf g hg _ _ pullback.condition

end FLT.Mazur.WeierstrassDividedDepth
