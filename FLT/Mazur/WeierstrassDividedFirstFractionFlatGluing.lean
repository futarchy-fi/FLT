/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionGluing

/-!
# Flat base change uniqueness for the glued fraction-domain action

Pulling back the actual affine cover and refining its members transports
local regular-center uniqueness to arbitrary flat scheme restrictions.
No affineness or reducedness is imposed on the new source scheme.
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
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstFractionCover hπ data hn f hf


local notation "E" => initialExterior d

/-- Every flat scheme restriction of the glued domain action is its unique step lift. -/
theorem firstFractionDomainAction_flat_unique {X : Scheme.{u}}
    (p : X ⟶ firstFractionDomain hπ data hn f hf) [Flat p]
    (a : X ⟶ finiteGlobalModel hπ data 1 hn)
    (ha : a ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstFractionDomainAction hπ data hn f hf ≫ finiteGlobalStep hπ data 0 hn) :
    a = p ≫ firstFractionDomainAction hπ data hn f hf :=
  SchemeAffineFlatLiftGluing.flat_unique (U) (firstFractionAction hπ data hn f hf)
    (finiteGlobalStep hπ data 0 hn)
    (fun k _ _ t _ b hb => firstFractionAction_flat_unique hπ data hn f hf k t b hb)
    (firstFractionDomainAction hπ data hn f hf) (firstFractionCover_action hπ data hn f hf)
    p a ha

/-- Equality after step contraction detects equality of arbitrary flat-restricted lifts. -/
theorem firstFractionDomainAction_flat_ext {X : Scheme.{u}}
    (p : X ⟶ firstFractionDomain hπ data hn f hf) [Flat p]
    (a b : X ⟶ finiteGlobalModel hπ data 1 hn)
    (ha : a ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstFractionDomainAction hπ data hn f hf ≫ finiteGlobalStep hπ data 0 hn)
    (hb : b ≫ finiteGlobalStep hπ data 0 hn =
      p ≫ firstFractionDomainAction hπ data hn f hf ≫ finiteGlobalStep hπ data 0 hn) :
    a = b :=
  (firstFractionDomainAction_flat_unique hπ data hn f hf p a ha).trans
    (firstFractionDomainAction_flat_unique hπ data hn f hf p b hb).symm

end FLT.Mazur.WeierstrassDividedDepth
