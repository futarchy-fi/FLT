/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetReflectedQuotientOutput
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleCoverage

/-!
# Reflected outputs cover the whole retained incidence domain

Restrict the three quotient-valued formulas along the actual simultaneous
transfer. Every point is covered, and both original coefficient projections
are preserved, including the nilpotents of the arithmetic base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
  (hij : i ≤ j) (hlo : 2 * (j + 1) < depth)
  (hhi : depth ≤ (i + 1) + 2 * (j + 1))
  (hstage : depth - (i + 1) - (j + 1) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => (Fin.succ ⟨k - i, by omega⟩ : Fin (k + 3))
local notation "rightIndex" => (Fin.succ ⟨k - j, by omega⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart a ≫ s
local notation "g" => chart rightIndex ≫ s
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj
local notation "T" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj
local notation "O" => arithmeticTargetReflectedOutputChart node data m k hk i j hi hj
  hij hlo hhi hstage
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R (Quotient R π m)))

/-- The three actual output domains pulled back to the retained incidence source. -/
def arithmeticRetainedReflectedChart (b : Fin 3) : (D).toScheme.Opens := T ⁻¹ᵁ O b

local notation "C" => arithmeticRetainedReflectedChart node data m k hk i j hi hj
  hij hlo hhi hstage

/-- Each local source has a whole output over the original arithmetic quotient. -/
def arithmeticRetainedReflectedOutput (b : Fin 3) : (C b).toScheme ⟶ pullback q t :=
  (T ∣_ O b) ≫ arithmeticTargetReflectedQuotientOutput node data m k hk i j hi hj
    hij hlo hhi hstage b

local notation "out" => arithmeticRetainedReflectedOutput node data m k hk i j hi hj
  hij hlo hhi hstage

/-- The output coefficient morphism is exactly that of the first original input. -/
@[reassoc] theorem arithmeticRetainedReflectedOutput_base (b : Fin 3) :
    out b ≫ pullback.fst q t = (C b).ι ≫ (D).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticRetainedReflectedOutput, Category.assoc,
    arithmeticTargetReflectedQuotientOutput_base, morphismRestrict_ι_assoc]
  exact congrArg (fun z => (C b).ι ≫ z)
    (arithmeticRetainedDoubleTransfer_first_assoc hπ data m k hk i j hi hj s)

/-- The same output also retains the second original input's coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedReflectedOutput_base_snd (b : Fin 3) :
    out b ≫ pullback.fst q t = (C b).ι ≫ (D).ι ≫ pullback.snd f g ≫ g := by
  rw [arithmeticRetainedReflectedOutput_base, pullback.condition]

/-- Every point of the actual retained incidence domain reaches a formula source. -/
theorem arithmeticRetainedReflectedChart_covers (hlt : i < j) : (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  have hp := arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i j hi hj p
  obtain ⟨b, hb⟩ := arithmeticTargetReflectedOutputChart_punctured
    node data m k hk i j hi hj hij hlo hhi hstage hlt (T p) hp.1 hp.2
  exact (le_iSup (fun b => C b) b) hb

/-- A genuine open cover of the whole unchanged retained incidence scheme. -/
def arithmeticRetainedReflectedCover (hlt : i < j) : (D).toScheme.OpenCover :=
  (D).toScheme.openCoverOfIsOpenCover C
    (arithmeticRetainedReflectedChart_covers node data m k hk i j hi hj
      hij hlo hhi hstage hlt)

end FLT.Mazur.WeierstrassDividedDepth
