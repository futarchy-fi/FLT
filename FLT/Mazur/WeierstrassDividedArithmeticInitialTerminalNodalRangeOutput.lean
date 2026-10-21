/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialTerminalNodalCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticInitialTerminalMiddleOutput

/-!
# Full initial/terminal outputs at every positive stage up to middle depth

The unconditional domain equality yields a full scheme morphism. Its output
lifts to the smooth model over the original arithmetic quotient, with both
original coefficient morphisms preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedInitialFormulaCoordinates terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "a" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))
local notation "b" => (1 : Fin (j + 3))
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s

local notation "D" => arithmeticInitialTerminalOpen hπ data m j hj

variable [IsLocalRing R] {depth : ℕ}
  (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hbound : 2 * j ≤ depth)

include node hj0 hbound in
/-- The complete mixed formula domain has an invertible original inclusion. -/
theorem arithmeticInitialTerminalNodalRange_inclusion_isIso : IsIso (D).ι := by
  rw [arithmeticInitialTerminalOpen_le_middle_eq_top hπ data m j hj node hj0 hbound]
  exact (pullback fa fb).topIso.isIso_hom

/-- The actual nodal-range formula is a morphism on the entire smooth arithmetic pair. -/
def arithmeticInitialTerminalNodalRangeOutput : (pullback fa fb) ⟶ (U).toScheme := by
  let _ := arithmeticInitialTerminalNodalRange_inclusion_isIso hπ data m j hj node hj0 hbound
  exact inv (D).ι ≫ arithmeticInitialTerminalAddition hπ data m j hj

local notation "out" => arithmeticInitialTerminalNodalRangeOutput hπ data m j hj node hj0 hbound

/-- Restriction recovers the entire existing addition morphism, not just its contraction. -/
@[reassoc] theorem arithmeticInitialTerminalNodalRangeOutput_restrict :
    (D).ι ≫ out = arithmeticInitialTerminalAddition hπ data m j hj := by
  let _ := arithmeticInitialTerminalNodalRange_inclusion_isIso hπ data m j hj node hj0 hbound
  rw [arithmeticInitialTerminalNodalRangeOutput, IsIso.hom_inv_id_assoc]

/-- The full output retains the original first coefficient morphism. -/
@[reassoc] theorem arithmeticInitialTerminalNodalRangeOutput_structure :
    out ≫ t = pullback.fst fa fb ≫ fa ≫ q := by
  let _ := arithmeticInitialTerminalNodalRange_inclusion_isIso hπ data m j hj node hj0 hbound
  rw [arithmeticInitialTerminalNodalRangeOutput, Category.assoc,
    arithmeticInitialTerminalAddition_structure, IsIso.inv_hom_id_assoc]

/-- The original terminal coefficient morphism is retained as well. -/
@[reassoc] theorem arithmeticInitialTerminalNodalRangeOutput_structure_snd :
    out ≫ t = pullback.snd fa fb ≫ fb ≫ q := by
  rw [arithmeticInitialTerminalNodalRangeOutput_structure, pullback.condition_assoc]

/-- The full output lives over the original quotient, including its nilpotents. -/
def arithmeticInitialTerminalNodalRangeArithmeticOutput : pullback fa fb ⟶ pullback t q :=
  pullback.lift out (pullback.fst fa fb ≫ fa) (by
    simpa only [Category.assoc] using
      arithmeticInitialTerminalNodalRangeOutput_structure hπ data m j hj node hj0 hbound)

local notation "arith" =>
  arithmeticInitialTerminalNodalRangeArithmeticOutput hπ data m j hj node hj0 hbound

/-- Forgetting the quotient recovers the actual resolved formula output. -/
@[reassoc] theorem arithmeticInitialTerminalNodalRangeArithmeticOutput_first :
    arith ≫ pullback.fst t q = out := pullback.lift_fst _ _ _

/-- The full arithmetic output preserves the original quotient point as a morphism. -/
@[reassoc] theorem arithmeticInitialTerminalNodalRangeArithmeticOutput_second :
    arith ≫ pullback.snd t q = pullback.fst fa fb ≫ fa := pullback.lift_snd _ _ _

/-- The same full arithmetic output with the original factors in reverse order. -/
def arithmeticTerminalInitialNodalRangeArithmeticOutput : pullback fb fa ⟶ pullback t q :=
  (pullbackSymmetry fb fa).hom ≫ arith

/-- Reversing the pair preserves its original first coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalInitialNodalRangeArithmeticOutput_structure :
    arithmeticTerminalInitialNodalRangeArithmeticOutput hπ data m j hj node hj0 hbound ≫
      pullback.snd t q = pullback.fst fb fa ≫ fb := by
  rw [arithmeticTerminalInitialNodalRangeArithmeticOutput, Category.assoc,
    arithmeticInitialTerminalNodalRangeArithmeticOutput_second,
    pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]

/-- The full output is uniquely determined by the entire existing addition morphism. -/
theorem arithmeticInitialTerminalNodalRangeOutput_unique
    (other : pullback fa fb ⟶ (U).toScheme)
    (hother : (D).ι ≫ other = arithmeticInitialTerminalAddition hπ data m j hj) :
    other = out := by
  let _ := arithmeticInitialTerminalNodalRange_inclusion_isIso hπ data m j hj node hj0 hbound
  apply (cancel_epi (D).ι).mp
  rw [hother, arithmeticInitialTerminalNodalRangeOutput_restrict]

/-- At exact middle depth the two full outputs agree as whole resolved morphisms. -/
theorem arithmeticInitialTerminalNodalRangeOutput_middle_eq (hmid : 2 * j = depth) :
    out = arithmeticInitialTerminalMiddleOutput hπ data m j hj node hj0 hmid := by
  symm
  exact arithmeticInitialTerminalNodalRangeOutput_unique hπ data m j hj node hj0 hbound _
    (arithmeticInitialTerminalMiddleOutput_restrict hπ data m j hj node hj0 hmid)

end FLT.Mazur.WeierstrassDividedDepth
