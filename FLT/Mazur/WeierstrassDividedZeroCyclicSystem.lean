/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicGlobalBase
public import FLT.Mazur.WeierstrassDividedZeroCyclicGlobalRestriction
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedGlobalSystem

/-!
# The actual depth-zero system is the standard five-gon system over its base

The full global isomorphism is natural at all quotient orders, including
nonconsecutive ones, and lies over the original coefficient system.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "F" => fun k ↦
  arithmeticZeroCyclicGlobalIso hπ data H k hj u hu
local notation "B" => fun k ↦ arithmeticZeroDiagonalSourceToBase hπ data H k hj u hu
local notation "p" => fun k ↦
  arithmeticZeroCyclicStandardToBase hπ data H k hj u hu

/-- The independent standard five-gons retain their full node coefficient maps. -/
def arithmeticZeroCyclicStandardSystem : ℕ ⥤ Scheme :=
  Functor.ofSequence (fun k ↦
    arithmeticZeroCyclicStandardRestriction hπ data H hj u hu k)

local notation "X" => changedArithmeticTargetSystem hπ data H 0 hj u hu
local notation "Y" => arithmeticZeroCyclicStandardSystem hπ data H hj u hu

/-- The entire actual comparison is natural for the full original arithmetic quotients. -/
def arithmeticZeroCyclicComparisonSystem : X ⟶ Y :=
  NatTrans.ofSequence (fun k ↦ (F k).hom) (by
    intro k
    simpa only [changedArithmeticTargetSystem,
      arithmeticZeroCyclicStandardSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroCyclicGlobalIso_restriction hπ data H k hj u hu)

/-- The entire global comparison is a natural isomorphism at every arithmetic order. -/
def arithmeticZeroCyclicComparisonSystemIso : X ≅ Y :=
  NatIso.ofComponents F (fun {_ _} f ↦
    (arithmeticZeroCyclicComparisonSystem hπ data H hj u hu).naturality f)

/-- The independent standard system retains the original full coefficient base. -/
def arithmeticZeroCyclicStandardSystemStructure : Y ⟶ baseSystem R π :=
  NatTrans.ofSequence p (by
    intro k
    simpa only [arithmeticZeroCyclicStandardSystem, baseSystem,
      Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ] using
      arithmeticZeroCyclicStandardRestriction_base hπ data H k hj u hu)

/-- The complete natural standard comparison preserves the original base system. -/
theorem arithmeticZeroCyclicComparisonSystem_base :
    arithmeticZeroCyclicComparisonSystem hπ data H hj u hu ≫
      arithmeticZeroCyclicStandardSystemStructure hπ data H hj u hu =
        arithmeticZeroInfinityNormalizedGlobalSourceSystemStructure hπ data H hj u hu := by
  ext k : 2
  exact arithmeticZeroCyclicGlobalIso_base hπ data H k hj u hu

/-- Nonconsecutive arithmetic orders retain the full standard comparison square. -/
@[reassoc] theorem arithmeticZeroCyclicComparisonSystem_naturality
    {i j : ℕ} (hij : i ≤ j) :
    (X).map (homOfLE hij) ≫ (F j).hom = (F i).hom ≫ (Y).map (homOfLE hij) :=
  (arithmeticZeroCyclicComparisonSystem hπ data H hj u hu).naturality _

/-- The actual quotient systems are isomorphic over the original coefficient system. -/
def arithmeticZeroCyclicComparisonSystemOverIso :
    Over.mk (arithmeticZeroInfinityNormalizedGlobalSourceSystemStructure hπ data H hj u hu) ≅
      Over.mk (arithmeticZeroCyclicStandardSystemStructure hπ data H hj u hu) :=
  Over.isoMk (arithmeticZeroCyclicComparisonSystemIso hπ data H hj u hu)
    (arithmeticZeroCyclicComparisonSystem_base hπ data H hj u hu)

end FLT.Mazur.WeierstrassDividedDepth
