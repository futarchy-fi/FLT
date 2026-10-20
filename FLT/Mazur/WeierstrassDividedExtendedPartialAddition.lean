/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantPartialOverlap

/-!
# Extend the resolved partial law by the genuine divided secant domain

Glue the previous partial addition and the new secant addition on their
actual open union in the full resolved product. Both laws and the original
coefficient morphism are retained. Full product coverage is still separate.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "V" => finiteResolvedOriginalFactorOpen hπ data j hj
local notation "N" => finiteResolvedSecantOutputOpen hπ data j hj

/-- The two actual domains to be glued: the previous union and the new secant. -/
def finiteResolvedExtendedChart (b : Bool) : Scheme :=
  if b then (N).toScheme else (V).toScheme

/-- Each existing domain retains its actual embedding in the full resolved product. -/
def finiteResolvedExtendedInput : (b : Bool) →
    finiteResolvedExtendedChart hπ data j hj b ⟶ finiteResolvedProduct hπ data j hj
  | false => (V).ι
  | true => finiteResolvedSecantDomainMap hπ data j hj

instance finiteResolvedExtendedInput_open (b : Bool) :
    IsOpenImmersion (finiteResolvedExtendedInput hπ data j hj b) := by
  cases b <;> dsimp only [finiteResolvedExtendedInput] <;> infer_instance

/-- Retain the two constructed laws as the local maps for gluing. -/
def finiteResolvedExtendedLocal : (b : Bool) →
    finiteResolvedExtendedChart hπ data j hj b ⟶ (U).toScheme
  | false => finiteResolvedPartialAddition hπ data j hj
  | true => finiteResolvedSecantAddition hπ data j hj

/-- All ambient intersections have the same resolved output, in both input orders. -/
theorem finiteResolvedExtended_overlap (b c : Bool) :
    pullback.fst (finiteResolvedExtendedInput hπ data j hj b)
        (finiteResolvedExtendedInput hπ data j hj c) ≫
          finiteResolvedExtendedLocal hπ data j hj b =
      pullback.snd (finiteResolvedExtendedInput hπ data j hj b)
        (finiteResolvedExtendedInput hπ data j hj c) ≫
          finiteResolvedExtendedLocal hπ data j hj c := by
  cases b <;> cases c
  · congr 1
    exact (cancel_mono (V).ι).mp pullback.condition
  · exact (finiteResolvedSecant_partialOverlap hπ data j hj _ _ pullback.condition.symm).symm
  · exact finiteResolvedSecant_partialOverlap hπ data j hj _ _ pullback.condition
  · congr 1
    exact (cancel_mono (finiteResolvedSecantDomainMap hπ data j hj)).mp pullback.condition

/-- The actual open union on which the larger partial multiplication is defined. -/
def finiteResolvedExtendedOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion (finiteResolvedExtendedInput hπ data j hj)

/-- The old law and the new secant law glue to a single actual resolved multiplication. -/
def finiteResolvedExtendedPartialAddition :
    (finiteResolvedExtendedOpen hπ data j hj).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue (finiteResolvedExtendedInput hπ data j hj)
    (finiteResolvedExtendedLocal hπ data j hj) (finiteResolvedExtended_overlap hπ data j hj)

/-- Restriction to the entire previous domain is exactly the previous partial law. -/
@[reassoc] theorem finiteResolvedExtendedPartialAddition_old :
    openImageUnionMap (finiteResolvedExtendedInput hπ data j hj) false ≫
        finiteResolvedExtendedPartialAddition hπ data j hj =
      finiteResolvedPartialAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ false

/-- Restriction to the new secant domain is exactly its constructed resolved output. -/
@[reassoc] theorem finiteResolvedExtendedPartialAddition_secant :
    openImageUnionMap (finiteResolvedExtendedInput hπ data j hj) true ≫
        finiteResolvedExtendedPartialAddition hπ data j hj =
      finiteResolvedSecantAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ true

/-- The glued multiplication retains the original coefficient point of the first input. -/
@[reassoc] theorem finiteResolvedExtendedPartialAddition_structure :
    finiteResolvedExtendedPartialAddition hπ data j hj ≫ t =
      (finiteResolvedExtendedOpen hπ data j hj).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext (finiteResolvedExtendedInput hπ data j hj)
  intro b
  cases b
  · rw [finiteResolvedExtendedPartialAddition_old_assoc]
    exact (finiteResolvedPartialAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc (finiteResolvedExtendedInput hπ data j hj) false
        (pullback.fst t t ≫ t)).symm
  · rw [finiteResolvedExtendedPartialAddition_secant_assoc]
    exact (finiteResolvedSecantAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc (finiteResolvedExtendedInput hπ data j hj) true
        (pullback.fst t t ≫ t)).symm

/-- The same original coefficient point is also retained from the second input. -/
@[reassoc] theorem finiteResolvedExtendedPartialAddition_structure_snd :
    finiteResolvedExtendedPartialAddition hπ data j hj ≫ t =
      (finiteResolvedExtendedOpen hπ data j hj).ι ≫ pullback.snd t t ≫ t := by
  rw [finiteResolvedExtendedPartialAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
