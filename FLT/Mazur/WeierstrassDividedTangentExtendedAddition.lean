/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentExtendedOverlap

/-!
# Extend the resolved partial law by the genuine divided tangent domain

Glue the previous extended partial addition and the new tangent addition on their
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
local notation "V" => finiteResolvedExtendedOpen hπ data j hj
local notation "N" => finiteResolvedTangentOutputOpen hπ data j hj

/-- The two actual domains to be glued: the previous union and the new tangent. -/
def finiteResolvedTangentExtendedChart (b : Bool) : Scheme :=
  if b then (N).toScheme else (V).toScheme

/-- Each existing domain retains its actual embedding in the full resolved product. -/
def finiteResolvedTangentExtendedInput : (b : Bool) →
    finiteResolvedTangentExtendedChart hπ data j hj b ⟶ finiteResolvedProduct hπ data j hj
  | false => (V).ι
  | true => finiteResolvedTangentDomainMap hπ data j hj

instance finiteResolvedTangentExtendedInput_open (b : Bool) :
    IsOpenImmersion (finiteResolvedTangentExtendedInput hπ data j hj b) := by
  cases b <;> dsimp only [finiteResolvedTangentExtendedInput] <;> infer_instance

/-- Retain the two constructed laws as the local maps for gluing. -/
def finiteResolvedTangentExtendedLocal : (b : Bool) →
    finiteResolvedTangentExtendedChart hπ data j hj b ⟶ (U).toScheme
  | false => finiteResolvedExtendedPartialAddition hπ data j hj
  | true => finiteResolvedTangentAddition hπ data j hj

/-- All ambient intersections have the same resolved output, in both input orders. -/
theorem finiteResolvedTangentExtended_overlap (b c : Bool) :
    pullback.fst (finiteResolvedTangentExtendedInput hπ data j hj b)
        (finiteResolvedTangentExtendedInput hπ data j hj c) ≫
          finiteResolvedTangentExtendedLocal hπ data j hj b =
      pullback.snd (finiteResolvedTangentExtendedInput hπ data j hj b)
        (finiteResolvedTangentExtendedInput hπ data j hj c) ≫
          finiteResolvedTangentExtendedLocal hπ data j hj c := by
  cases b <;> cases c
  · congr 1
    exact (cancel_mono (V).ι).mp pullback.condition
  · exact (finiteResolvedTangent_extendedOverlap hπ data j hj _ _ pullback.condition.symm).symm
  · exact finiteResolvedTangent_extendedOverlap hπ data j hj _ _ pullback.condition
  · congr 1
    exact (cancel_mono (finiteResolvedTangentDomainMap hπ data j hj)).mp pullback.condition

/-- The actual open union on which the larger partial multiplication is defined. -/
def finiteResolvedTangentExtendedOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion (finiteResolvedTangentExtendedInput hπ data j hj)

/-- The old law and the new tangent law glue to a single actual resolved multiplication. -/
def finiteResolvedTangentExtendedPartialAddition :
    (finiteResolvedTangentExtendedOpen hπ data j hj).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue (finiteResolvedTangentExtendedInput hπ data j hj)
    (finiteResolvedTangentExtendedLocal hπ data j hj)
    (finiteResolvedTangentExtended_overlap hπ data j hj)

/-- Restriction to the entire previous domain is exactly the previous partial law. -/
@[reassoc] theorem finiteResolvedTangentExtendedPartialAddition_old :
    openImageUnionMap (finiteResolvedTangentExtendedInput hπ data j hj) false ≫
        finiteResolvedTangentExtendedPartialAddition hπ data j hj =
      finiteResolvedExtendedPartialAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ false

/-- Restriction to the new tangent domain is exactly its constructed resolved output. -/
@[reassoc] theorem finiteResolvedTangentExtendedPartialAddition_tangent :
    openImageUnionMap (finiteResolvedTangentExtendedInput hπ data j hj) true ≫
        finiteResolvedTangentExtendedPartialAddition hπ data j hj =
      finiteResolvedTangentAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ true

/-- The glued multiplication retains the original coefficient point of the first input. -/
@[reassoc] theorem finiteResolvedTangentExtendedPartialAddition_structure :
    finiteResolvedTangentExtendedPartialAddition hπ data j hj ≫ t =
      (finiteResolvedTangentExtendedOpen hπ data j hj).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext (finiteResolvedTangentExtendedInput hπ data j hj)
  intro b
  cases b
  · rw [finiteResolvedTangentExtendedPartialAddition_old_assoc]
    exact (finiteResolvedExtendedPartialAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc (finiteResolvedTangentExtendedInput hπ data j hj) false
        (pullback.fst t t ≫ t)).symm
  · rw [finiteResolvedTangentExtendedPartialAddition_tangent_assoc]
    exact (finiteResolvedTangentAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc (finiteResolvedTangentExtendedInput hπ data j hj) true
        (pullback.fst t t ≫ t)).symm

/-- The same original coefficient point is also retained from the second input. -/
@[reassoc] theorem finiteResolvedTangentExtendedPartialAddition_structure_snd :
    finiteResolvedTangentExtendedPartialAddition hπ data j hj ≫ t =
      (finiteResolvedTangentExtendedOpen hπ data j hj).ι ≫ pullback.snd t t ≫ t := by
  rw [finiteResolvedTangentExtendedPartialAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
