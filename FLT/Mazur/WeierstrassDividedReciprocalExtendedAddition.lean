/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalTangentExtendedOverlap

/-!
# Extend the resolved partial law by the genuine divided reciprocal domain

Glue the previous extended partial addition and the new reciprocal addition on their
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
local notation "V" => finiteResolvedTangentExtendedOpen hπ data j hj
local notation "N" => finiteResolvedReciprocalOutputOpen hπ data j hj

/-- The two actual domains to be glued: the previous union and the new reciprocal. -/
def finiteResolvedReciprocalExtendedChart (b : Bool) : Scheme :=
  if b then (N).toScheme else (V).toScheme

/-- Each existing domain retains its actual embedding in the full resolved product. -/
def finiteResolvedReciprocalExtendedInput : (b : Bool) →
    finiteResolvedReciprocalExtendedChart hπ data j hj b ⟶ finiteResolvedProduct hπ data j hj
  | false => (V).ι
  | true => finiteResolvedReciprocalDomainMap hπ data j hj

instance finiteResolvedReciprocalExtendedInput_open (b : Bool) :
    IsOpenImmersion (finiteResolvedReciprocalExtendedInput hπ data j hj b) := by
  cases b <;> dsimp only [finiteResolvedReciprocalExtendedInput] <;> infer_instance

/-- Retain the two constructed laws as the local maps for gluing. -/
def finiteResolvedReciprocalExtendedLocal : (b : Bool) →
    finiteResolvedReciprocalExtendedChart hπ data j hj b ⟶ (U).toScheme
  | false => finiteResolvedTangentExtendedPartialAddition hπ data j hj
  | true => finiteResolvedReciprocalAddition hπ data j hj

/-- All ambient intersections have the same resolved output, in both input orders. -/
theorem finiteResolvedReciprocalExtended_overlap (b c : Bool) :
    pullback.fst (finiteResolvedReciprocalExtendedInput hπ data j hj b)
        (finiteResolvedReciprocalExtendedInput hπ data j hj c) ≫
          finiteResolvedReciprocalExtendedLocal hπ data j hj b =
      pullback.snd (finiteResolvedReciprocalExtendedInput hπ data j hj b)
        (finiteResolvedReciprocalExtendedInput hπ data j hj c) ≫
          finiteResolvedReciprocalExtendedLocal hπ data j hj c := by
  cases b <;> cases c
  · congr 1
    exact (cancel_mono (V).ι).mp pullback.condition
  · exact (finiteResolvedReciprocal_tangentExtendedOverlap hπ data j hj _ _
      pullback.condition.symm).symm
  · exact finiteResolvedReciprocal_tangentExtendedOverlap hπ data j hj _ _ pullback.condition
  · congr 1
    exact (cancel_mono (finiteResolvedReciprocalDomainMap hπ data j hj)).mp pullback.condition

/-- The actual open union on which the larger partial multiplication is defined. -/
def finiteResolvedReciprocalExtendedOpen : (finiteResolvedProduct hπ data j hj).Opens :=
  openImageUnion (finiteResolvedReciprocalExtendedInput hπ data j hj)

/-- The old law and the new reciprocal law glue to a single actual resolved multiplication. -/
def finiteResolvedReciprocalExtendedPartialAddition :
    (finiteResolvedReciprocalExtendedOpen hπ data j hj).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue (finiteResolvedReciprocalExtendedInput hπ data j hj)
    (finiteResolvedReciprocalExtendedLocal hπ data j hj)
    (finiteResolvedReciprocalExtended_overlap hπ data j hj)

/-- Restriction to the entire previous domain is exactly the previous partial law. -/
@[reassoc] theorem finiteResolvedReciprocalExtendedPartialAddition_old :
    openImageUnionMap (finiteResolvedReciprocalExtendedInput hπ data j hj) false ≫
        finiteResolvedReciprocalExtendedPartialAddition hπ data j hj =
      finiteResolvedTangentExtendedPartialAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ false

/-- Restriction to the new reciprocal domain is exactly its constructed resolved output. -/
@[reassoc] theorem finiteResolvedReciprocalExtendedPartialAddition_reciprocal :
    openImageUnionMap (finiteResolvedReciprocalExtendedInput hπ data j hj) true ≫
        finiteResolvedReciprocalExtendedPartialAddition hπ data j hj =
      finiteResolvedReciprocalAddition hπ data j hj :=
  openImageUnionGlue_fac _ _ _ true

/-- The glued multiplication retains the original coefficient point of the first input. -/
@[reassoc] theorem finiteResolvedReciprocalExtendedPartialAddition_structure :
    finiteResolvedReciprocalExtendedPartialAddition hπ data j hj ≫ t =
      (finiteResolvedReciprocalExtendedOpen hπ data j hj).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext (finiteResolvedReciprocalExtendedInput hπ data j hj)
  intro b
  cases b
  · rw [finiteResolvedReciprocalExtendedPartialAddition_old_assoc]
    exact (finiteResolvedTangentExtendedPartialAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc (finiteResolvedReciprocalExtendedInput hπ data j hj) false
        (pullback.fst t t ≫ t)).symm
  · rw [finiteResolvedReciprocalExtendedPartialAddition_reciprocal_assoc]
    exact (finiteResolvedReciprocalAddition_structure hπ data j hj).trans
      (openImageUnionMap_fac_assoc (finiteResolvedReciprocalExtendedInput hπ data j hj) true
        (pullback.fst t t ≫ t)).symm

/-- The same original coefficient point is also retained from the second input. -/
@[reassoc] theorem finiteResolvedReciprocalExtendedPartialAddition_structure_snd :
    finiteResolvedReciprocalExtendedPartialAddition hπ data j hj ≫ t =
      (finiteResolvedReciprocalExtendedOpen hπ data j hj).ι ≫ pullback.snd t t ≫ t := by
  rw [finiteResolvedReciprocalExtendedPartialAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
