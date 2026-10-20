/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedProductOverlap

/-!
# Multiplication on the union of the two original-factor opens

Glue the two actual actions inside the product of the full resolved smooth
locus with itself. Either input may be on any resolved component if the
other is originally smooth. Pairs with neither input in that original open
still require the remaining multiplication construction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

local notation "s" => integralSmoothStructure W
local notation "t" => (U).ι ≫ base
local notation "e" => finiteOriginalToResolved hπ data j hj

local notation "V" => finiteResolvedOriginalFactorOpen hπ data j hj
local notation "i" => finiteResolvedInput hπ data j hj

/-- Actual resolved multiplication on the open where at least one input is originally smooth. -/
def finiteResolvedPartialAddition : (V).toScheme ⟶ (U).toScheme :=
  openImageUnionGlue i (fun _ => finiteGlobalSmoothAction hπ data j hj)
    (finiteResolvedAction_overlap hπ data j hj)

/-- Both input orders retain the same original action on every resolved component. -/
@[reassoc] theorem finiteResolvedPartialAddition_chart (b : Bool) :
    openImageUnionMap i b ≫ finiteResolvedPartialAddition hπ data j hj =
      finiteGlobalSmoothAction hπ data j hj :=
  openImageUnionGlue_fac _ _ _ b

/-- The partial multiplication retains the original coefficient map of its first input. -/
@[reassoc] theorem finiteResolvedPartialAddition_structure :
    finiteResolvedPartialAddition hπ data j hj ≫ t =
      (V).ι ≫ pullback.fst t t ≫ t := by
  apply openImageUnion_hom_ext i
  intro b
  rw [finiteResolvedPartialAddition_chart_assoc, finiteGlobalSmoothAction_structure]
  change pullback.fst s t ≫ s =
    openImageUnionMap i b ≫ (openImageUnion i).ι ≫ pullback.fst t t ≫ t
  rw [openImageUnionMap_fac_assoc]
  cases b
  · change pullback.fst s t ≫ s = finiteResolvedLeftInput hπ data j hj ≫ pullback.fst t t ≫ t
    rw [finiteResolvedLeftInput_fst_assoc, finiteOriginalToResolved_structure]
  · rw [finiteResolvedRightInput_fst_assoc]
    exact pullback.condition

/-- The second input has precisely that same original coefficient morphism. -/
@[reassoc] theorem finiteResolvedPartialAddition_structure_snd :
    finiteResolvedPartialAddition hπ data j hj ≫ t =
      (V).ι ≫ pullback.snd t t ≫ t := by
  rw [finiteResolvedPartialAddition_structure, pullback.condition]

end FLT.Mazur.WeierstrassDividedDepth
