/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedLineTwist
public import FLT.Mazur.IdealModulePullbackRestrict
public import FLT.Mazur.BaseAdicThickening

/-!
# Canonical pullback of ideal-adic graded pieces

The comparison is constructed from the actual ideal-module pullback map
and descends through the next-power relation. No flatness is needed, and
no assertion that this comparison is invertible is made.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Pullback of an ideal power maps canonically into the extended power. -/
def powerComparison (n : ℕ) :
    (Scheme.Modules.pullback f).obj (idealModule (J ^ n)) ⟶ idealModule (J.comap f ^ n) :=
  idealModulePullbackHom (J ^ n) f ≫
    idealMap (idealSheaf_comap_pow J f n).le

/-- The comparison retains the original pulled-back ideal inclusion. -/
@[reassoc]
lemma powerComparison_inclusion (n : ℕ) :
    powerComparison J f n ≫ idealModuleι (J.comap f ^ n) =
      idealModulePullbackι (J ^ n) f := by
  unfold powerComparison
  rw [Category.assoc, idealMap_comp, idealModulePullbackHom_ι]

/-- The adjoint comparison permits descent in the category on the base. -/
def powerMap (n : ℕ) :
    idealModule (J ^ n) ⟶ (pushforward f).obj (idealModule (J.comap f ^ n)) :=
  (pullbackPushforwardAdjunction f).homEquiv _ _ (powerComparison J f n)

/-- Base sections map to their actual scheme images in the extended ideal. -/
lemma powerMap_inclusion (n : ℕ) (U : Y.Opens) (s : Γ(idealModule (J ^ n), U)) :
    (idealModuleι (J.comap f ^ n)).app (f ⁻¹ᵁ U) ((powerMap J f n).app U s) =
      f.app U ((idealModuleι (J ^ n)).app U s) := by
  have h := congrArg (fun k ↦ k.app (f ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction f).unit.app (idealModule (J ^ n))).app U s))
      (powerComparison_inclusion J f n)
  exact h.trans (idealModulePullbackι_unit (J ^ n) f U s)

/-- The power comparison commutes with the next-power inclusions. -/
@[reassoc]
lemma powerMap_step (n : ℕ) :
    idealStep J n ≫ powerMap J f n =
      powerMap J f (n + 1) ≫ (pushforward f).map (idealStep (J.comap f) n) := by
  apply (cancel_mono ((pushforward f).map (idealModuleι (J.comap f ^ n)))).mp
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  change (idealModuleι (J.comap f ^ n)).app (f ⁻¹ᵁ U)
    ((powerMap J f n).app U ((idealStep J n).app U s)) =
    (idealModuleι (J.comap f ^ n)).app (f ⁻¹ᵁ U)
      ((idealStep (J.comap f) n).app (f ⁻¹ᵁ U) ((powerMap J f (n + 1)).app U s))
  have hs (K : Y.IdealSheafData) := idealMap_comp
    (I := K ^ (n + 1)) (J := K ^ n) (fun _ ↦ Ideal.pow_le_pow_right (by omega))
  have ht := idealMap_comp (I := J.comap f ^ (n + 1)) (J := J.comap f ^ n)
    (fun _ ↦ Ideal.pow_le_pow_right (by omega))
  rw [powerMap_inclusion]
  have h1 := congrArg (fun k ↦ k.app U s) (hs J)
  have h2 := congrArg (fun k ↦ k.app (f ⁻¹ᵁ U) ((powerMap J f (n + 1)).app U s)) ht
  exact (congrArg (f.app U) h1).trans ((powerMap_inclusion J f (n + 1) U s).symm.trans
    h2.symm)

/-- The next base power vanishes in the target graded quotient. -/
lemma powerMap_quotient_zero (n : ℕ) :
    idealStep J n ≫ (powerMap J f n ≫
      (pushforward f).map (cokernel.π (idealStep (J.comap f) n))) = 0 := by
  rw [powerMap_step_assoc, ← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero]

/-- The canonical comparison on the actual associated-graded pieces. -/
def gradedMap (n : ℕ) :
    idealGraded J n ⟶ (pushforward f).obj (idealGraded (J.comap f) n) :=
  cokernel.desc (idealStep J n)
    (powerMap J f n ≫ (pushforward f).map (cokernel.π (idealStep (J.comap f) n)))
    (powerMap_quotient_zero J f n)

/-- The comparison takes the class of a base ideal section to its extended class. -/
@[reassoc (attr := simp)]
lemma gradedMap_projection (n : ℕ) :
    cokernel.π (idealStep J n) ≫ gradedMap J f n =
      powerMap J f n ≫ (pushforward f).map (cokernel.π (idealStep (J.comap f) n)) :=
  cokernel.π_desc _ _ _

/-- Pullback of the graded piece maps to the actual extended-ideal graded piece. -/
def gradedComparison (n : ℕ) :
    (Scheme.Modules.pullback f).obj (idealGraded J n) ⟶ idealGraded (J.comap f) n :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm (gradedMap J f n)

end FLT.Mazur.IdealAdicGradedPullback
