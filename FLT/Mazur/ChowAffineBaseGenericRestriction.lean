/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessGenericRestriction
public import FLT.Mazur.ChowAffineBaseLineBundle

/-!
# Generic restriction of Chow witnesses

Over the actual dense isomorphism open, the direct image of every natural power
is the line bundle transported by the inverse scheme isomorphism. At the generic
point of an integral source, the maximal ideal vanishes and the actual stalk has
dimension one for its canonical residue-field action. No coherence of the full
direct image or cohomology comparison is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CoherentGenericIdealEmbedding
open FLT.Mazur.AnnihilatorSubsheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat} [IsNoetherianRing R] {X : Scheme} (f : X ⟶ Spec R)
  [IsProper f]

/-- Open base change followed by transport through the actual Chow isomorphism. -/
def graphPowerCommonIso (n : ℕ) :
    ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).restrict
        (chartData f).common.ι ≅
      ((graphLineBundlePower f n).restrict
        (graphClosureπ f ⁻¹ᵁ (chartData f).common).ι).restrict
          (graphClosureCommonIso f).inv :=
  (closedPushforwardRestriction (graphClosureπ f) (chartData f).common).app _ ≪≫
    (pushforwardIsoRestrictInverse (graphClosureCommonIso f)).app _

/-- Every power of the witness has local rank one on the specified dense open. -/
theorem graphPowerCommon_locallyFreeRankOne (n : ℕ) :
    LocallyFreeRankOne
      (((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).restrict
        (chartData f).common.ι) :=
  (((graphLineBundlePower_locallyFreeRankOne f n).restrict _).restrict _).of_iso
    (graphPowerCommonIso f n).symm

end FLT.Mazur.Chow.AffineBase


namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat} [IsNoetherianRing R] {X : Scheme} (f : X ⟶ Spec R)
  [IsProper f]

/-- The canonical residue action on the actual direct-image generic stalk is defined. -/
theorem graphPower_genericStalkAnnihilated [IsIntegral X] (n : ℕ) :
    StalkAnnihilated ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n))
      (genericPoint X) := genericStalkAnnihilated _

/-- The original direct-image stalk has rank one over the generic local ring. -/
def graphPowerGenericCoordinates [IsIntegral X] (n : ℕ) :
    ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).presheaf.stalk
        (genericPoint X) ≃ₗ[X.functionField] X.functionField := by
  let M := (pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)
  let U := (chartData f).common
  let x : U.toScheme := ⟨genericPoint X, graphCommon_genericPoint f⟩
  let h := graphPowerCommon_locallyFreeRankOne f n x
  let V := h.choose
  have hx := h.choose_spec.1
  let e := h.choose_spec.2.some
  let j := V.ι ≫ U.ι
  let y : V.toScheme := ⟨x, hx⟩
  let t : M.restrict j ≅ (structureModule X).restrict j :=
    (restrictFunctorComp V.ι U.ι).app M ≪≫ e ≪≫ (restrictUnitIso j).symm
  let c : M.presheaf.stalk (genericPoint X) ≃ₗ[X.functionField]
      (structureModule X).presheaf.stalk (genericPoint X) := openStalkLinearEquiv j y t
  exact c.trans (structureStalkLinearEquiv (genericPoint X))

/-- The generic residue dimension is one for the action supplied by the annihilation proof. -/
theorem graphPower_generic_finrank [IsIntegral X] (n : ℕ) :
    let := residueModule ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n))
      (genericPoint X) (graphPower_genericStalkAnnihilated f n)
    Module.finrank (X.residueField (genericPoint X))
      (((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n)).presheaf.stalk
        (genericPoint X)) = 1 := by
  let := residueModule ((pushforward (graphClosureπ f)).obj (graphLineBundlePower f n))
    (genericPoint X) (graphPower_genericStalkAnnihilated f n)
  exact (genericResidueCoordinates _ (graphPowerGenericCoordinates f n)).finrank_eq.trans
    (Module.finrank_self _)

end FLT.Mazur.Chow.AffineBase
