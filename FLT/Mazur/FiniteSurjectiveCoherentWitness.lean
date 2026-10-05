/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SurjectiveStructureSupport
public import FLT.Mazur.FinitePushforwardCoherent
public import FLT.Mazur.CoherentIdealPowerFiltration

/-!
# Coherent witnesses for finite surjective maps

For an integral closed subscheme of the target, take the structure module of
its inverse image and push it to the source. Base change preserves finite
surjectivity. Factoring its direct image through the integral closed subscheme
proves both its exact support and its generic maximal-ideal annihilation.
This gives the witnesses of Stacks 01YO without a generic-rank-one restriction.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.CoherentGenericIdealEmbedding

universe u

namespace FLT.Mazur.FCurve
open CoherentDevissage CoherentIdealIntersection

/-- The structure module of the inverse image supplies a coherent direct-image witness. -/
theorem finiteSurjective_exists_coherent_witness {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (g : Y ⟶ X) [IsFinite g] [Surjective g] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] :
    ∃ F : Y.Modules, F.IsFinitePresentation ∧
      support ((pushforward g).obj F) = Set.range J.subschemeι ∧
      StalkAnnihilated ((pushforward g).obj F) (J.subschemeι (genericPoint J.subscheme)) := by
  let P := pullback g J.subschemeι
  let a : P ⟶ Y := pullback.fst g J.subschemeι
  let b : P ⟶ J.subscheme := pullback.snd g J.subschemeι
  have : IsClosedImmersion a := inferInstanceAs (IsClosedImmersion (pullback.fst g J.subschemeι))
  have : IsFinite b := inferInstanceAs (IsFinite (pullback.snd g J.subschemeι))
  have : Surjective b := inferInstanceAs (Surjective (pullback.snd g J.subschemeι))
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := structureModule_coherent (X := P)
  let F := (pushforward a).obj (structureModule P)
  let N := (pushforward b).obj (structureModule P)
  let e : (pushforward g).obj F ≅ (pushforward J.subschemeι).obj N :=
    (pushforwardComp a g).app (structureModule P) ≪≫
      (pushforwardCongr (pullback.condition (f := g) (g := J.subschemeι))).app
        (structureModule P) ≪≫ ((pushforwardComp b J.subschemeι).app (structureModule P)).symm
  refine ⟨F, closedPushforward_isFinitePresentation a _, ?_, ?_⟩
  · rw [support_iso e, support_closedPushforward,
      StructureDirectImage.support_eq_univ_of_dominant b]
    exact Set.image_univ
  · exact ((idealKilled_subschemePushforward J N).of_iso e.symm).generic_stalk

end FLT.Mazur.FCurve
