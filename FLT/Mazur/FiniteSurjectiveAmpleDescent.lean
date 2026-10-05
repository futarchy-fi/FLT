/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSurjectiveCoherentWitness
public import FLT.Mazur.IdealWitnessSupportInduction
public import FLT.Mazur.IdealCohomologyAmpleAnyBase

/-!
# Finite-surjective descent of ampleness

Stacks 0B5V for schemes proper over a Noetherian ring. Actual finite direct
images supply the coherent generic witnesses and ideal-multiple vanishing.
Support induction gives vanishing for every coherent coefficient, and the
arbitrary-base cohomological criterion proves ampleness downstairs.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.CoherentIdealIntersection

namespace FLT.Mazur.FCurve
open CoherentDevissage ModuleSheafTensor ModuleLineBundleTensorPullback

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X Y : Scheme}
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
  (g : Y ⟶ X) [IsFinite g] [Surjective g] {L : X.Modules}

include f

/-- An ample finite-surjective pullback kills all high twists of every coherent coefficient. -/
theorem finiteSurjective_eventualTwistVanishing (hL : LocallyFreeRankOne L)
    (hample : AmpleLineBundle ((pullback g).obj L))
    (M : X.Modules) [M.IsFinitePresentation] : EventualTwistVanishing L M := by
  have := Chow.source_isNoetherian f
  apply eventualTwistVanishing_of_supported_witnesses hL Set.univ _ M (Set.subset_univ _)
  intro Z hZ _
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  let : IsIntegral J.subscheme := reducedClosedSubscheme_isIntegral Z hZ
  obtain ⟨F, hF, hs, hAnn⟩ := finiteSurjective_exists_coherent_witness g J
  refine ⟨(pushforward g).obj F, finitePushforward_isFinitePresentation g F, ?_, hAnn, ?_⟩
  · simpa [J, Scheme.IdealSheafData.range_subschemeι] using hs
  · intro I
    exact finitePushforward_ideal_ample_coherent_vanishing f g hL hample F I

/-- Ampleness descends along a finite surjective map over a Noetherian affine base. -/
theorem ampleLineBundle_of_finiteSurjective (hL : LocallyFreeRankOne L)
    (hample : AmpleLineBundle ((pullback g).obj L)) : AmpleLineBundle L := by
  have := Chow.source_isNoetherian f
  apply ampleLineBundle_of_ideal_h1_vanishing_anyBase hL
  intro I
  have := idealModule_coherent I
  obtain ⟨n, hn⟩ := finiteSurjective_eventualTwistVanishing f g hL hample (idealModule I)
  exact ⟨max 1 n, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _),
    hn (max 1 n) (le_max_right _ _) 0⟩

/-- Stacks 0B5V: finite surjective pullback detects ampleness. -/
theorem ampleLineBundle_finiteSurjective_iff (hL : LocallyFreeRankOne L) :
    AmpleLineBundle ((pullback g).obj L) ↔ AmpleLineBundle L :=
  ⟨ampleLineBundle_of_finiteSurjective f g hL, fun h ↦ h.pullback_affine g⟩

end FLT.Mazur.FCurve
