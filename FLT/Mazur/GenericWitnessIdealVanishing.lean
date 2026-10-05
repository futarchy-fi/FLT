/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericIdealSumComparison
public import FLT.Mazur.IdealPowerVanishingTransfer

/-!
# Vanishing of ideal factors from a finite-rank generic witness

A common ideal intersection compares a finite sum with the witness. Reverse
comparison transfers eventual vanishing to this sum; a retraction then gives
one ideal, and the smaller-support quotient gives every other nonzero ideal.
No generic-rank-one assumption is imposed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.GlobalIdealPower
open FLT.Mazur.CommonIdealDirectSum FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.CoherentGenericIdealEmbedding FLT.Mazur.GenericIdealSumComparison

universe u

namespace FLT.Mazur.FCurve
open CoherentDevissage

/-- Ideal-multiple vanishing for one nonzero generic witness controls every ideal factor. -/
theorem ideal_vanishing_of_generic_witness {X : Scheme.{u}} [IsNoetherian X]
    {L : X.Modules} (hL : LocallyFreeRankOne L) (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (G : X.Modules) [G.IsFinitePresentation]
    (hAnn : StalkAnnihilated G (J.subschemeι (genericPoint J.subscheme)))
    (hs : support G = Set.range J.subschemeι)
    (hsmall : ∀ N : X.Modules, N.IsFinitePresentation →
      support N ⊂ Set.range J.subschemeι → EventualTwistVanishing L N)
    (hideal : ∀ K : X.IdealSheafData, EventualTwistVanishing L (multiple K G))
    (I' : J.subscheme.IdealSheafData) (hI' : I' ≠ ⊥) :
    EventualTwistVanishing L ((pushforward J.subschemeι).obj (idealModule I')) := by
  obtain ⟨I, hI, f, hseq, hf, _, _⟩ :=
    GenericIdealSupport.exists_supported_embedding J G hAnn hs.le
  have hf' : IsIso ((stalk (J.subschemeι (genericPoint J.subscheme))).map f) :=
    (mem_comparisonOpen_iff f _).mp hf
  let r := Module.finrank J.subscheme.functionField
    ((CoherentClosedReduction.descent J G).presheaf.stalk (genericPoint J.subscheme))
  have hr : 0 < r := comparison_rank_pos J G hAnn (hs.symm ▸ ⟨genericPoint _, rfl⟩)
  have hII' := intersection_ne_bot I I' hI hI'
  let a := sumMap (inf_le_left : I ⊓ I' ≤ I) r
  have ha : IsIso ((stalk (genericPoint J.subscheme)).map a) :=
    sumMap_stalk _ hII' hI r
  have := closed_map_stalk_isIso J.subschemeι a (genericPoint J.subscheme)
  let b := (pushforward J.subschemeι).map a ≫ f
  have hb : IsIso ((stalk (J.subschemeι (genericPoint J.subscheme))).map b) := by
    dsimp only [b]
    rw [Functor.map_comp]
    infer_instance
  have hv : EventualTwistVanishing L
      ((pushforward J.subschemeι).obj (idealSum (I ⊓ I') r)) :=
    eventualTwistVanishing_of_generic_comparison hL b
      (J.subschemeι (genericPoint J.subscheme)) (Set.range J.subschemeι)
      ⟨genericPoint _, rfl⟩
      (support_closedPushforward_subset_range _ _) hs.le hsmall hideal
  have hi := vanishing_of_sum J.subschemeι L (I ⊓ I') r hr hv
  let c := pushedIdealMap J.subschemeι (inf_le_right : I ⊓ I' ≤ I')
  have hc := pushedIdealSequence J.subschemeι (inf_le_right : I ⊓ I' ≤ I')
  exact EventualTwistVanishing.middle hL (ShortComplex.cokernelSequence c) hc.shortExact
    hi (hsmall _ hc.finite₃ (pushed_quotient_support_ssubset J.subschemeι _ hII' hI'))

end FLT.Mazur.FCurve
