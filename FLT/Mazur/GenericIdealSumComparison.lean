/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericIdealSupport
public import FLT.Mazur.EventualTwistVanishing

/-!
# Finite ideal sums at the generic point

Nonzero generic stalks force the constructed comparison rank to be positive.
An ideal is a retract of its nonempty finite sum, including after pushforward.
Comparable nonzero ideals induce generic isomorphisms on their finite sums.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.FCurve.CoherentDevissage
open FLT.Mazur.CommonIdealDirectSum FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.CoherentGenericIdealEmbedding FLT.Mazur.CoherentGenericCoordinates

universe u

namespace FLT.Mazur.GenericIdealSumComparison

variable {X Y : Scheme.{u}}

/-- The generic rank of the actual closed descent is positive on the witness support. -/
theorem comparison_rank_pos [IsLocallyNoetherian X] (J : X.IdealSheafData)
    [IsIntegral J.subscheme] (F : X.Modules) [F.IsFinitePresentation]
    (hF : StalkAnnihilated F (J.subschemeι (genericPoint J.subscheme)))
    (hs : J.subschemeι (genericPoint J.subscheme) ∈ support F) :
    0 < Module.finrank J.subscheme.functionField
      ((CoherentClosedReduction.descent J F).presheaf.stalk (genericPoint J.subscheme)) := by
  have : Nontrivial (F.presheaf.stalk (J.subschemeι (genericPoint J.subscheme))) := by
    apply not_subsingleton_iff_nontrivial.mp
    exact fun h ↦ hs (AddCommGrpCat.isZero_iff_subsingleton.mpr h)
  have := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  have := coherent_stalk_finite (CoherentClosedReduction.descent J F)
    (genericPoint J.subscheme)
  let e := descentStalkAddEquiv J F hF
  have := e.symm.injective.nontrivial
  exact Module.finrank_pos

/-- Retraction to one coordinate survives any scheme pushforward. -/
theorem vanishing_of_sum (g : Y ⟶ X) (L : X.Modules) (I : Y.IdealSheafData)
    (r : ℕ) (hr : 0 < r)
    (h : EventualTwistVanishing L ((pushforward g).obj (idealSum I r))) :
    EventualTwistVanishing L ((pushforward g).obj (idealModule I)) := by
  let k : ULift.{u} (Fin r) := ⟨⟨0, hr⟩⟩
  let i := Sigma.ι (fun _ : ULift.{u} (Fin r) ↦ idealModule I) k
  let p := Sigma.desc (fun _ : ULift.{u} (Fin r) ↦ 𝟙 (idealModule I))
  apply EventualTwistVanishing.retract ((pushforward g).map i) ((pushforward g).map p) _ h
  rw [← Functor.map_comp]
  simp [i, p]

/-- The coordinatewise map of finite sums induced by ideal containment. -/
def sumMap {I J : X.IdealSheafData} (h : I ≤ J) (r : ℕ) : idealSum I r ⟶ idealSum J r :=
  Limits.Sigma.map (fun _ : ULift.{u} (Fin r) ↦ idealMap h)

/-- The coproduct comparison identifies the stalk map with the sum of stalk maps. -/
lemma sumMap_stalk [IsIntegral X] {I J : X.IdealSheafData}
    (h : I ≤ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (r : ℕ) :
    IsIso ((stalk (genericPoint X)).map (sumMap h r)) := by
  let F := stalk (genericPoint X)
  have := idealMap_generic_isIso h hI hJ
  have he : sigmaComparison F (fun _ : ULift.{u} (Fin r) ↦ idealModule I) ≫
      F.map (sumMap h r) =
      Limits.Sigma.map (fun _ : ULift.{u} (Fin r) ↦ F.map (idealMap h)) ≫
        sigmaComparison F (fun _ : ULift.{u} (Fin r) ↦ idealModule J) := by
    apply Sigma.hom_ext
    intro k
    simp only [ι_comp_sigmaComparison_assoc, sumMap, Sigma.ι_map_assoc,
      ι_comp_sigmaComparison, ← F.map_comp, Sigma.ι_map]
  have : IsIso (sigmaComparison F (fun _ : ULift.{u} (Fin r) ↦ idealModule I) ≫
      F.map (sumMap h r)) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left
    (sigmaComparison F (fun _ : ULift.{u} (Fin r) ↦ idealModule I)) _

end FLT.Mazur.GenericIdealSumComparison
