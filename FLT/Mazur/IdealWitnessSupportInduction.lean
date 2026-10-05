/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericWitnessIdealVanishing
public import FLT.Mazur.CoherentGeometricFiltration

/-!
# Support induction for eventual twist vanishing

The finite-rank witness step and the actual geometric ideal filtration give
Noetherian support induction. Witnesses must have the prescribed support and
generic annihilator, with vanishing for all their ideal multiples. This is
the cohomological specialization of Stacks 01YM used in finite descent.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ZeroObject
open Scheme.Modules FLT.Mazur.GlobalIdealPower
open FLT.Mazur.CoherentGenericIdealEmbedding

universe u

namespace FLT.Mazur.FCurve
open CoherentDevissage ModuleSheafTensor ModuleSheafTensorCurrying ModuleLineBundleTensorPullback

local instance supportInductionHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- A zero coefficient has vanishing cohomology in every twist. -/
theorem EventualTwistVanishing.of_isZero {X : Scheme.{u}} (L M : X.Modules)
    (hM : IsZero M) : EventualTwistVanishing L M := by
  refine ⟨0, fun n _ q ↦ ?_⟩
  let F := tensoring (tensorPower L n) ⋙ moduleRingHFunctor (RingHom.id Γ(X, ⊤)) (q + 1)
  exact ModuleCat.isZero_iff_subsingleton.mp (F.map_isZero hM)

/-- Generic witnesses with vanishing ideal multiples imply vanishing for all coherent sheaves
inside the chosen support bound. -/
theorem eventualTwistVanishing_of_supported_witnesses {X : Scheme.{u}} [IsNoetherian X]
    {L : X.Modules} (hL : LocallyFreeRankOne L) (T : Set X)
    (hwitness : ∀ (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)), (Z : Set X) ⊆ T →
      letI := reducedClosedSubscheme_isIntegral Z hZ
      ∃ G : X.Modules, G.IsFinitePresentation ∧
        support G = (Z : Set X) ∧
        StalkAnnihilated G ((reducedClosedSubschemeι Z) (genericPoint (reducedClosedSubscheme Z))) ∧
        ∀ K : X.IdealSheafData, EventualTwistVanishing L (multiple K G))
    (M : X.Modules) [M.IsFinitePresentation] (hM : support M ⊆ T) :
    EventualTwistVanishing L M := by
  have hzero : EventualTwistVanishing L (0 : X.Modules) :=
    EventualTwistVanishing.of_isZero L 0 (isZero_zero _)
  have h : ∀ Z : Closeds X, (Z : Set X) ⊆ T →
      ∀ N : X.Modules, N.IsFinitePresentation → support N ⊆ Z →
        EventualTwistVanishing L N := by
    intro Z
    induction Z using closed_induction with
    | step Z ih =>
      intro hZT N hN hNZ
      apply geometric_ideal_criterion
        (fun h p₁ p₃ ↦ EventualTwistVanishing.middle hL _ h.shortExact p₁ p₃)
        hzero (Z : Set X) _ N hNZ
      intro W hW hWZ I hI
      rcases lt_or_eq_of_le (show W ≤ Z from hWZ) with hlt | rfl
      · have hcoh := GenericIdealSupport.closedIdeal_coherent
          (Scheme.IdealSheafData.vanishingIdeal W) I
        apply ih W hlt (hWZ.trans hZT) _ hcoh
        simpa [Scheme.IdealSheafData.range_subschemeι] using
          (support_closedPushforward_subset_range
            (Scheme.IdealSheafData.vanishingIdeal W).subschemeι (idealModule I))
      · obtain ⟨G, hG, hs, hAnn, hideal⟩ := hwitness W hW hZT
        let J := Scheme.IdealSheafData.vanishingIdeal W
        let : IsIntegral J.subscheme := reducedClosedSubscheme_isIntegral W hW
        apply ideal_vanishing_of_generic_witness hL J G hAnn
          (by simpa [J, Scheme.IdealSheafData.range_subschemeι] using hs) _ hideal I hI
        intro F hF hsmall
        have hFZ : closedSupport F < W := by
          change support F ⊂ (W : Set X)
          simpa [J, Scheme.IdealSheafData.range_subschemeι] using hsmall
        exact ih (closedSupport F) hFZ
          ((show support F ⊆ (W : Set X) from hFZ.le).trans hZT) F hF (Set.Subset.refl _)
  exact h (closedSupport M) hM M inferInstance (Set.Subset.refl _)

end FLT.Mazur.FCurve
