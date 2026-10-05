/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ComaximalIdealSequence
public import FLT.Mazur.ModuleCohomologyVanishing
public import FLT.Mazur.ModuleLineTensorExact

/-!
# Lifting sections of a twisted ideal quotient

Vanishing of the actual kernel H¹ makes the map on global sections
surjective. Applied to comaximal ideals and a line twist, this lifts every
section of (O/J) ⊗ L to an actual section of I ⊗ L.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace FLT.Mazur.FCurve

local instance sectionLiftHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}}

/-- H¹ vanishing of the kernel lifts every global quotient section. -/
theorem globalSections_surjective_of_kernel_h1 (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Subsingleton (ModuleH S.X₁ 1)] :
    Function.Surjective (S.g.app ⊤) := by
  have hAb : (moduleAbelianComplex S).ShortExact :=
    CoherentDevissage.moduleToSheaf_shortExact hS
  have he : Function.Exact (moduleHMap S.g 0) (moduleHConnecting S hAb 0) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' hAb 0 1 rfl)
  intro t
  obtain ⟨s, hs⟩ := (he ((moduleH0Equiv S.X₃).symm t)).mp (Subsingleton.elim _ _)
  refine ⟨moduleH0Equiv S.X₂ s, ?_⟩
  rw [← moduleH0Equiv_naturality, hs, LinearEquiv.apply_symm_apply]

open CoherentIdealIntersection ModuleSheafTensor ModuleSheafTensorCurrying

/-- Comaximal ideal reduction, tensored with a line, is short exact. -/
theorem comaximalLineSequence_shortExact (I J : X.IdealSheafData)
    (hIJ : I ⊔ J = ⊤) {L : X.Modules} (hL : LocallyFreeRankOne L) :
    ((reductionComplex I J).map (tensoring L)).ShortExact :=
  ModuleLineTensorExact.shortExact _ (reductionComplex_shortExact I J hIJ) L hL

/-- The actual ideal-tensor map lifts all sections when its intersection-twist H¹ vanishes. -/
theorem comaximalLineReduction_surjective (I J : X.IdealSheafData)
    (hIJ : I ⊔ J = ⊤) {L : X.Modules} (hL : LocallyFreeRankOne L)
    [Subsingleton (ModuleH (tensor (idealModule (I ⊓ J)) L) 1)] :
    Function.Surjective ((ModuleSheafTensor.map (reduction I J) (𝟙 L)).app ⊤) := by
  let S := (reductionComplex I J).map (tensoring L)
  have : Subsingleton (ModuleH S.X₁ 1) :=
    inferInstanceAs (Subsingleton (ModuleH (tensor (idealModule (I ⊓ J)) L) 1))
  exact globalSections_surjective_of_kernel_h1 S (comaximalLineSequence_shortExact I J hIJ hL)

end FLT.Mazur.FCurve
