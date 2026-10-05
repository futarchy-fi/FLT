/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericIdealInjection
public import FLT.Mazur.ClosedSubsets
public import FLT.Mazur.FiniteSupportClosedDescent

/-!
# Comparing a line with the structure sheaf on an integral curve

Extend a trivialization at the generic point through a common ideal power.
The resulting coherent sheaf embeds into both the line and the structure
sheaf, with finite-support cokernels on an integral curve.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open CoherentDevissage FLT.Mazur.GenericIdealInjection
open FLT.Mazur.CoherentGenericCoordinates
open FLT.Mazur.CommonIdealDirectSum FLT.Mazur.CoherentIdealIntersection

variable {X : Scheme} [IsNoetherian X] [IsIntegral X]

/-- A coherent cokernel missing the generic point of a curve has finite support. -/
theorem finite_cokernel_support_of_generic_isIso
    (hd : topologicalKrullDim X ≤ 1) {M N : X.Modules}
    [M.IsFinitePresentation] [N.IsFinitePresentation] (a : M ⟶ N)
    [IsIso ((stalk (genericPoint X)).map a)] : (support (cokernel a)).Finite := by
  have := coherent_cokernel a
  apply finite_of_isClosed_of_ne_univ hd (isClosed_support _)
  intro he
  exact ((isIso_stalk_iff_notMem_support a (genericPoint X)).mp inferInstance).2
    (he.symm ▸ Set.mem_univ _)

/-- A generic trivialization constructs coherent comparisons with finite-support errors. -/
theorem exists_line_structure_comparison (hd : topologicalKrullDim X ≤ 1)
    {L : X.Modules} (hL : LocallyFreeRankOne L) :
    ∃ (M : X.Modules) (a : M ⟶ structureModule X) (b : M ⟶ L),
      M.IsFinitePresentation ∧ Mono a ∧ Mono b ∧
        (support (cokernel a)).Finite ∧ (support (cokernel b)).Finite := by
  have := hL.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  obtain ⟨U, hx, ⟨e⟩⟩ := hL (genericPoint X)
  let t : finiteFree X 1 ≅ structureModule X :=
    coproductUniqueIso (fun _ : ULift (Fin 1) ↦ structureModule X)
  let g : (finiteFree X 1).restrict U.ι ⟶ L.restrict U.ι :=
    (restrictFunctor U.ι).map t.hom ≫ (restrictUnitIso U.ι).hom ≫ e.inv
  have : IsIso g := by dsimp [g]; infer_instance
  obtain ⟨n, b, hb⟩ := exists_sum_extension U 1 L g
  let I := comparisonIdeal U ^ n
  have hi := sumInclusion_comparison_isIso U n 1
  have hbU : IsIso ((restrictFunctor U.ι).map b) := by rw [hb]; infer_instance
  have hbη := stalk_isIso_of_restrict b U _ hx
  have hbMono := mono_of_generic_mono I 1 b
  let a : idealSum I 1 ⟶ structureModule X := sumInclusion I 1 ≫ t.hom
  have : Mono a := by dsimp [a]; infer_instance
  have haU : IsIso ((restrictFunctor U.ι).map a) := by
    dsimp [a]
    rw [Functor.map_comp]
    infer_instance
  have haη := stalk_isIso_of_restrict a U _ hx
  exact ⟨idealSum I 1, a, b, inferInstance, inferInstance, inferInstance,
    finite_cokernel_support_of_generic_isIso hd a,
    finite_cokernel_support_of_generic_isIso hd b⟩

end FLT.Mazur.FCurve
