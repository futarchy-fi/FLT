/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReducedDenseRestriction
public import FLT.Mazur.CurveClosedSupportAwayGenerics
public import FLT.Mazur.GenericLineTrivialization

/-!
# Line/structure comparisons on reduced curves

Trivialize the line over a dense open containing every generic point, then
extend through a power of its complement ideal. Reducedness proves injectivity;
the curve dimension bound makes both actual cokernels finitely supported.
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

variable {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]

/-- An arbitrary line on a reduced curve has coherent comparisons with finite-support errors. -/
theorem exists_reduced_line_structure_comparison (hd : topologicalKrullDim X ≤ 1)
    {L : X.Modules} (hL : LocallyFreeRankOne L) :
    ∃ (M : X.Modules) (a : M ⟶ structureModule X) (b : M ⟶ L),
      M.IsFinitePresentation ∧ Mono a ∧ Mono b ∧
        (support (cokernel a)).Finite ∧ (support (cokernel b)).Finite := by
  have := hL.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  obtain ⟨U, hg, hDense, ⟨e⟩⟩ := exists_line_trivialization_all_generics hL
  let t : finiteFree X 1 ≅ structureModule X :=
    coproductUniqueIso (fun _ : ULift (Fin 1) ↦ structureModule X)
  let g : (finiteFree X 1).restrict U.ι ⟶ L.restrict U.ι :=
    (restrictFunctor U.ι).map t.hom ≫ (restrictUnitIso U.ι).hom ≫ e.inv
  have : IsIso g := by dsimp [g]; infer_instance
  obtain ⟨n, b, hb⟩ := exists_sum_extension U 1 L g
  let I := comparisonIdeal U ^ n
  have hi := sumInclusion_comparison_isIso U n 1
  have hbU : IsIso ((restrictFunctor U.ι).map b) := by rw [hb]; infer_instance
  have hbMono : Mono b := ReducedDenseRestriction.mono_of_dense_stalk_mono U hDense I 1 b
    (fun x hx ↦ by have := stalk_isIso_of_restrict b U x hx; infer_instance)
  let a : idealSum I 1 ⟶ structureModule X := sumInclusion I 1 ≫ t.hom
  have : Mono a := by dsimp [a]; infer_instance
  have haU : IsIso ((restrictFunctor U.ι).map a) := by
    dsimp [a]
    rw [Functor.map_comp]
    infer_instance
  exact ⟨idealSum I 1, a, b, inferInstance, inferInstance, inferInstance,
    finite_cokernel_support_of_all_generic_isIso hd a
      (fun x hx ↦ stalk_isIso_of_restrict a U x (hg hx)),
    finite_cokernel_support_of_all_generic_isIso hd b
      (fun x hx ↦ stalk_isIso_of_restrict b U x (hg hx))⟩

end FLT.Mazur.FCurve
