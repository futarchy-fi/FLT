/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientAffineStructureMap
public import FLT.Mazur.PointLocalizedObstructionVanishing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Local obstruction vanishing for actual affine coefficient models

Flatness of the recovered affine chart over the original base kills the whole
fixed local maximal-ideal obstruction after finite coefficient enlargement.
Every ring, map and colimit here is constructed from that chart's pullbacks;
flatness of the finite chart model is not an input.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CoefficientAffineLocalObstruction
open Approximation CoefficientAffineRingSystem CoefficientAffineStructureMap
open PointLocalizedRingDiagram PointLocalizedRingMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A : Type u} [CommRing A] (R : Subalgebra ℤ A)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [IsAffine Y]

/-- Flatness is needed only after recovering the chart over the original base. -/
theorem originalMap_flat
    [Flat (pullback.snd q (Spec.map (CommRingCat.ofHom R.val.toRingHom)))] :
    (originalMap R q).Flat :=
  (RingHom.Flat.of_bijective
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.bijective).comp
      (pullback.snd q (Spec.map (CommRingCat.ofHom R.val.toRingHom))).flat_appTop

variable (Q : Ideal (CoefficientAffineRingSystem.cocone R q).pt) [Q.IsPrime]

/-- The constructed local structure map on the original coefficient index. -/
abbrev localStructureMap (i : CoefficientStage R) :=
  stageMap (coefficientStageCocone R) (CoefficientAffineRingSystem.cocone R q)
    (structureMap R q) (originalMap R q) (cocone_square R q) Q i

/-- A single later coefficient stage kills every original local maximal-ideal obstruction. -/
theorem exists_vanishing_stage [Algebra.FiniteType ℤ R] [LocallyOfFiniteType q]
    [Flat (pullback.snd q (Spec.map (CommRingCat.ofHom R.val.toRingHom)))]
    (i : CoefficientStage R) :
    ∃ (j : CoefficientStage R) (g : i ⟶ j), ∀ (k : CoefficientStage R) (e : j ⟶ k),
      let _ := (localStructureMap R q Q i).toAlgebra
      let _ := (localStructureMap R q Q k).toAlgebra
      ∀ z : IdealTensorKernel.obstruction (S := CoefficientAffineRingSystem.LocalRing R q Q i)
        (IsLocalRing.maximalIdeal
          (Stage (coefficientStageCocone R) (Q.comap (originalMap R q)) i)),
      IdealTensorKernel.transition
        (transition (coefficientStageCocone R) (Q.comap (originalMap R q)) (g ≫ e))
        (transition (CoefficientAffineRingSystem.cocone R q) Q (g ≫ e))
        (PointLocalizedObstructionVanishing.stage_square (coefficientStageCocone R)
          (CoefficientAffineRingSystem.cocone R q) (structureMap R q) (originalMap R q)
          (cocone_square R q) Q (g ≫ e))
        (IsLocalRing.maximalIdeal
          (Stage (coefficientStageCocone R) (Q.comap (originalMap R q)) i)) z.val = 0 := by
  let _ : IsNoetherianRing ((coefficientStageDiagram R).obj i) :=
    Algebra.FiniteType.isNoetherianRing ℤ i.val
  exact PointLocalizedObstructionVanishing.exists_maximal_obstruction_vanishing_of_flat
    (coefficientStageCocone R) (CoefficientAffineRingSystem.cocone R q)
    (coefficientStageIsColimit R) (CoefficientAffineRingSystem.isColimit R q)
    (structureMap R q) (originalMap R q) (cocone_square R q) Q (originalMap_flat R q) i

end FLT.Mazur.CoefficientAffineLocalObstruction
