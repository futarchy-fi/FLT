/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleSectionRotation

/-!
# Rotation retains the original complete-base scalars

The cyclic action lies over the identity of the specified power-series base.
The degree-zero pullback formula therefore fixes every structural scalar in
the actual compatible section ring, including the original smoothing parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage rotation preserves its actual structural morphism. -/
@[reassoc] theorem stageRotation_toBase (m : ℕ) (a : ZMod n) :
    stageRotation R n h m a ≫ (family R m n h).hom = (family R m n h).hom :=
  PolygonInfinitesimal.rotation_toBase (Ring R m) (parameter R m) n h a

/-- The canonical cyclic section pullback fixes every original complete-base scalar. -/
theorem boundarySectionsRotation_series (m : ℕ) (a : ZMod n) (r : PowerSeries R) :
    boundarySectionsRotation R n h m a (boundarySeriesScalars R n h m r) =
      boundarySeriesScalars R n h m r := by
  let _ : IsIso (idealModulePullbackHom (boundaryIdeal R m n h) (stageRotation R n h m a)) :=
    idealModulePullbackHom_isIso_of_cartier _ (boundaryIdeal_cartier R m n h).1
      ((boundaryIdeal_stageRotation R n h m a).symm ▸ (boundaryIdeal_cartier R m n h).1)
  let e : (Scheme.Modules.pullback (stageRotation R n h m a)).obj (boundaryLine R m n h) ≅
      boundaryLine R m n h := divisorLinePullbackIsoOfEq _
    (boundaryIdeal_cartier R m n h).1 (boundaryIdeal_cartier R m n h).1
    (boundaryIdeal_stageRotation R n h m a)
  simp only [boundarySeriesScalars_eq]
  change SectionGradedLinePullback.ringHom (stageRotation R n h m a) e
    (of (boundaryLine R m n h) ⊤ 0 _) = of (boundaryLine R m n h) ⊤ 0 _
  rw [SectionGradedLinePullback.ringHom_of, SectionGradedLinePullback.sectionMap_zero]
  congr 1
  exact congrArg
    (fun k : (family R m n h).left ⟶ Spec (.of (PowerSeries R)) ↦
      k.appTop ((Scheme.ΓSpecIso (.of (PowerSeries R))).inv r))
    (stageRotation_toBase_assoc R n h m a (baseToSeries R m))

attribute [local irreducible] compatibleSectionRotation compatibleEval

/-- The original complete coefficient algebra is fixed by the constructed cyclic action. -/
theorem compatibleSectionRotation_algebraMap (a : ZMod n) (r : PowerSeries R) :
    compatibleSectionRotation R n h a
      (algebraMap (PowerSeries R) (CompatibleSections R n h) r) =
        algebraMap (PowerSeries R) (CompatibleSections R n h) r := by
  apply compatibleEval_ext R n h
  intro m
  rw [compatibleSectionRotation_eval, compatibleEval_algebraMap,
    boundarySectionsRotation_series]

/-- The cyclic action is an automorphism over the original complete coefficient algebra. -/
def compatibleSectionRotationAlgEquiv (a : ZMod n) :
    CompatibleSections R n h ≃ₐ[PowerSeries R] CompatibleSections R n h :=
  { compatibleSectionRotationEquiv R n h a with
    commutes' := compatibleSectionRotation_algebraMap R n h a }

end FLT.Mazur.PolygonInfinitesimalStages
