/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXIncidenceSectionMaps
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry

/-!
# The two original marked points on the full incidence line

The slope evaluations at zero and minus the original tangent coefficient
are the same full-fiber sections already used by the initial conic components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)

/-- Evaluating the entire incidence line at zero gives the original first node. -/
theorem incidenceLineFirstSection_algebra :
    (aeval (0 : R)).comp (fiberIncidenceMap a c) = fullFirstIncidencePoint a c ha := by
  apply fiber_hom_ext a c
  · simp only [AlgHom.comp_apply, fiberIncidenceMap_t, map_zero, fullFirstIncidencePoint_t]
  · simp only [AlgHom.comp_apply, fiberIncidenceMap_v, aeval_X, fullFirstIncidencePoint_v]

/-- Evaluating at minus the original tangent coefficient gives the original second node. -/
theorem incidenceLineSecondSection_algebra :
    (aeval (-a)).comp (fiberIncidenceMap a c) = fullSecondIncidencePoint a c ha := by
  apply fiber_hom_ext a c
  · simp only [AlgHom.comp_apply, fiberIncidenceMap_t, map_zero, fullSecondIncidencePoint_t]
  · simp only [AlgHom.comp_apply, fiberIncidenceMap_v, aeval_X, fullSecondIncidencePoint_v]

/-- The first incidence marking is an equality on the full original fiber scheme. -/
@[reassoc] theorem incidenceLineFirstSection_spec :
    Spec.map (CommRingCat.ofHom (aeval (0 : R)).toRingHom) ≫ fiberIncidenceImmersion a c =
      Spec.map (CommRingCat.ofHom (fullFirstIncidencePoint a c ha).toRingHom) := by
  rw [fiberIncidenceImmersion, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (incidenceLineFirstSection_algebra a c ha)

/-- The opposite incidence marking keeps its original slope and tangent ordering. -/
@[reassoc] theorem incidenceLineSecondSection_spec :
    Spec.map (CommRingCat.ofHom (aeval (-a)).toRingHom) ≫ fiberIncidenceImmersion a c =
      Spec.map (CommRingCat.ofHom (fullSecondIncidencePoint a c ha).toRingHom) := by
  rw [fiberIncidenceImmersion, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (incidenceLineSecondSection_algebra a c ha)

end FLT.Mazur.WeierstrassModificationX
