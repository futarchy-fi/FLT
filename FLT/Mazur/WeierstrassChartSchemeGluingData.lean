/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleChartCocycle
public import FLT.Mazur.PrincipalAffineRefinement
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Scheme charts and their triple intersections

The spectra of the integral cubic chart rings have explicit open overlap maps.
The product localization is identified with the categorical intersection, with
both projections given by the concrete coordinate restriction homomorphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j k l : Fin 3)

/-- The integral cubic chart with its j coordinate normalized. -/
abbrev chartScheme := Spec (.of (Coordinate W j))

/-- Its principal overlap with chart k. -/
abbrev overlapScheme := Spec (.of (Overlap W j k))

/-- The explicit principal open inclusion. -/
def overlapInclusion : overlapScheme W j k ⟶ chartScheme W j :=
  PrincipalAffineRefinement.inclusion (coord W j k)

instance overlapInclusion_isOpenImmersion : IsOpenImmersion (overlapInclusion W j k) :=
  IsOpenImmersion.of_isLocalization (coord W j k)

/-- The pairwise normalization as a scheme transition. -/
def chartTransition : overlapScheme W j k ⟶ overlapScheme W k j :=
  Spec.map (CommRingCat.ofHom (transition W j k).toRingHom)

/-- The entire triple intersection. -/
abbrev tripleScheme := Spec (.of (TripleOverlap W j k l))

/-- Its inclusion in the original chart. -/
def tripleInclusion : tripleScheme W j k l ⟶ chartScheme W j :=
  PrincipalAffineRefinement.inclusion (coord W j k * coord W j l)

instance tripleInclusion_isOpenImmersion : IsOpenImmersion (tripleInclusion W j k l) :=
  IsOpenImmersion.of_isLocalization (coord W j k * coord W j l)

/-- Projection of the triple intersection to the first pair. -/
def tripleFst : tripleScheme W j k l ⟶ overlapScheme W j k :=
  Spec.map (CommRingCat.ofHom (tripleLeft W j k l).toRingHom)

/-- Projection of the triple intersection to the second pair. -/
def tripleSnd : tripleScheme W j k l ⟶ overlapScheme W j l :=
  Spec.map (CommRingCat.ofHom (tripleRight W j k l).toRingHom)

/-- The first restriction has the original chart inclusion as composite. -/
theorem tripleFst_inclusion :
    tripleFst W j k l ≫ overlapInclusion W j k = tripleInclusion W j k l := by
  have he : (tripleLeft W j k l).comp
      (IsScalarTower.toAlgHom R (Coordinate W j) (Overlap W j k)) =
        IsScalarTower.toAlgHom R (Coordinate W j) (TripleOverlap W j k l) := by
    apply hom_ext
    intro i
    exact tripleLeft_coord W j k l i
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) he

/-- The second restriction has the same composite. -/
theorem tripleSnd_inclusion :
    tripleSnd W j k l ≫ overlapInclusion W j l = tripleInclusion W j k l := by
  have he : (tripleRight W j k l).comp
      (IsScalarTower.toAlgHom R (Coordinate W j) (Overlap W j l)) =
        IsScalarTower.toAlgHom R (Coordinate W j) (TripleOverlap W j k l) := by
    apply hom_ext
    intro i
    exact tripleRight_coord W j k l i
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) he

/-- The actual pullback is the principal open at the product of coordinates. -/
def triplePullbackIso :
    pullback (overlapInclusion W j k) (overlapInclusion W j l) ≅ tripleScheme W j k l :=
  IsOpenImmersion.isoOfRangeEq
    (pullback.fst _ _ ≫ overlapInclusion W j k) (tripleInclusion W j k l) (by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      change Set.range (PrincipalAffineRefinement.inclusion (coord W j k)) ∩
        Set.range (PrincipalAffineRefinement.inclusion (coord W j l)) =
        Set.range (PrincipalAffineRefinement.inclusion (coord W j k * coord W j l))
      rw [PrincipalAffineRefinement.range_inclusion, PrincipalAffineRefinement.range_inclusion,
        PrincipalAffineRefinement.range_inclusion, PrimeSpectrum.basicOpen_mul]
      rfl)

/-- The comparison preserves the common chart map. -/
theorem triplePullbackIso_hom_inclusion :
    (triplePullbackIso W j k l).hom ≫ tripleInclusion W j k l =
      pullback.fst _ _ ≫ overlapInclusion W j k :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

/-- The comparison preserves the first overlap projection. -/
theorem triplePullbackIso_hom_fst :
    (triplePullbackIso W j k l).hom ≫ tripleFst W j k l = pullback.fst _ _ := by
  rw [← cancel_mono (overlapInclusion W j k), Category.assoc, tripleFst_inclusion,
    triplePullbackIso_hom_inclusion]

/-- The comparison preserves the second overlap projection. -/
theorem triplePullbackIso_hom_snd :
    (triplePullbackIso W j k l).hom ≫ tripleSnd W j k l = pullback.snd _ _ := by
  rw [← cancel_mono (overlapInclusion W j l), Category.assoc, tripleSnd_inclusion,
    triplePullbackIso_hom_inclusion, pullback.condition]

end FLT.Mazur.WeierstrassIntegralChart
