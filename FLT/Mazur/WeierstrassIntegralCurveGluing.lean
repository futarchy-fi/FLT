/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartSchemeGluingData

/-!
# Gluing the integral projective Weierstrass curve

The explicit principal overlaps and their normalization cocycle define scheme
gluing data over any commutative coefficient ring. No smoothness hypothesis is
needed to assemble the three affine cubic charts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j k l : Fin 3)

/-- A chart's self-overlap is the entire chart. -/
instance overlapInclusion_self_isIso : IsIso (overlapInclusion W j j) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  change Set.range (PrincipalAffineRefinement.inclusion (coord W j j)) = Set.univ
  rw [PrincipalAffineRefinement.range_inclusion, coord_self, PrimeSpectrum.basicOpen_one]
  rfl

/-- The self-transition fixes the whole self-overlap scheme. -/
theorem chartTransition_self : chartTransition W j j = 𝟙 _ := by
  unfold chartTransition
  rw [transition_self]
  exact Spec.map_id _

/-- The cyclic transition between the spectra of the triple intersections. -/
def tripleChartTransition : tripleScheme W j k l ⟶ tripleScheme W k l j :=
  Spec.map (CommRingCat.ofHom (tripleTransition W j k l).toRingHom)

/-- The triple scheme transition recovers the pairwise transition. -/
theorem tripleChartTransition_snd :
    tripleChartTransition W j k l ≫ tripleSnd W k l j =
      tripleFst W j k l ≫ chartTransition W j k := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (tripleTransition_pair W j k l)

/-- The cyclic scheme transitions compose to the identity. -/
theorem tripleChartTransition_cocycle :
    tripleChartTransition W j k l ≫ tripleChartTransition W k l j ≫
      tripleChartTransition W l j k = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  calc
    _ = Spec.map (CommRingCat.ofHom (AlgHom.id R (TripleOverlap W j k l)).toRingHom) :=
      congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
        (tripleTransition_cocycle W j k l)
    _ = 𝟙 _ := Spec.map_id _

/-- The same transition on the actual categorical pullbacks used by gluing. -/
def chartPullbackTransition :
    pullback (overlapInclusion W j k) (overlapInclusion W j l) ⟶
      pullback (overlapInclusion W k l) (overlapInclusion W k j) :=
  (triplePullbackIso W j k l).hom ≫ tripleChartTransition W j k l ≫
    (triplePullbackIso W k l j).inv

/-- The required factorization for the gluing datum. -/
theorem chartPullbackTransition_snd :
    chartPullbackTransition W j k l ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ chartTransition W j k := by
  have hs : (triplePullbackIso W k l j).inv ≫ pullback.snd _ _ =
      tripleSnd W k l j := by
    rw [← triplePullbackIso_hom_snd W k l j, Iso.inv_hom_id_assoc]
  simp only [chartPullbackTransition, Category.assoc, hs, tripleChartTransition_snd]
  rw [← Category.assoc, triplePullbackIso_hom_fst]

/-- Conjugating the explicit cocycle gives the categorical gluing cocycle. -/
theorem chartPullbackTransition_cocycle :
    chartPullbackTransition W j k l ≫ chartPullbackTransition W k l j ≫
      chartPullbackTransition W l j k = 𝟙 _ := by
  simp only [chartPullbackTransition, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (tripleChartTransition W k l j),
    ← Category.assoc (tripleChartTransition W j k l),
    tripleChartTransition_cocycle, Category.id_comp, Iso.hom_inv_id]

/-- Explicit integral cubic chart gluing data, including the actual cocycle proof. -/
def integralCurveGlueData : Scheme.GlueData.{u} where
  J := ULift.{u} (Fin 3)
  U := fun j => chartScheme W j.down
  V := fun p => overlapScheme W p.1.down p.2.down
  f := fun j k => overlapInclusion W j.down k.down
  t := fun j k => chartTransition W j.down k.down
  t_id := fun j => chartTransition_self W j.down
  t' := fun j k l => chartPullbackTransition W j.down k.down l.down
  t_fac := fun j k l => chartPullbackTransition_snd W j.down k.down l.down
  cocycle := fun j k l => chartPullbackTransition_cocycle W j.down k.down l.down
  f_open := fun _ _ => inferInstance

/-- The integral projective cubic assembled from its three affine charts. -/
def integralCurve : Scheme := (integralCurveGlueData W).glued

/-- Inclusion of each cubic chart in the glued curve. -/
def integralCurveChart : chartScheme W j ⟶ integralCurve W :=
  (integralCurveGlueData W).ι ⟨j⟩

instance integralCurveChart_isOpenImmersion : IsOpenImmersion (integralCurveChart W j) :=
  inferInstanceAs (IsOpenImmersion ((integralCurveGlueData W).ι ⟨j⟩))

/-- The three charts cover the glued curve. -/
theorem integralCurveChart_cover (x : integralCurve W) :
    ∃ (j : Fin 3) (y : chartScheme W j), integralCurveChart W j y = x := by
  obtain ⟨j, y, hy⟩ := (integralCurveGlueData W).ι_jointly_surjective x
  exact ⟨j.down, y, hy⟩

/-- The original normalized transitions agree in the glued curve. -/
theorem integralCurveChart_compatibility :
    chartTransition W j k ≫ overlapInclusion W k j ≫ integralCurveChart W k =
      overlapInclusion W j k ≫ integralCurveChart W j :=
  (integralCurveGlueData W).glue_condition ⟨j⟩ ⟨k⟩

end FLT.Mazur.WeierstrassIntegralChart
