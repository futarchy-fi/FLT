/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothTranslationOrbitOpen

/-!
# Smooth Hilbert parameters map to their actual quotient neighborhoods

The original orbit map descends along the smooth surjective parameter map.
Its descent is an open surjection from the actual parameter scheme onto the
actual quotient neighborhood. Injectivity is not asserted for smooth bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

omit [Smooth V.hom] in
/-- The parameter kernel pair maps to the original relation, with its actual endpoints. -/
def variableParameterKernelToRelation :
    pullback (variableSourceParameter f hL d V c) (variableSourceParameter f hL d V c) ⟶
      smoothHilbertRelation f hL :=
  smoothHilbertRelationLift f hL
    (pullback.fst _ _ ≫ variableSourceInclusion f hL d V c)
    (pullback.snd _ _ ≫ variableSourceInclusion f hL d V c) (by
      simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        variableSourceIntersection_class]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, pullback.condition])

omit [Smooth V.hom] in
/-- The first original endpoint of the parameter kernel-pair comparison. -/
theorem variableParameterKernelToRelation_fst :
    variableParameterKernelToRelation f hL d V c ≫ smoothHilbertRelationFst f hL =
      pullback.fst _ _ ≫ variableSourceInclusion f hL d V c :=
  smoothHilbertRelationLift_fst f hL _ _ _

omit [Smooth V.hom] in
/-- The second original endpoint of the parameter kernel-pair comparison. -/
theorem variableParameterKernelToRelation_snd :
    variableParameterKernelToRelation f hL d V c ≫ smoothHilbertRelationSnd f hL =
      pullback.snd _ _ ≫ variableSourceInclusion f hL d V c :=
  smoothHilbertRelationLift_snd f hL _ _ _

/-- Equal actual parameters give equal original orbits, without a monomorphism assumption. -/
theorem smoothTranslationSourceOrbitMap_eq_of_parameter
    (x y : (variableSourceIntersection f hL d V c).left)
    (h : (variableSourceParameter f hL d V c).left x =
      (variableSourceParameter f hL d V c).left y) :
    smoothTranslationSourceOrbitMap f hL d V c x =
      smoothTranslationSourceOrbitMap f hL d V c y := by
  have H := (IsPullback.of_hasPullback (variableSourceParameter f hL d V c)
    (variableSourceParameter f hL d V c)).map (Over.forget _)
  obtain ⟨z, hx, hy⟩ := Scheme.exists_preimage_of_isPullback H x y h
  apply Subtype.ext
  apply (projection_eq_iff (smoothHilbertEquivalenceRelation f hL) _ _).mpr
  refine ⟨(variableParameterKernelToRelation f hL d V c).left z, ?_, ?_⟩
  · exact (congrArg (fun k ↦ k.left z)
      (variableParameterKernelToRelation_fst f hL d V c)).trans
        (congrArg (variableSourceInclusion f hL d V c).left hx)
  · exact (congrArg (fun k ↦ k.left z)
      (variableParameterKernelToRelation_snd f hL d V c)).trans
        (congrArg (variableSourceInclusion f hL d V c).left hy)

/-- The actual continuous parameter projection used for descent. -/
def variableParameterContinuous :
    C((variableSourceIntersection f hL d V c).left, (variableHilbertTest f d V).left) :=
  ⟨(variableSourceParameter f hL d V c).left, (variableSourceParameter f hL d V c).left.continuous⟩

omit [Smooth V.hom] in
/-- The source-parameter map has the quotient topology for any translation base. -/
theorem variableParameter_isOpenQuotientMap :
    IsOpenQuotientMap (variableParameterContinuous f hL d V c) :=
  ⟨(variableSourceParameter f hL d V c).left.surjective,
    (variableParameterContinuous f hL d V c).continuous,
    (variableSourceParameter f hL d V c).left.isOpenMap⟩

/-- Descent gives the parameter's map to the actual original quotient neighborhood. -/
def smoothTranslationChartToOrbit :
    C((variableHilbertTest f d V).left, smoothTranslationOrbitOpen f hL d V c) :=
  (variableParameter_isOpenQuotientMap f hL d V c).isQuotientMap.lift
    (smoothTranslationSourceOrbitMap f hL d V c)
    (fun {_ _} h ↦ smoothTranslationSourceOrbitMap_eq_of_parameter f hL d V c _ _ h)

/-- The descended map recovers the original orbit on the common source. -/
theorem smoothTranslationChartToOrbit_parameter
    (x : (variableSourceIntersection f hL d V c).left) :
    smoothTranslationChartToOrbit f hL d V c ((variableSourceParameter f hL d V c).left x) =
      smoothTranslationSourceOrbitMap f hL d V c x :=
  congrArg (fun k : C(_, _) ↦ k x)
    ((variableParameter_isOpenQuotientMap f hL d V c).isQuotientMap.lift_comp
      (smoothTranslationSourceOrbitMap f hL d V c)
      (fun {_ _} h ↦ smoothTranslationSourceOrbitMap_eq_of_parameter f hL d V c _ _ h))

/-- The actual parameter covers every point of its original quotient neighborhood. -/
theorem smoothTranslationChartToOrbit_surjective :
    Function.Surjective (smoothTranslationChartToOrbit f hL d V c) := by
  intro z
  obtain ⟨x, rfl⟩ := smoothTranslationSourceOrbitMap_surjective f hL d V c z
  exact ⟨(variableSourceParameter f hL d V c).left x,
    smoothTranslationChartToOrbit_parameter f hL d V c x⟩

/-- The parameter map onto the actual quotient neighborhood is open. -/
theorem smoothTranslationChartToOrbit_isOpenMap :
    IsOpenMap (smoothTranslationChartToOrbit f hL d V c) := by
  apply IsOpenMap.of_comp (variableParameterContinuous f hL d V c).continuous
    (variableSourceParameter f hL d V c).left.surjective
  have he : (smoothTranslationChartToOrbit f hL d V c) ∘
      (variableSourceParameter f hL d V c).left =
        smoothTranslationSourceOrbitMap f hL d V c :=
    funext (smoothTranslationChartToOrbit_parameter f hL d V c)
  change IsOpenMap ((smoothTranslationChartToOrbit f hL d V c) ∘
    (variableSourceParameter f hL d V c).left)
  rw [he]
  exact smoothTranslationSourceOrbitMap_isOpenMap f hL d V c

end FLT.Mazur.HilbertChart
