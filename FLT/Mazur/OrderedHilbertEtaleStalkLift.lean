/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothEtaleStalkLift
public import FLT.Mazur.OrderedHilbertEtaleResidueLift
public import FLT.Mazur.VariableHilbertEtaleRelation

/-!
# Full ordered Hilbert charts through arbitrary residue-rational points

The original ordered parameter and Picard class lift to a constructed étale
translation test. Its full relation has étale projections, including pairs
with distinct translation-base maps. This is local chart construction, not
scheme effectivity or coverage by these charts at all geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f] [IsProper f]
  [Flat f] [GeometricallyIntegral f]
  (i : SmoothHilbertTranslationIndex) (φ : R →+* K) (hφ : φ.SurjectiveOnStalks)
  (x : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ smoothHilbertTest f i)

include hφ in
/-- The whole original Hilbert point lifts after a constructed étale change of translation base. -/
theorem exists_orderedHilbert_etale_stalk_lift :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i.1)
      (y : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ variableHilbertTest f i.2 E),
      Etale E.hom ∧ y ≫ baseMarkedChartChange f b i.2 = x := by
  let xbase := x ≫ variableHilbertBase f i.2 (smoothTranslationTest f i.1)
  obtain ⟨E, e, v, z, he, hv, hz, hvz⟩ := SmoothEtaleStalkLift.exists_lift
    (smoothTranslationTest f i.1).hom φ hφ xbase.left (Over.w xbase)
  let b : Over.mk e ⟶ smoothTranslationTest f i.1 := Over.homMk v hv
  let a : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ Over.mk e := Over.homMk z hz
  have ha : a ≫ b = xbase := Over.OverMorphism.ext hvz
  refine ⟨Over.mk e, b,
    variableHilbertLift f i.2 _ a (x ≫ variableHilbertParameter f i.2 _), he, ?_⟩
  apply prod.hom_ext
  · change _ ≫ variableHilbertBase f i.2 _ = _
    rw [Category.assoc, baseMarkedChartChange_base, ← Category.assoc]
    exact (congrArg (fun k ↦ k ≫ b) (prod.lift_fst _ _)).trans ha
  · change _ ≫ variableHilbertParameter f i.2 _ = _
    rw [Category.assoc, baseMarkedChartChange_parameter]
    exact prod.lift_snd _ _

variable {L : X.Modules} (hL : AmpleLineBundle L)

include hφ in
/-- Construct an original-class chart with its entire étale scheme relation at the given point. -/
theorem exists_orderedHilbert_etale_stalk_chart :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i.1)
      (y : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ variableHilbertTest f i.2 E),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      Etale E.hom ∧ y ≫ baseMarkedChartChange f b i.2 = x ∧
        variableHilbertPoint f i.2 hL E c _ y = smoothHilbertPoint f hL i _ x ∧
        Etale (variableChartRelationFst f hL i.2 E c).left ∧
        Etale (variableChartRelationSnd f hL i.2 E c).left := by
  obtain ⟨E, b, y, he, hy⟩ := exists_orderedHilbert_etale_stalk_lift f i φ hφ x
  let _ := he
  exact ⟨E, b, y, he, hy, orderedHilbert_etale_lift_class f i φ x hL b y hy,
    inferInstance, inferInstance⟩

/-- The chart construction applies to rational points over every original base residue field. -/
theorem exists_orderedHilbert_etale_prime_lift (p : Ideal R) [p.IsPrime]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) ⟶
      smoothHilbertTest f i) :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i.1)
      (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))) ⟶
        variableHilbertTest f i.2 E),
      Etale E.hom ∧ y ≫ baseMarkedChartChange f b i.2 = x :=
  exists_orderedHilbert_etale_stalk_lift f i _ p.surjectiveOnStalks_residueField x

end FLT.Mazur.HilbertChart
