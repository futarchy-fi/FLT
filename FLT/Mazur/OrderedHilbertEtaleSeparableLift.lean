/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedTranslationEtaleSeparableLift
public import FLT.Mazur.OrderedHilbertEtaleResidueLift
public import FLT.Mazur.VariableHilbertEtaleRelation

/-!
# Separable translation neighborhoods retain arbitrary Hilbert parameters

Construct one étale neighborhood through a separable residue translation.
Every original Hilbert parameter above that translation, on any further test,
lifts without changing its original point or Picard class. In particular its
Hilbert coordinates may be transcendental over the original residue field.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f] [IsProper f]
  [Flat f] [GeometricallyIntegral f]
  (i : SmoothHilbertTranslationIndex) (φ : R →+* k) (hφ : φ.SurjectiveOnStalks)
  (x : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶
    smoothTranslationTest f i.1)

include hφ in
/-- One constructed neighborhood recovers every Hilbert parameter over the residue translation. -/
theorem exists_orderedHilbert_etale_separable_neighborhood :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i.1)
      (z : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶ E),
      Etale E.hom ∧ z ≫ b = x ∧
        ∀ (T : Over (Spec (.of R)))
          (a : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))))
          (p : T ⟶ smoothHilbertTest f i),
          p ≫ variableHilbertBase f i.2 _ = a ≫ x →
          ∃ y : T ⟶ variableHilbertTest f i.2 E, y ≫ baseMarkedChartChange f b i.2 = p := by
  obtain ⟨E, b, z, he, hz⟩ := exists_orderedTranslation_etale_separable_lift f i.1 φ hφ x
  refine ⟨E, b, z, he, hz, ?_⟩
  intro T a p hp
  refine ⟨variableHilbertLift f i.2 E (a ≫ z) (p ≫ variableHilbertParameter f i.2 _), ?_⟩
  apply prod.hom_ext
  · change _ ≫ variableHilbertBase f i.2 _ = _
    rw [Category.assoc, baseMarkedChartChange_base, ← Category.assoc]
    calc
      _ = (a ≫ z) ≫ b := congrArg (fun t ↦ t ≫ b) (prod.lift_fst _ _)
      _ = _ := by rw [Category.assoc, hz]; exact hp.symm
  · change _ ≫ variableHilbertParameter f i.2 _ = _
    rw [Category.assoc, baseMarkedChartChange_parameter]
    exact prod.lift_snd _ _

variable {L : X.Modules} (hL : AmpleLineBundle L)

include hφ in
/-- The original class and full étale relation survive with arbitrary further Hilbert parameters. -/
theorem exists_orderedHilbert_etale_separable_chart
    (T : Over (Spec (.of R)))
    (a : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))))
    (p : T ⟶ smoothHilbertTest f i)
    (hp : p ≫ variableHilbertBase f i.2 _ = a ≫ x) :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i.1)
      (y : T ⟶ variableHilbertTest f i.2 E),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      Etale E.hom ∧ y ≫ baseMarkedChartChange f b i.2 = p ∧
        variableHilbertPoint f i.2 hL E c T y = smoothHilbertPoint f hL i T p ∧
        Etale (variableChartRelationFst f hL i.2 E c).left ∧
        Etale (variableChartRelationSnd f hL i.2 E c).left := by
  obtain ⟨E, b, _, he, _, h⟩ :=
    exists_orderedHilbert_etale_separable_neighborhood f i φ hφ x
  obtain ⟨y, hy⟩ := h T a p hp
  let _ := he
  refine ⟨E, b, y, he, hy, ?_, inferInstance, inferInstance⟩
  have hc := baseMarkedChartChange_class f hL b
    (i.2, smoothTranslationClass f hL.2.1 i.1) y
  dsimp only [baseMarkedIndexChange, Prod.fst, Prod.snd] at hc
  rw [hy] at hc
  exact hc.symm

end FLT.Mazur.HilbertChart
