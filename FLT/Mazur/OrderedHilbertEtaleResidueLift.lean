/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedTranslationEtaleResidueLift
public import FLT.Mazur.BaseMarkedHilbertChartChange
public import FLT.Mazur.SmoothOrderedHilbertCharts

/-!
# Étale translation charts retain entire original Hilbert points

The constructed neighborhood of the ordered translation base lifts the
original Hilbert parameter without altering its degree or original Picard
class. The comparison recovers the entire original scheme-valued point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f] [IsProper f]
  [Flat f] [GeometricallyIntegral f]
  (i : SmoothHilbertTranslationIndex) (φ : R →+* K) (hφ : Function.Surjective φ)
  (x : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ smoothHilbertTest f i)

include hφ in
/-- Construct an étale translation chart lifting the entire original ordered Hilbert point. -/
theorem exists_orderedHilbert_etale_lift :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i.1)
      (y : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ variableHilbertTest f i.2 E),
      Etale E.hom ∧ y ≫ baseMarkedChartChange f b i.2 = x := by
  obtain ⟨E, b, a, he, ha⟩ := exists_orderedTranslation_etale_lift f i.1 φ hφ
    (x ≫ variableHilbertBase f i.2 _)
  refine ⟨E, b, variableHilbertLift f i.2 E a (x ≫ variableHilbertParameter f i.2 _),
    he, ?_⟩
  apply prod.hom_ext
  · change _ ≫ variableHilbertBase f i.2 _ = _
    rw [Category.assoc, baseMarkedChartChange_base, ← Category.assoc]
    exact (congrArg (fun k ↦ k ≫ b) (prod.lift_fst _ _)).trans ha
  · change _ ≫ variableHilbertParameter f i.2 _ = _
    rw [Category.assoc, baseMarkedChartChange_parameter]
    exact prod.lift_snd _ _

variable {L : X.Modules} (hL : AmpleLineBundle L)

/-- The recovered point has exactly its original Picard class on the original test. -/
theorem orderedHilbert_etale_lift_class {E : Over (Spec (.of R))}
    (b : E ⟶ smoothTranslationTest f i.1)
    (y : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ variableHilbertTest f i.2 E)
    (hy : y ≫ baseMarkedChartChange f b i.2 = x) :
    variableHilbertPoint f i.2 hL E
      ((relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)) _ y =
        smoothHilbertPoint f hL i _ x := by
  have h := baseMarkedChartChange_class f hL b
    (i.2, smoothTranslationClass f hL.2.1 i.1) y
  dsimp only [baseMarkedIndexChange, Prod.fst, Prod.snd] at h
  rw [hy] at h
  exact h.symm

end FLT.Mazur.HilbertChart
