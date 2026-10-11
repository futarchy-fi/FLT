/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertSeparableGeometricCoverage
public import FLT.Mazur.OrderedHilbertEtaleSeparableLift

/-!
# Constructed étale translation charts cover original geometric classes

A full-intersection representative supplies a separable ordered translation.
Its constructed étale residue neighborhood lifts the unrestricted Hilbert
parameter and retains the original class and the full étale relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
  [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (φ : R →+* k) (hφ : φ.SurjectiveOnStalks)

include hφ in
/-- Constructed étale translation bases cover each original geometric Picard class. -/
theorem exists_orderedHilbert_etale_geometric_chart
    (s : (relativeFppfSheaf f).obj.obj
      (op (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)))))) :
    ∃ (i : SmoothHilbertTranslationIndex) (E : Over (Spec (.of R)))
      (b : E ⟶ smoothTranslationTest f i.1)
      (q : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶
        variableHilbertTest f i.2 E),
      let c := (relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hL.2.1 i.1)
      Etale E.hom ∧ variableHilbertPoint f i.2 hL E c _ q = s ∧
        Etale (variableChartRelationFst f hL i.2 E c).left ∧
        Etale (variableChartRelationSnd f hL i.2 E c).left := by
  obtain ⟨i, y, p, hy, hp, hc⟩ :=
    exists_orderedHilbert_separable_geometric_point f hL φ s
  let T := Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ)))
  let S := Over.mk (Spec.map
    (CommRingCat.ofHom ((algebraMap k (separableClosure k K)).comp φ)))
  let x : S ⟶ smoothTranslationTest f i.1 := Over.homMk y hy
  let a : T ⟶ S := Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K))) (by
      dsimp only [S, T, Over.mk_hom]
      rw [← Spec.map_comp]
      congr 1)
  have hp' : p ≫ variableHilbertBase f i.2 _ = a ≫ x := Over.OverMorphism.ext hp
  obtain ⟨E, b, q, he, _, hq, hfst, hsnd⟩ :=
    exists_orderedHilbert_etale_separable_chart f i φ hφ x hL T a p hp'
  exact ⟨i, E, b, q, he, hq.trans hc, hfst, hsnd⟩

end FLT.Mazur.HilbertChart
