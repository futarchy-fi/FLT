/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricSimultaneousHilbertTranslation
public import FLT.Mazur.SmoothTranslationGeometricClass

/-!
# Common-degree parameters in the original smooth translation family

The actual simultaneous line translations are recovered in the fixed smooth
ordered parameter schemes. Every original geometric class acquires the same
Hilbert degree, with its translation coordinate retained. The chosen smooth
translation parameters may differ with the class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of R))

/-- Fixed original smooth translation schemes realize simultaneous acyclic degree conditions. -/
theorem exists_simultaneous_smooth_acyclic_degree {ι : Type}
    (s : ι → (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (i : ι → SmoothTranslationIndex)
      (v : ∀ j, Over.mk t ⟶ smoothTranslationTest f (i j)), ∀ j,
      s j * (relativeFppfSheaf f).obj.map (v j).op
        (smoothTranslationClass f hL.2.1 (i j)) ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  obtain ⟨d, M, hM⟩ := exists_simultaneous_geometric_acyclic_degree f hL t s
  have h (j : ι) := exists_smoothTranslation_geometric_class f hL t (M j)
  choose i v hv using h
  refine ⟨d, i, v, fun j ↦ ?_⟩
  rw [hv j]
  exact hM j

/-- Every supplied class has an actual original smooth Hilbert map of one common degree. -/
theorem exists_simultaneous_smooth_hilbert_lifts {ι : Type}
    (s : ι → (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (i : ι → SmoothTranslationIndex)
      (a : ∀ j, Over.mk t ⟶ variableHilbertTest f d (smoothTranslationTest f (i j))),
      ∀ j, (relativeFppfSheaf f).obj.map (a j).op
        (variableChartSection f hL d (smoothTranslationTest f (i j))
          (smoothTranslationClass f hL.2.1 (i j))) = s j := by
  obtain ⟨d, i, v, hv⟩ := exists_simultaneous_smooth_acyclic_degree f hL t s
  exact ⟨d, i, fun j ↦ acyclicTranslationLift f hL d _ _ (s j) (v j) (hv j),
    fun j ↦ acyclicTranslationLift_class f hL d _ _ (s j) (v j) (hv j)⟩

end FLT.Mazur.HilbertChart
