/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricHilbertTranslation
public import FLT.Mazur.SmoothTranslationGeometricClass
public import FLT.Mazur.SmoothOrderedHilbertCharts

/-!
# The fixed smooth Hilbert charts lift every geometric sheaf section

The locally constructed Hilbert translation is first pulled back along a
split covering member. Geometric line recovery then replaces that actual
translation by a member of the fixed countable ordered family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  {k : Type} [Field k] [IsAlgClosed k] (g : Spec (.of k) ⟶ Spec (.of R))

include hB in
/-- Every original geometric sheaf section lifts to the fixed smooth chart family. -/
theorem exists_smoothHilbert_geometric_lift
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk g))) :
    ∃ (i : SmoothHilbertTranslationIndex) (a : Over.mk g ⟶ smoothHilbertTest f i),
      smoothHilbertPoint f hB i (Over.mk g) a = s := by
  obtain ⟨d, a, M, ha⟩ := exists_geometric_hilbert_translation f hB g s
  obtain ⟨i, b, hb⟩ := exists_smoothTranslation_geometric_class f hB g M
  refine ⟨⟨i, d⟩, variableHilbertLift f d _ b a, ?_⟩
  change variableHilbertPoint f d hB _ _ _ (variableHilbertLift f d _ b a) = s
  rw [variableHilbertPoint_lift, hb]
  exact ha

end FLT.Mazur.HilbertChart
