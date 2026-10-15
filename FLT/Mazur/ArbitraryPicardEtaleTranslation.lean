/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricAcyclicEtaleTranslation
public import FLT.Mazur.SimultaneousSmoothHilbertParameters

/-!
# Constructed original étale translations for arbitrary geometric classes

No extension of the input class to the original coefficient base is required.
The translation is an actual original class on an affine étale scheme, and
the original fixed-degree Hilbert chart represents the prescribed class at
one constructed geometric lift. Other independent lifts are not discarded
or asserted to satisfy the same acyclicity condition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve OrderedCurvePower
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of R))
  (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t)))

include hL in
/-- Every geometric original class has a constructed original affine étale acyclic translation. -/
theorem exists_arbitraryPicard_etale_translation :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V)) (v : Over.mk t ⟶ V),
      IsAffine V.left ∧ Etale V.hom ∧
      s * (relativeFppfSheaf f).obj.map v.op c ∈
        (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk t)) := by
  obtain ⟨d, i, v, hv⟩ := exists_simultaneous_smooth_acyclic_degree f hL t
    (fun _ : Fin 1 ↦ s)
  obtain ⟨V, r, z, hV, he, hz⟩ :=
    exists_etale_translation_of_geometric_acyclicity f d (smoothTranslationTest f (i 0))
      (smoothTranslationClass f hL.2.1 (i 0)) s (v 0) (hv 0)
  exact ⟨d, V, (relativeFppfSheaf f).obj.map r.op
    (smoothTranslationClass f hL.2.1 (i 0)), z, hV, he, hz⟩

/-- The constructed translation yields an original Hilbert map representing the prescribed class. -/
theorem exists_arbitraryPicard_etale_hilbert_lift :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (a : Over.mk t ⟶ variableHilbertTest f d V),
      IsAffine V.left ∧ Etale V.hom ∧
      (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c) = s := by
  obtain ⟨d, V, c, v, hV, he, hv⟩ := exists_arbitraryPicard_etale_translation f hL t s
  exact ⟨d, V, c, acyclicTranslationLift f hL d V c s v hv, hV, he,
    acyclicTranslationLift_class f hL d V c s v hv⟩

end FLT.Mazur.HilbertChart
