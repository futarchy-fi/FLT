/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalPicardEtaleAcyclicTranslation
public import FLT.Mazur.AffineHilbertConstructedGeometricRetention

/-!
# Constructed original full fibers for globally defined Picard classes

A global original Picard section constructs an affine étale translation and
an original affine Hilbert chart whose full envelope fiber contains its
geometric restriction. Both all-branch acyclicity and chart retention are
outputs. No claim is made for classes having no original global extension.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (s : (relativeFppfSheaf f).obj.obj (op (Over.mk (𝟙 (Spec (.of R))))))
  {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ Spec (.of R))

/-- Global original classes construct original affine full fibers without branch hypotheses. -/
theorem exists_globalPicard_affine_full_fiber :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A),
      IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left,
      let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) =
        (relativeFppfSheaf f).obj.map (Over.homMk t).op s ∧
      b.left (default : Spec (.of K)) ∈ fullEnvelopeLocus f hL d V c k := by
  obtain ⟨d, V, c, v, hV, he, hA⟩ :=
    exists_globalPicard_etale_acyclic_translation f hL s t
  obtain ⟨A, k, b, hAf, hk, _, hs, hb⟩ :=
    exists_affine_full_fiber_of_geometric_acyclicity f hL d V c
      ((relativeFppfSheaf f).obj.map (Over.homMk t).op s) v hA
  exact ⟨d, V, c, A, k, b, hV, he, hAf, hk, hs, hb⟩

end FLT.Mazur.HilbertChart.AffineRestriction
