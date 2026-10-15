/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricFiniteAllLiftTranslations
public import FLT.Mazur.GeometricTestResidueFactor

/-!
# Common all-lift translations over arbitrary original geometric tests

The input is an arbitrary whole geometric coefficient map. Its residue
factorization and the algebraic-closure embedding are constructed, then
removed from the output. One original affine étale test works at every
independent lift, for all prescribed classes and one common degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {B : X.Modules} (hB : AmpleLineBundle B)
  (q : Spec (.of K) ⟶ Spec (.of R))
  {n : ℕ} (s : Fin n → (relativeFppfSheaf f).obj.obj (op (Over.mk q)))

include hB in
/-- Common-degree original translations control all independent lifts of an arbitrary test. -/
theorem exists_arbitrary_geometric_all_lift_translations :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : Fin n → (relativeFppfSheaf f).obj.obj (op V)) (_z : Over.mk q ⟶ V),
      IsAffine V.left ∧ Etale V.hom ∧ ∀ (w : Over.mk q ⟶ V) j,
        s j * (relativeFppfSheaf f).obj.map w.op (c j) ∈
          (acyclicDegreePicardSubfunctor f d).obj (op (Over.mk q)) := by
  obtain ⟨k, hk, hA, t, ht, hq⟩ := GeometricTestResidueFactor.exists_factor q
  let _ := hk
  let _ := hA
  let _ := ht
  subst q
  exact exists_finite_all_lift_translations f hB t s

end FLT.Mazur.HilbertChart
