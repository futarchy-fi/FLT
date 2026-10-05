/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntersectionGluedModelSheaf
public import FLT.Mazur.FiniteIntersectionScalarGluingOver
public import FLT.Mazur.FiniteLineCocycleModel

/-!
# Finite coefficient models carrying a genuine line sheaf

The finite transition model supplies a rank-one sheaf on the same explicit
scheme model used for cartesian recovery. Coordinate units recover the
original transitions. Identification of the original line sheaf with the
pullback of this model sheaf is a separate remaining step.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A genuine line sheaf yields a rank-one sheaf on a finite coefficient scheme model,
with cartesian recovery of the scheme and recovery of all coordinate transition units. -/
theorem exists_finite_line_sheaf_model {A : Type u} [CommRing A]
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (p : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation p]
    (L : X.Modules) (hL : FLT.Mazur.FCurve.LocallyFreeRankOne L)
    (s : Set A) (hs : s.Finite) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
      ∃ g : FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle U,
        Nonempty (g.sheaf ≅ L) ∧
      ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ D : NonemptyChartSet ι ⥤ CommAlgCat S,
      ∃ e : ∀ a, A ⊗[S] D.obj a ≃ₐ[A] (finiteIntersectionSectionDiagram U p).obj a,
        (∀ {a b} (f : a ⟶ b), (e b).toAlgHom.comp
            (affineScalarExtensionHom (S := A) (D.map f).hom) =
          ((finiteIntersectionSectionDiagram U p).map f).hom.comp (e a).toAlgHom) ∧
      ∃ hopen : ∀ a b (f : a ⟶ b),
        IsOpenImmersion (Spec.map (CommRingCat.ofHom (D.map f).hom.toRingHom)),
      ∃ hp : ∀ (r a b : NonemptyChartSet ι) (hra : r ≤ a) (hrb : r ≤ b),
        IsPullback
          (Spec.map (CommRingCat.ofHom
            (D.map (homOfLE (le_unionChartSet_left a b))).hom.toRingHom))
          (Spec.map (CommRingCat.ofHom
            (D.map (homOfLE (le_unionChartSet_right a b))).hom.toRingHom))
          (Spec.map (CommRingCat.ofHom (D.map (homOfLE hra)).hom.toRingHom))
          (Spec.map (CommRingCat.ofHom (D.map (homOfLE hrb)).hom.toRingHom)),
      ∃ y : ∀ a, IntersectionPair a → (D.obj a)ˣ,
      ∃ hnat : ∀ {a b} (f : a ⟶ b) k, (D.map f).hom (y a k) =
        (y b (intersectionPairMap f k) : D.obj b),
      ∃ hmul : ∀ a (k : IntersectionTriple a),
        y a (k.1, k.2.1) * y a (k.2.1, k.2.2) = y a (k.1, k.2.2),
        letI := hopen
        (∀ a k, e a (1 ⊗ₜ (y a k : D.obj a)) =
          (finiteIntersectionCocycleUnit U p g a k :
            (finiteIntersectionSectionDiagram U p).obj a)) ∧
        FLT.Mazur.FCurve.LocallyFreeRankOne
          (affineIntersectionGluedModelSheaf D hp y hnat hmul) ∧
        ∃ f : X ⟶ (affineIntersectionGlueData D hp).glued,
          IsPullback f p (affineIntersectionGluedToBase D hp)
            (Spec.map (CommRingCat.ofHom (algebraMap S A))) := by
  obtain ⟨ι, hι, U, hU, hcover, g, hg, S, hS, hsS, D, e, he,
    hopen, hp, y, hy, hnat, hmul⟩ := exists_finite_line_cocycle_model p L hL s hs
  let := hι
  let := hopen
  refine ⟨ι, hι, U, hU, hcover, g, hg, S, hS, hsS, D, e, he,
    hopen, hp, y, hnat, hmul, hy,
    affineIntersectionGluedModelSheaf_rankOne D hp y hnat hmul, ?_⟩
  let E := finiteIntersectionScalarGluingIso U p hU hcover D hp e he
  refine ⟨E.inv ≫ affineIntersectionGluingProjection D hp, ?_⟩
  apply (affineIntersectionGluing_isPullback (A := A) D hp).of_iso
    E (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp
  · simpa [E] using (finiteIntersectionScalarGluingIso_over U p hU hcover D hp e he).symm
  · simp
  · simp

end FLT.Mazur.Approximation
