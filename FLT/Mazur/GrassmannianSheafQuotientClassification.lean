/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianLocallyFramedQuotient
public import FLT.Mazur.GrassmannianQuotientCoverIndependence

/-!
# Cover-independent classification of original sheaf quotients

The atlas predicate retains each full original projection. Existence is
constructed from local frames, and uniqueness compares arbitrary source covers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- An original quotient atlas presents the scheme morphism and the whole ambient map. -/
@[irreducible] def SheafQuotientClassifies
    (f : X ⟶ ambientGrassmannianScheme R M κ d) : Prop :=
  ∃ (C : X.AffineOpenCover.{u}) (a : ∀ j, Algebra R (C.X j)),
    let _ := a
    ∃ (hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j))
      (N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d),
      (∀ j, C.f j ≫ f = ambientClassifyingMap b (N j) hκ) ∧
      ∀ j, ∃ e : grassmannianQuotientSheaf (N j) ≅ (pullback (C.f j)).obj P,
        grassmannianQuotientSheafMap (N j) ≫ e.hom =
          sheafQuotientTestMap β p (C.f j) (hC j)

/-- The full original atlas forces the original base map. -/
theorem SheafQuotientClassifies.over {f : X ⟶ ambientGrassmannianScheme R M κ d}
    (h : SheafQuotientClassifies β p b hκ f) :
    f ≫ ambientGrassmannianStructure R M κ d = β := by
  unfold SheafQuotientClassifies at h
  obtain ⟨C, a, hC, N, hf, _⟩ := h
  let _ := a
  apply C.openCover.hom_ext
  intro j
  change C.f j ≫ f ≫ ambientGrassmannianStructure R M κ d = C.f j ≫ β
  rw [← Category.assoc, hf j, ambientClassifyingMap_over, hC j]

/-- The classifying map does not depend on the chosen source cover or local frames. -/
theorem SheafQuotientClassifies.unique {f g : X ⟶ ambientGrassmannianScheme R M κ d}
    (h : SheafQuotientClassifies β p b hκ f)
    (h' : SheafQuotientClassifies β p b hκ g) : f = g := by
  unfold SheafQuotientClassifies at h h'
  obtain ⟨C, a, hC, N, hf, he⟩ := h
  obtain ⟨D, a', hD, N', hg, he'⟩ := h'
  let _ := a
  let _ := a'
  exact sheafQuotientClassifying_eq_of_covers b hκ β p C D hC hD N N'
    (fun j ↦ (he j).choose) (fun k ↦ (he' k).choose)
    (fun j ↦ (he j).choose_spec) (fun k ↦ (he' k).choose_spec) f g hf hg

/-- Actual pointwise fixed-rank frames construct the unique global classification. -/
theorem existsUnique_sheafQuotientClassifies [Epi p] {τ : Type u} [Fintype τ]
    (hP : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (P.restrict U.ι ≅ SheafOfModules.free τ)) (hd : Fintype.card τ = d) :
    ∃! f, SheafQuotientClassifies β p b hκ f := by
  obtain ⟨f, _, C, a, hC, N, hf, he⟩ :=
    exists_locallyFramedQuotientClassifying β p hP hd b hκ
  have h : SheafQuotientClassifies β p b hκ f := by
    unfold SheafQuotientClassifies
    exact ⟨C, a, hC, N, hf, he⟩
  exact ⟨f, h, fun g hg ↦ hg.unique β p b hκ h⟩

end FLT.Mazur.GrassmannianChart
