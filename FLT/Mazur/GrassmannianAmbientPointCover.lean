/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientGluedChartPoint

/-!
# A coefficient principal cover for every original ambient quotient

The index records all original ambient charts and coefficient localizations on
which their selected summand is a quotient basis. The cover is proved from local
basis coverage, retaining the ambient-rank-minus-quotient-rank complement formula.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Every localization and original ambient chart carrying a basis for the localized quotient. -/
def AmbientPointCoverIndex (N : Module.Grassmannian A (A ⊗[R] M) d) :=
  Σ i : AmbientChartIndex R M κ d, {r : A // Function.Bijective
    ((Module.Grassmannian.map (IsScalarTower.toAlgHom R A
      (Localization.Away r)) N).toSubmodule.mkQ.comp
       (ambientChartSelected (ambientChartBaseChange (Localization.Away r) i)))}

/-- The local chart point is the actual scalar extension of the entire original quotient. -/
def ambientPointCoverChartPoint (N : Module.Grassmannian A (A ⊗[R] M) d)
    (q : AmbientPointCoverIndex (κ := κ) N) :
    AmbientChartPoint (ambientChartBaseChange (Localization.Away q.2.val) q.1) :=
  ⟨Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) N,
    q.2.property⟩

/-- These actual localization spectra cover the entire original coefficient spectrum. -/
def ambientPointPrincipalCover {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
    (N : Module.Grassmannian A (A ⊗[R] M) d) (hκ : Fintype.card κ = Fintype.card ι - d) :
    (Spec (.of A)).OpenCover where
  I₀ := AmbientPointCoverIndex (κ := κ) N
  X q := Spec (.of (Localization.Away q.2.val))
  f q := Spec.algebraMap A (Localization.Away q.2.val)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p ↦ ?_, fun q ↦ inferInstance⟩
    obtain ⟨i, r, hr, hi⟩ := exists_functor_localized_chart b N hκ p
    refine ⟨⟨i, ⟨r, hi⟩⟩, (basicOpenIsoSpecAway (R := .of A) r).hom ⟨p, hr⟩, ?_⟩
    exact congrArg (fun f ↦ f ⟨p, hr⟩)
      (basicOpenIsoSpecAway_hom_SpecMap (R := .of A) r)

/-- The local classification on each principal member of the actual quotient's cover. -/
def ambientPointCoverClassifyingMap (N : Module.Grassmannian A (A ⊗[R] M) d)
    (q : AmbientPointCoverIndex (κ := κ) N) :
    Spec (.of (Localization.Away q.2.val)) ⟶ ambientGrassmannianScheme R M κ d :=
  ambientGluedChartPoint q.1 (ambientPointCoverChartPoint N q)

/-- Every local classification is a morphism over the original base ring. -/
@[reassoc] theorem ambientPointCoverClassifyingMap_over
    (N : Module.Grassmannian A (A ⊗[R] M) d) (q : AmbientPointCoverIndex (κ := κ) N) :
    ambientPointCoverClassifyingMap N q ≫ ambientGrassmannianStructure R M κ d =
      Spec.algebraMap R (Localization.Away q.2.val) :=
  ambientGluedChartPoint_over _ _

end FLT.Mazur.GrassmannianChart
