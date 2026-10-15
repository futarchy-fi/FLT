/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGeometricFiberSections
public import FLT.Mazur.EtaleFiniteGeometricAffine

/-!
# Spreading the original independent envelope sections

The complete finite family on a separably closed test extends simultaneously
to actual maps from one affine étale neighborhood of the ORIGINAL source.
Its coefficient map has finite presentation. Distinctness and enumeration
are asserted on the original geometric test, not on every nearby fiber.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart.AffineRestriction
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
  (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  {A : Over (Spec (.of R))} [IsAffine A.left]
  {K : Type} [Field K] [IsSepClosed K]
  {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- The original fiber enumeration spreads to one affine, finitely presented étale test. -/
theorem exists_independent_etale_spread :
    ∃ (U : Over (Spec (.of R))) (q : U ⟶ A) (z : Over.mk t ⟶ U)
      (e : Fin (π ⁻¹' {b.left η}).ncard → (U ⟶ prod A V)),
      IsAffine U.left ∧ Etale q.left ∧ q.left.appTop.hom.FinitePresentation ∧
      z ≫ q = b ∧ (∀ i, e i ≫ prod.fst = q) ∧
      Function.Injective (fun i ↦ (z ≫ e i).left η) ∧
      Set.range (fun i ↦ (z ≫ e i).left η) = π ⁻¹' {b.left η} := by
  obtain ⟨a, ha, hi, hr⟩ := exists_independent_geometric_sections V b
  have hp : π = (Over.prodLeftIsoPullback A V).hom ≫ pullback.fst A.hom V.hom :=
    (Over.prodLeftIsoPullback_hom_fst A V).symm
  let _ : Etale π := by rw [hp]; infer_instance
  obtain ⟨U, q, z, e, hU, hq, hz, he, hze⟩ :=
    EtaleFiniteGeometricDiagram.exists_common_affine (fun _ ↦ (prod A V).left)
      (fun _ ↦ π) b.left (fun i ↦ (a i).left) (fun i ↦ congrArg Over.Hom.left (ha i))
  let W : Over (Spec (.of R)) := Over.mk (q ≫ A.hom)
  let q' : W ⟶ A := Over.homMk q
  let z' : Over.mk t ⟶ W := Over.homMk z (by
    change z ≫ q ≫ A.hom = t
    rw [← Category.assoc, hz, b.w]
    rfl)
  have hw (i : Fin (π ⁻¹' {b.left η}).ncard) : e i ≫ (prod A V).hom = W.hom := by
    rw [← (prod.fst : prod A V ⟶ A).w, ← Category.assoc, he]
    rfl
  let e' (i : Fin (π ⁻¹' {b.left η}).ncard) : W ⟶ prod A V :=
    Over.homMk (e i) (hw i)
  have he' (i : Fin (π ⁻¹' {b.left η}).ncard) : z' ≫ e' i = a i :=
    Over.OverMorphism.ext (hze i)
  refine ⟨W, q', z', e', hU, hq, q.finitePresentation_appTop,
    Over.OverMorphism.ext hz, fun i ↦ Over.OverMorphism.ext (he i), ?_, ?_⟩
  · simpa only [he'] using hi
  · simpa only [he'] using hr

end FLT.Mazur.HilbertChart.AffineRestriction
