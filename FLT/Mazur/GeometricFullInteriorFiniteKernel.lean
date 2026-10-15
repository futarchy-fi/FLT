/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFullInteriorFiniteKernel

/-!
# Geometric classes on constructed finite-model kernel neighborhoods

The nonvanishing invariant norm constructs an actual open affine source.
Factor the whole original geometric map through that open, retaining its
Picard section and the full scheme kernel square, including nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
/-- Use the original translation structural algebra for its finite basis. -/
local instance geometricKernelTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (e : Basis ι R Γ(V.left, ⊤))
  {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))

include e in
/-- A constructed norm neighborhood retains the whole geometric class and full finite kernel. -/
theorem exists_geometric_fullInterior_finite_kernel
    (hx : b.left η ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ (B : Over (Spec (.of R))) (_ : IsAffine B.left)
      (u : B ⟶ A) (_ : IsOpenImmersion u.left)
      (l : B ⟶ variableHilbertTest f d V) (_ : IsOpenImmersion l.left)
      (z : Over.mk t ⟶ B), z ≫ u = b ∧ l = u ≫ k ∧
      (relativeFppfSheaf f).obj.map z.op (sectionAt f hL d V c l) =
        (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) ∧
      IsPullback (fst f hL d V c l).left (snd f hL d V c l).left
        (finiteKernelProjection f hL d V c l).left
        (finiteKernelProjection f hL d V c l).left := by
  obtain ⟨B, hB, u, hu, l, hl, y, hy, hku, hker⟩ :=
    exists_fullInterior_finite_kernel f hL d V c k e (b.left η) hx
  have hr : Set.range b.left ⊆ Set.range u.left := by
    rintro _ ⟨x, rfl⟩
    exact ⟨y, hy.trans (congrArg b.left (Subsingleton.elim η x))⟩
  let z₀ := IsOpenImmersion.lift u.left b.left hr
  have hz₀ : z₀ ≫ u.left = b.left := IsOpenImmersion.lift_fac _ _ _
  let z : Over.mk t ⟶ B := Over.homMk z₀ (by
    rw [← u.w, ← Category.assoc, hz₀]
    exact b.w)
  have hz : z ≫ u = b := Over.OverMorphism.ext hz₀
  refine ⟨B, hB, u, hu, l, hl, z, hz, hku, ?_, hker⟩
  rw [hku]
  simp only [sectionAt, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hc := congrArg (fun a ↦ (relativeFppfSheaf f).obj.map a.op
    (sectionAt f hL d V c k)) hz
  simpa only [sectionAt, op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hc

end FLT.Mazur.HilbertChart.AffineRestriction
