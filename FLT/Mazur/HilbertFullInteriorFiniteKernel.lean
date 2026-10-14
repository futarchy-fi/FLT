/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertAdmissibleFiniteKernel
public import FLT.Mazur.HilbertAdmissiblePrincipalExistence

/-!
# Constructed finite-model kernels through full-interior points

The original full-interior condition constructs an affine principal refinement,
an admissible invariant norm, and a further original open source containing
the given point. Its actual recomputed finite coefficient model has the entire
original Picard relation as kernel. No envelope or seed certificate is input.
Coverage of arbitrary original classes by full-interior points remains open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
/-- The finite basis uses the original translation structural algebra. -/
local instance finiteInteriorTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))

include b in
/-- Every original full-interior point has a constructed affine finite-model kernel neighborhood. -/
theorem exists_fullInterior_finite_kernel (x : A.left)
    (hx : x ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ (B : Over (Spec (.of R))) (_ : IsAffine B.left)
      (u : B ⟶ A) (_ : IsOpenImmersion u.left)
      (l : B ⟶ variableHilbertTest f d V) (_ : IsOpenImmersion l.left) (y : B.left),
      u.left y = x ∧ l = u ≫ k ∧
      IsPullback (fst f hL d V c l).left (snd f hL d V c l).left
        (finiteKernelProjection f hL d V c l).left
        (finiteKernelProjection f hL d V c l).left := by
  obtain ⟨r, hr, _, s, hs, hy⟩ :=
    exists_fullInterior_admissible_principal f hL d V c k b x hx
  let l := orbitPrincipalChart f d V k r
  let B := invariantPrincipalSource f hL d V c l s
  let j := invariantPrincipalSourceMap f hL d V c l s
  let u : B ⟶ A := j ≫ orbitPrincipalSourceMap r
  have hu : IsOpenImmersion u.left := by
    change IsOpenImmersion (((orbitPrincipalSource r).left.basicOpen s.val).ι ≫
      (A.left.basicOpen r).ι)
    infer_instance
  let l' := invariantPrincipalChart f hL d V c l s
  let y : B.left := ⟨⟨x, hr⟩, hy⟩
  refine ⟨B, inferInstance, u, hu, l', inferInstance, y, rfl, ?_, ?_⟩
  · unfold l' invariantPrincipalChart l orbitPrincipalChart
    exact (Category.assoc _ _ _).symm
  · exact admissibleFinite_isPullback f hL d V c l s hs

end FLT.Mazur.HilbertChart.AffineRestriction
