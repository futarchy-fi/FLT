/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocalHilbertTranslationCover
public import FLT.Mazur.CanonicalRelativeLineModel

/-!
# Original sections lift to finitely presented translation charts

After affine refinement, the local translation line descends to an affine
parameter base of finite presentation over the original base. Its actual
variable Hilbert chart recovers the original section on each cover member.
The parameter base is not asserted to be smooth.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard Approximation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

include hB in
/-- Every section is locally in charts whose translation bases are finitely presented. -/
theorem exists_finitePresentation_hilbert_translation_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left,
      (∀ i, IsAffine (C.X i)) ∧ ∀ i,
      ∃ (V : Over (Spec (.of R))) (b : relativeCoverMember T C i ⟶ V)
        (M : LineBundle (pullback f V.hom)) (d : ℕ)
        (k : relativeCoverMember T C i ⟶ variableHilbertTest f d V),
        IsAffine V.left ∧ IsLocallyNoetherian V.left ∧ LocallyOfFinitePresentation V.hom ∧
          k ≫ variableHilbertBase f d V = b ∧
          variableHilbertPoint f d hB V
            (relativeFppfClass f V (relativeClass _ (mk M.val M.property))) _ k =
              (relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s := by
  obtain ⟨C, hA, hC⟩ := exists_affine_local_hilbert_translation_cover f hB T s
  refine ⟨C, hA, fun i ↦ ?_⟩
  let _ : IsAffine (relativeCoverMember T C i).left := hA i
  obtain ⟨d, k, L, hk⟩ := hC i
  obtain ⟨V, b, M, hV, hN, hu, ⟨e⟩⟩ :=
    exists_canonical_relative_line_model f (relativeCoverMember T C i) L
  refine ⟨V, b, M, d, variableHilbertLift f d V b k, hV, hN, hu,
    prod.lift_fst _ _, ?_⟩
  rw [variableHilbertPoint_lift, canonical_relative_line_model_class f b L M e]
  exact hk

end FLT.Mazur.HilbertChart
