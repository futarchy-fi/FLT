/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalHilbertTranslationCover

/-!
# Affine refinement of the original local Hilbert translations

Every original Picard section has a small fppf cover by affine tests carrying
actual Hilbert parameters and translation lines. The comparison is with the
original section restricted along the flattened cover arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

include hB in
/-- Affine local Hilbert presentations preserve every original sheaf section. -/
theorem exists_affine_local_hilbert_translation_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left,
      (∀ i, IsAffine (C.X i)) ∧ ∀ i,
      ∃ (d : ℕ) (k : relativeCoverMember T C i ⟶ acyclicHilbertTest f d)
        (M : LineBundle (pullback f (relativeCoverMember T C i).hom)),
        (show (relativeFppfSheaf f).obj.obj (op (relativeCoverMember T C i)) from
          acyclicHilbertPicardPoint f d hB _ k) /
          relativeFppfClass f _ (relativeClass _ (mk M.val M.property)) =
            (relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s := by
  obtain ⟨C, hC⟩ := exists_local_hilbert_translation_cover f hB T s
  let E i := (C.X i).affineOpenCover.openCover.weaken
    Scheme.zariskiPrecoverage_le_fppfPrecoverage
  let F := C.bind E
  refine ⟨F, fun i ↦ ?_, fun i ↦ ?_⟩
  · change IsAffine (Spec (((C.X i.1).affineOpenCover).X i.2))
    infer_instance
  · let V := relativeCoverMember T C i.1
    let W := relativeCoverMember T F i
    let a : W ⟶ V := Over.homMk ((E i.1).f i.2) (by rfl)
    obtain ⟨d, k, M, hk⟩ := hC i.1
    let N := (Scheme.Modules.pullback (relativeTotalMap f a)).obj M.val
    have hN := M.property.pullback (relativeTotalMap f a)
    refine ⟨d, a ≫ k, ⟨N, hN⟩, ?_⟩
    rw [acyclicHilbertPicardPoint_natural]
    change _ / relativeFppfClass f W
      (relativeBaseMap f a (relativeClass _ (mk M.val M.property))) = _
    rw [← relativeFppfClass_naturality, ← map_div, hk]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 2

end FLT.Mazur.HilbertChart
