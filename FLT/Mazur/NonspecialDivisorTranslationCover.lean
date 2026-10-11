/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NonspecialDivisorLineCover
public import FLT.Mazur.DivisorTranslationLine

/-!
# Local translations of arbitrary original Picard sections

Every section, on every original test, has a small fppf cover with an actual
translation line and a full nonspecial divisor. Dividing the divisor's Abel
class by the translation recovers the given section, not a replacement class.
The translations are allowed to vary with the covering base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

include hB in
/-- Actual line translations present every original Picard section by full nonspecial divisors. -/
theorem exists_nonspecial_divisor_translation_cover (T : Over (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ C : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left, ∀ i,
      ∃ (D : AcyclicRankOneRelativeDivisor (pullback.snd f (relativeCoverMember T C i).hom))
        (L M : LineBundle (pullback f (relativeCoverMember T C i).hom)),
        Nonempty (ModuleSheafTensor.tensor L.val M.val ≅
          divisorLineBundle D.val.val D.val.property) ∧
        relativeFppfClass f _ (relativeClass _ (mk L.val L.property)) =
          (relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s ∧
        relativeFppfClass f _ (abel _ D.val) /
          relativeFppfClass f _ (relativeClass _ (mk M.val M.property)) =
            (relativeFppfSheaf f).obj.map (relativeCoverArrow T C i).op s := by
  obtain ⟨C, hC⟩ := exists_nonspecial_divisor_line_cover f hB T s
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨D, L, hL⟩ := hC i
  let M : LineBundle (pullback f (relativeCoverMember T C i).hom) :=
    ⟨divisorTranslationLine D.val L.val, divisorTranslationLine_rankOne D.val L.val L.property⟩
  refine ⟨D, L, M, divisorTranslationLine_tensor_iso D.val L.val L.property, hL, ?_⟩
  rw [← map_div]
  exact (congrArg (relativeFppfClass f _) (divisorTranslationLine_recover _ D.val L.val
    L.property)).trans hL

end FLT.Mazur.CartierAbel
