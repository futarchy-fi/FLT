/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationNeighborhoods
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Quasi-compactness of the full relation over a Noetherian affine parameter

For a Noetherian affine parameter and an affine étale translation, the full
relation is an open subscheme of a Noetherian affine envelope. Thus the qcqs
principal-section calculation applies to the whole relation. Noetherianity
of the parameter is an explicit input, not inferred from finite variables.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsLocallyNoetherian A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]

omit [Algebra.FiniteType ℤ R] [IsAffine A.left] [IsAffine V.left] in
/-- The original product envelope is locally Noetherian over the original affine parameter. -/
theorem envelope_isLocallyNoetherian : IsLocallyNoetherian (prod A V).left := by
  let _ : LocallyOfFiniteType (prod.fst : prod A V ⟶ A).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst A V]
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (prod.fst : prod A V ⟶ A).left

/-- The full relation is Noetherian as a space; all its original arrows are retained. -/
theorem relation_noetherianSpace : NoetherianSpace (relation f hL d V c k).left := by
  let _ := variableHilbertOverlap_envelope_affine V A
  let _ := envelope_isLocallyNoetherian V (A := A)
  let _ : IsNoetherian (prod A V).left := ⟨⟩
  exact (toEnvelope f hL d V c k).left.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace

/-- The complete original relation is quasi-compact, without selecting a finite branch subset. -/
theorem relation_compactSpace : CompactSpace (relation f hL d V c k).left := by
  let _ := relation_noetherianSpace f hL d V c k
  infer_instance

omit [IsAffine A.left] [IsAffine V.left] in
/-- The complete original relation is quasi-separated. -/
theorem relation_quasiSeparatedSpace : QuasiSeparatedSpace (relation f hL d V c k).left := by
  let _ := envelope_isLocallyNoetherian V (A := A)
  let _ := isLocallyNoetherian_of_isOpenImmersion (toEnvelope f hL d V c k).left
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
