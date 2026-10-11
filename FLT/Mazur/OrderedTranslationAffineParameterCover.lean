/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedTranslationLocallyRingedMap

/-!
# Affine-domain refinements cover the original invariant quotient

Actual affine opens of the ordered parameter schemes map to the original
locally ringed quotient and their open images cover it. These images refine
arbitrary original quotient neighborhoods. The maps are not asserted to be
open immersions, nor are their images asserted to be affine schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : SmoothHilbertTranslationIndex)

/-- The actual locally ringed parameter map is open on underlying spaces. -/
theorem orderedTranslationLocallyRingedMap_isOpenMap :
    IsOpenMap (orderedTranslationLocallyRingedMap f hL i).base := by
  let _ : IsOpenImmersion (smoothHilbertSourceArrow f i).left := by
    change IsOpenImmersion (Sigma.ι (fun j ↦ (smoothHilbertTest f j).left) i)
    infer_instance
  change IsOpenMap ((smoothHilbertInvariantProjection f hL).base ∘
    (smoothHilbertSourceArrow f i).left)
  exact (smoothHilbertInvariantProjection_isOpenMap f hL).comp
    (smoothHilbertSourceArrow f i).left.isOpenMap

/-- The original locally ringed map restricted to an actual parameter open. -/
def orderedTranslationParameterOpenMap (W : (smoothHilbertTest f i).left.Opens) :
    W.toScheme.toLocallyRingedSpace ⟶ smoothHilbertInvariantQuotient f hL :=
  W.ι.toLRSHom ≫ orderedTranslationLocallyRingedMap f hL i

/-- The restricted parameter map is open on underlying spaces. -/
theorem orderedTranslationParameterOpenMap_isOpenMap
    (W : (smoothHilbertTest f i).left.Opens) :
    IsOpenMap (orderedTranslationParameterOpenMap f hL i W).base :=
  (orderedTranslationLocallyRingedMap_isOpenMap f hL i).comp W.ι.isOpenEmbedding.isOpenMap

/-- The actual image open in the original invariant quotient. -/
def orderedTranslationParameterImage (W : (smoothHilbertTest f i).left.Opens) :
    TopologicalSpace.Opens (smoothHilbertInvariantQuotient f hL) :=
  ⟨Set.range (orderedTranslationParameterOpenMap f hL i W).base,
    (orderedTranslationParameterOpenMap_isOpenMap f hL i W).isOpen_range⟩

/-- Parameter-open images remain inside their original smooth quotient neighborhood. -/
theorem orderedTranslationParameterImage_le (W : (smoothHilbertTest f i).left.Opens) :
    orderedTranslationParameterImage f hL i W ≤ orderedTranslationOrbitOpen f hL i := by
  rintro z ⟨x, rfl⟩
  exact (Set.ext_iff.mp (orderedTranslationLocallyRingedMap_range f hL i) _).mp ⟨x.val, rfl⟩

omit i in
/-- Affine parameter domains cover every actual quotient point. -/
theorem orderedTranslationAffineParameter_covers (z : smoothHilbertInvariantQuotient f hL) :
    ∃ (i : SmoothHilbertTranslationIndex) (W : (smoothHilbertTest f i).left.Opens),
      IsAffineOpen W ∧ z ∈ orderedTranslationParameterImage f hL i W := by
  obtain ⟨i, x, hx⟩ := orderedTranslationLocallyRingedMap_covers f hL z
  obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := (smoothHilbertTest f i).left) (x := x) (U := ⊤) trivial
  exact ⟨i, W, hW, ⟨⟨x, hxW⟩, hx⟩⟩

omit i in
/-- The open images of affine parameter domains refine every original quotient neighborhood. -/
theorem orderedTranslationAffineParameter_refines
    (O : TopologicalSpace.Opens (smoothHilbertInvariantQuotient f hL))
    (z : smoothHilbertInvariantQuotient f hL) (hz : z ∈ O) :
    ∃ (i : SmoothHilbertTranslationIndex) (W : (smoothHilbertTest f i).left.Opens),
      IsAffineOpen W ∧ z ∈ orderedTranslationParameterImage f hL i W ∧
        orderedTranslationParameterImage f hL i W ≤ O := by
  obtain ⟨i, x, hx⟩ := orderedTranslationLocallyRingedMap_covers f hL z
  let U := (TopologicalSpace.Opens.map (orderedTranslationLocallyRingedMap f hL i).base).obj O
  have hxU : x ∈ U := by change (orderedTranslationLocallyRingedMap f hL i).base x ∈ O; rwa [hx]
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hxU
  refine ⟨i, W, hW, ⟨⟨x, hxW⟩, hx⟩, ?_⟩
  rintro y ⟨t, rfl⟩
  exact hWU t.property

end FLT.Mazur.HilbertChart
