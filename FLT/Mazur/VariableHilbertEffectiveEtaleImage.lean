/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeKernelPairPropertyDescent
public import FLT.Mazur.VariableHilbertRelationGeometry
public import FLT.Mazur.VariableHilbertEffectivePicardImage

/-!
# Effective full Hilbert models represent the original etale chart image

The supplied fppf projection is proved etale from its full kernel pair.
Consequently every represented section has an actual etale local original
Hilbert representative, even if the effective model was first built fppf-locally.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {Z : Over (Spec (.of R))} (π : variableHilbertTest f d V ⟶ Z)
  (H : IsPullback (variableChartRelationFst f hL d V c)
    (variableChartRelationSnd f hL d V c) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
local notation "sZ" => effectivePicardSection f hL d V c π H
local notation "s" => variableChartSection f hL d V c

include H

/-- Any effective fppf model has a smooth projection when the translation base is smooth. -/
theorem effectiveProjection_smooth [Smooth V.hom] : Smooth π.left := by
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (H.map (Over.forget _))
    ⟨⟨inferInstanceAs (Surjective π.left), inferInstanceAs (Flat π.left)⟩,
      inferInstanceAs (LocallyOfFinitePresentation π.left)⟩
    (inferInstanceAs (Smooth (variableChartRelationFst f hL d V c).left))

/-- The full relation, including independently varying base maps, forces the model to be etale. -/
theorem effectiveProjection_etale [Etale V.hom] : Etale π.left := by
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (H.map (Over.forget _))
    ⟨⟨inferInstanceAs (Surjective π.left), inferInstanceAs (Flat π.left)⟩,
      inferInstanceAs (LocallyOfFinitePresentation π.left)⟩
    (inferInstanceAs (Etale (variableChartRelationFst f hL d V c).left))

/-- The model represents precisely the etale-local image of the original Hilbert source. -/
theorem effectivePicardEtaleImage_iff [Etale V.hom] {T : Over (Spec (.of R))}
    (z : (relativeFppfSheaf f).obj.obj (op T)) :
    (∃ k : T ⟶ Z, (relativeFppfSheaf f).obj.map k.op sZ = z) ↔
      ∃ (T' : Over (Spec (.of R))) (t : T' ⟶ T)
        (a : T' ⟶ variableHilbertTest f d V),
        Etale t.left ∧ Surjective t.left ∧
          (relativeFppfSheaf f).obj.map t.op z = (relativeFppfSheaf f).obj.map a.op s := by
  constructor
  · rintro ⟨k, rfl⟩
    let _ := effectiveProjection_etale f hL d V c π H
    refine ⟨RelativeFppfPairCover.source π k k, RelativeFppfPairCover.cover π k k,
      RelativeFppfPairCover.fst π k k, inferInstance, inferInstance, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← RelativeFppfPairCover.fst_map]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      effectivePicardSection_source]
  · rintro ⟨T', t, a, ht, hs, hz⟩
    exact (effectivePicardImage_existsUnique f hL d V c π H t a z hz).exists

/-- For this original chart, fppf and etale local representability coincide. -/
theorem effectivePicard_fppf_iff_etale [Etale V.hom] {T : Over (Spec (.of R))}
    (z : (relativeFppfSheaf f).obj.obj (op T)) :
    (∃ (T' : Over (Spec (.of R))) (t : T' ⟶ T)
      (a : T' ⟶ variableHilbertTest f d V),
      Flat t.left ∧ LocallyOfFinitePresentation t.left ∧ Surjective t.left ∧
        (relativeFppfSheaf f).obj.map t.op z = (relativeFppfSheaf f).obj.map a.op s) ↔
    ∃ (T' : Over (Spec (.of R))) (t : T' ⟶ T)
      (a : T' ⟶ variableHilbertTest f d V),
      Etale t.left ∧ Surjective t.left ∧
        (relativeFppfSheaf f).obj.map t.op z = (relativeFppfSheaf f).obj.map a.op s :=
  (effectivePicardImage_iff f hL d V c π H z).symm.trans
    (effectivePicardEtaleImage_iff f hL d V c π H z)

end FLT.Mazur.HilbertChart
