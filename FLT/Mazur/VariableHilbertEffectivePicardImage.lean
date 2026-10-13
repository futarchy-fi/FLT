/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertEffectivePicardSection
public import FLT.Mazur.SmoothHilbertSheafQuotient

/-!
# The effective model represents exactly the original fppf chart image

An original Picard section locally represented by the actual Hilbert source
has a unique map to the effective model. Both the local cover and the map
are scheme morphisms over the unchanged coefficient base.
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
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "s" => variableChartSection f hL d V c
variable {Z : Over (Spec (.of R))} (π : variableHilbertTest f d V ⟶ Z)
  (H : IsPullback (variableChartRelationFst f hL d V c)
    (variableChartRelationSnd f hL d V c) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
local notation "sZ" => effectivePicardSection f hL d V c π H

/-- The effective model maps to the ORIGINAL fppf sheaf with only its group structure forgotten. -/
def effectivePicardSheafMap :
    (Scheme.fppfTopology.over (Spec (.of R))).uliftYoneda.{1}.obj Z ⟶
      smoothHilbertTargetSheaf f :=
  ⟨effectivePicardMap f hL d V c π H⟩

/-- The model is a represented subobject of the original fppf Picard sheaf. -/
instance effectivePicardSheafMap_mono : Mono (effectivePicardSheafMap f hL d V c π H) :=
  (sheafToPresheaf _ (Type 1)).mono_of_mono_map
    (inferInstanceAs (Mono (effectivePicardMap f hL d V c π H)))

variable {T T' : Over (Spec (.of R))} (t : T' ⟶ T)
  [Flat t.left] [LocallyOfFinitePresentation t.left] [Surjective t.left]
  (a : T' ⟶ variableHilbertTest f d V) (z : (relativeFppfSheaf f).obj.obj (op T))
  (hz : (relativeFppfSheaf f).obj.map t.op z =
    (relativeFppfSheaf f).obj.map a.op (variableChartSection f hL d V c))

omit [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
  [Flat t.left] [LocallyOfFinitePresentation t.left] [Surjective t.left] in
include hz H in
/-- A locally represented original section gives compatible actual quotient maps. -/
theorem effectivePicardImage_compatible :
    pullback.fst t t ≫ (a ≫ π) = pullback.snd t t ≫ (a ≫ π) := by
  have hc : (relativeFppfSheaf f).obj.map (pullback.fst t t ≫ a).op s =
      (relativeFppfSheaf f).obj.map (pullback.snd t t ≫ a).op s := by
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hz]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      pullback.condition]
  let r := variableChartRelationLift f hL d V c _ _ hc
  have hr : r ≫ P = pullback.fst t t ≫ a :=
    variableChartRelationLift_fst f hL d V c _ _ hc
  have hr' : r ≫ Q = pullback.snd t t ≫ a :=
    variableChartRelationLift_snd f hL d V c _ _ hc
  rw [← Category.assoc, ← Category.assoc, ← hr, ← hr',
    Category.assoc, Category.assoc, H.w]

include hz in
/-- Local representation constructs a unique original-test map into the effective quotient. -/
theorem effectivePicardImage_existsUnique :
    ∃! k : T ⟶ Z, (relativeFppfSheaf f).obj.map k.op sZ = z := by
  let k := RelativeFppfSchemeCover.descend t (a ≫ π)
    (effectivePicardImage_compatible f hL d V c π H t a z hz)
  have hk : t ≫ k = a ≫ π := RelativeFppfSchemeCover.descend_source _ _ _
  have hkz : (relativeFppfSheaf f).obj.map k.op sZ = z := by
    apply relativePicardFppf_singleton_injective f t
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hk]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      effectivePicardSection_source, hz]
  exact ⟨k, hkz, fun l hl ↦
    effectivePicardSection_injective f hL d V c π H T (hl.trans hkz.symm)⟩

omit [Flat t.left] [LocallyOfFinitePresentation t.left] [Surjective t.left] in
/-- The quotient represents precisely the original fppf-local chart image on every test. -/
theorem effectivePicardImage_iff (z : (relativeFppfSheaf f).obj.obj (op T)) :
    (∃ k : T ⟶ Z, (relativeFppfSheaf f).obj.map k.op sZ = z) ↔
      ∃ (T' : Over (Spec (.of R))) (t : T' ⟶ T)
        (a : T' ⟶ variableHilbertTest f d V),
        Flat t.left ∧ LocallyOfFinitePresentation t.left ∧ Surjective t.left ∧
          (relativeFppfSheaf f).obj.map t.op z = (relativeFppfSheaf f).obj.map a.op s := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨RelativeFppfPairCover.source π k k, RelativeFppfPairCover.cover π k k,
      RelativeFppfPairCover.fst π k k, inferInstance, inferInstance, inferInstance, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← RelativeFppfPairCover.fst_map]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      effectivePicardSection_source]
  · rintro ⟨T', t, a, ht₁, ht₂, ht₃, hz⟩
    exact (effectivePicardImage_existsUnique f hL d V c π H t a z hz).exists

end FLT.Mazur.HilbertChart
