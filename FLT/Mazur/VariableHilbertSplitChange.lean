/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChartChange
public import FLT.Mazur.BaseOpenHilbertBaseChange
public import FLT.Mazur.VariableHilbertChartRelationOperations

/-!
# Split translation changes and the original full Hilbert relation

For a translation pulled from an open base, the full equal-Picard-class
relation is the kernel pair of the actual parameter-base comparison.
A section of the base comparison gives an actual section on parameters.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

/-- Full original class equality is exactly equality in the unchanged target chart. -/
theorem variableHilbertChange_eq_iff {T : Over (Spec (.of R))}
    (k l : T ⟶ variableHilbertTest f d W) :
    k ≫ baseMarkedChartChange f b d = l ≫ baseMarkedChartChange f b d ↔
      (relativeFppfSheaf f).obj.map k.op (variableChartSection f hL d W cW) =
        (relativeFppfSheaf f).obj.map l.op (variableChartSection f hL d W cW) := by
  have hk := baseMarkedChartChange_class f hL b (d, c) k
  have hl := baseMarkedChartChange_class f hL b (d, c) l
  dsimp only [baseMarkedIndexChange, Prod.fst, Prod.snd] at hk hl
  rw [variableChartSection_map, variableChartSection_map, ← hk, ← hl]
  exact (baseOpenHilbertPoint_injective f hL d V c T).eq_iff.symm

/-- The full original relation is coequalized by the actual comparison. -/
theorem variableHilbertChange_condition :
    variableChartRelationFst f hL d W cW ≫ baseMarkedChartChange f b d =
      variableChartRelationSnd f hL d W cW ≫ baseMarkedChartChange f b d :=
  (variableHilbertChange_eq_iff f hL d b c _ _).mpr
    (variableChartRelation_class f hL d W cW)

/-- Every compatible pair lifts uniquely to the ORIGINAL full relation. -/
theorem variableHilbertChange_relation_lift {T : Over (Spec (.of R))}
    (k l : T ⟶ variableHilbertTest f d W)
    (h : k ≫ baseMarkedChartChange f b d = l ≫ baseMarkedChartChange f b d) :
    ∃! r : T ⟶ variableChartRelation f hL d W cW,
      r ≫ variableChartRelationFst f hL d W cW = k ∧
        r ≫ variableChartRelationSnd f hL d W cW = l :=
  variableChartRelation_lift f hL d W cW k l
    ((variableHilbertChange_eq_iff f hL d b c k l).mp h)

/-- The full relation is the actual scheme kernel pair, including distinct base maps. -/
theorem variableHilbertChange_isPullback :
    IsPullback (variableChartRelationFst f hL d W cW)
      (variableChartRelationSnd f hL d W cW)
      (baseMarkedChartChange f b d) (baseMarkedChartChange f b d) := by
  let lift (z : PullbackCone (baseMarkedChartChange f b d) (baseMarkedChartChange f b d)) :=
    variableHilbertChange_relation_lift f hL d b c z.fst z.snd z.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (variableHilbertChange_condition f hL d b c) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z r h₁ h₂ ↦ (lift z).choose_spec.2 r ⟨h₁, h₂⟩))

omit [IsOpenImmersion V.hom] in
/-- A section of the translation base gives a section of the actual chart comparison. -/
theorem variableHilbertChange_section (s : V ⟶ W) (hs : s ≫ b = 𝟙 V) :
    baseMarkedChartChange f s d ≫ baseMarkedChartChange f b d = 𝟙 _ := by
  apply prod.hom_ext
  · change _ ≫ variableHilbertBase f d V = _
    rw [Category.assoc, baseMarkedChartChange_base, ← Category.assoc,
      baseMarkedChartChange_base, Category.assoc, hs, Category.comp_id, Category.id_comp]
    rfl
  · change _ ≫ variableHilbertParameter f d V = _
    rw [Category.assoc, baseMarkedChartChange_parameter,
      baseMarkedChartChange_parameter, Category.id_comp]
    rfl

end FLT.Mazur.HilbertChart
