/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertChartFullRelation

/-!
# Internal equivalence on the entire original chart restriction

The original equal-class universal property constructs reflexivity, symmetry,
and composition for arbitrary translation bases. No parameter equality is
substituted for the full original Picard relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "P₁" => restrictedFst f hL d V c
local notation "P₂" => restrictedSnd f hL d V c
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hL

/-- Pulling back a full restricted relation preserves equality of the original classes. -/
theorem full_restricted_class_map {T : Over (Spec (.of R))}
    (a : T ⟶ restrictedRelation f hL d V c) :
    (relativeFppfSheaf f).obj.map
      ((a ≫ P₁) ≫ inclusion f hL d V c).op sU =
    (relativeFppfSheaf f).obj.map
      ((a ≫ P₂) ≫ inclusion f hL d V c).op sU := by
  rw [Category.assoc, Category.assoc]
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg ((relativeFppfSheaf f).obj.map a.op) (full_restricted_class f hL d V c)

/-- The composable-pair scheme retains transitivity of the original classes. -/
theorem full_restricted_composable_class :
    (relativeFppfSheaf f).obj.map
      ((pullback.fst P₂ P₁ ≫ P₁) ≫ inclusion f hL d V c).op sU =
    (relativeFppfSheaf f).obj.map
      ((pullback.snd P₂ P₁ ≫ P₂) ≫ inclusion f hL d V c).op sU := by
  calc
    _ = (relativeFppfSheaf f).obj.map
        ((pullback.fst P₂ P₁ ≫ P₂) ≫ inclusion f hL d V c).op sU :=
      full_restricted_class_map f hL d V c _
    _ = (relativeFppfSheaf f).obj.map
        ((pullback.snd P₂ P₁ ≫ P₁) ≫ inclusion f hL d V c).op sU := by
      rw [pullback.condition]
    _ = _ := full_restricted_class_map f hL d V c _

/-- The full original restricted relation is internally an equivalence relation on every chart. -/
def fullRestrictedEquivalence : CategoryTheory.EquivalenceRelation P₁ P₂ where
  right_cancellation _ _ _ h₁ h₂ := restricted_hom_ext f hL d V c h₁ h₂
  r := (full_restricted_lift f hL d V c (𝟙 _) (𝟙 _) rfl).choose
  reflexivity₁ := (full_restricted_lift f hL d V c (𝟙 _) (𝟙 _) rfl).choose_spec.1.1
  reflexivity₂ := (full_restricted_lift f hL d V c (𝟙 _) (𝟙 _) rfl).choose_spec.1.2
  s := (full_restricted_lift f hL d V c P₂ P₁
    (full_restricted_class f hL d V c).symm).choose
  symmetry₁ := (full_restricted_lift f hL d V c P₂ P₁
    (full_restricted_class f hL d V c).symm).choose_spec.1.1
  symmetry₂ := (full_restricted_lift f hL d V c P₂ P₁
    (full_restricted_class f hL d V c).symm).choose_spec.1.2
  c := PullbackCone.mk (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  isLimit := pullbackIsPullback _ _
  t := (full_restricted_lift f hL d V c _ _
    (full_restricted_composable_class f hL d V c)).choose
  transitivity₁ := (full_restricted_lift f hL d V c _ _
    (full_restricted_composable_class f hL d V c)).choose_spec.1.1
  transitivity₂ := (full_restricted_lift f hL d V c _ _
    (full_restricted_composable_class f hL d V c)).choose_spec.1.2

end FLT.Mazur.OrderedHilbertBaseOpenChart
