/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertFppfQuotient
public import FLT.Mazur.OrderedHilbertChartFullEquivalence

/-!
# The entire original restricted relation as a nonsplit fppf kernel pair

When the translating section descends along an fppf map to an open base,
the composite parameter map is a constructed fppf projection. Its kernel
pair is the whole original double restriction, retaining mixed components.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "P₁" => restrictedFst f hL d W cW
local notation "P₂" => restrictedSnd f hL d W cW
local notation "s" => OrderedHilbertIdentityOriginalSection.sourceSection f hL

/-- The actual quotient projection combines the original chart cover and fppf base change. -/
def fppfChartProjection : source f hL d W cW ⟶ variableHilbertTest f d V :=
  projection f hL d W cW ≫ baseMarkedChartChange f b d

/-- Composite parameters agree exactly when the original source classes agree. -/
theorem fppfChartProjection_eq_iff {T : Over (Spec (.of R))}
    (a a' : T ⟶ source f hL d W cW) :
    a ≫ fppfChartProjection f hL d b c = a' ≫ fppfChartProjection f hL d b c ↔
      (relativeFppfSheaf f).obj.map (a ≫ inclusion f hL d W cW).op s =
        (relativeFppfSheaf f).obj.map (a' ≫ inclusion f hL d W cW).op s := by
  rw [full_parameter_class, full_parameter_class]
  simpa only [fppfChartProjection, Category.assoc] using
    variableHilbertChange_eq_iff f hL d b c
      (a ≫ projection f hL d W cW) (a' ≫ projection f hL d W cW)

/-- The entire original restricted relation is coequalized by the composite projection. -/
theorem fppfChartProjection_condition :
    P₁ ≫ fppfChartProjection f hL d b c = P₂ ≫ fppfChartProjection f hL d b c :=
  (fppfChartProjection_eq_iff f hL d b c _ _).mpr (full_restricted_class f hL d W cW)

/-- The full original restriction is the actual scheme kernel pair of the composite map. -/
theorem fppfChartProjection_isPullback :
    IsPullback P₁ P₂ (fppfChartProjection f hL d b c) (fppfChartProjection f hL d b c) := by
  let lift (z : PullbackCone (fppfChartProjection f hL d b c)
      (fppfChartProjection f hL d b c)) :=
    full_restricted_lift f hL d W cW z.fst z.snd
      ((fppfChartProjection_eq_iff f hL d b c _ _).mp z.condition)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fppfChartProjection_condition f hL d b c) (fun z ↦ (lift z).choose)
    (fun z ↦ (lift z).choose_spec.1.1) (fun z ↦ (lift z).choose_spec.1.2)
    (fun z k h₁ h₂ ↦ (lift z).choose_spec.2 k ⟨h₁, h₂⟩))

instance fppfChartProjection_flat [Flat b.left] :
    Flat (fppfChartProjection f hL d b c).left := by
  change Flat ((projection f hL d W cW).left ≫ (baseMarkedChartChange f b d).left)
  infer_instance

instance fppfChartProjection_locallyOfFinitePresentation [LocallyOfFinitePresentation b.left] :
    LocallyOfFinitePresentation (fppfChartProjection f hL d b c).left := by
  change LocallyOfFinitePresentation
    ((projection f hL d W cW).left ≫ (baseMarkedChartChange f b d).left)
  infer_instance

instance fppfChartProjection_surjective [Surjective b.left] :
    Surjective (fppfChartProjection f hL d b c).left := by
  change Surjective ((projection f hL d W cW).left ≫ (baseMarkedChartChange f b d).left)
  infer_instance

end FLT.Mazur.OrderedHilbertBaseOpenChart
