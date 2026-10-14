/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertModelEffectiveDescent
public import FLT.Mazur.RelativeFppfTargetOpen

/-!
# Original Picard sections on constructed fppf effective model regions

For any locally finitely presented coequalizing model, restrict its effective
projection to the constructed fppf target region. Flatness and surjectivity
are proved for this projection, without being assumed for the original model.
The original Picard section and its full equality relation are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  {T : Over (Spec (.of R))} (w : A ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
variable [LocallyOfFinitePresentation w.left]
local notation "g" => modelEffectiveRelativeProjection f hL d V c k w hw
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)

/-- A constructed open of the effective target, retaining its coefficient base. -/
def modelFppfTarget : Over (Spec (.of R)) := RelativeFppfTargetOpen.target g

/-- The entire original effective source over the constructed region. -/
def modelFppfSource : Over (Spec (.of R)) := RelativeFppfTargetOpen.source g

/-- The comparison with the complete effective source is an actual open restriction. -/
def modelFppfToEffective : modelFppfSource f hL d V c k w hw ⟶
    modelEffectiveOver f hL d V c k w hw := RelativeFppfTargetOpen.toSource g

/-- The projection is constructed from the original model morphism. -/
def modelFppfProjection : modelFppfSource f hL d V c k w hw ⟶
    modelFppfTarget f hL d V c k w hw := RelativeFppfTargetOpen.projection g

/-- The retained target includes into the original effective model over the same base. -/
def modelFppfToEffectiveTarget : modelFppfTarget f hL d V c k w hw ⟶
    modelEffectiveTarget f hL d V c k w hw := RelativeFppfTargetOpen.toTarget g

/-- The restriction is Cartesian with the complete original effective source. -/
theorem modelFppf_isPullback :
    IsPullback (modelFppfToEffective f hL d V c k w hw).left
      (modelFppfProjection f hL d V c k w hw).left (g).left
      (modelFppfToEffectiveTarget f hL d V c k w hw).left :=
  RelativeFppfTargetOpen.isPullback g

local notation "π" => modelFppfProjection f hL d V c k w hw
local notation "b₀" => modelFppfToEffective f hL d V c k w hw

/-- The original source and target maps commute before forgetting coefficients. -/
@[reassoc]
theorem modelFppf_condition :
    b₀ ≫ g = π ≫ RelativeFppfTargetOpen.toTarget g := RelativeFppfTargetOpen.condition g

instance modelFppfProjection_flat : Flat (π).left :=
  RelativeFppfTargetOpen.projection_flat g

instance modelFppfProjection_surjective : Surjective (π).left :=
  RelativeFppfTargetOpen.projection_surjective g

instance modelFppfProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (π).left :=
  RelativeFppfTargetOpen.projection_locallyOfFinitePresentation g

/-- The target is an actual open in the original model, with its original base map. -/
def modelFppfTargetToModel : modelFppfTarget f hL d V c k w hw ⟶ T :=
  modelFppfToEffectiveTarget f hL d V c k w hw ≫
    Over.homMk (KernelPairEffectiveOpen.targetOpen
      (fst f hL d V c k).left (snd f hL d V c k).left w.left hw).ι

instance modelFppfTargetToModel_isOpenImmersion :
    IsOpenImmersion (modelFppfTargetToModel f hL d V c k w hw).left := by
  change IsOpenImmersion ((RelativeFppfTargetOpen.toTarget g).left ≫
    (KernelPairEffectiveOpen.targetOpen
      (fst f hL d V c k).left (snd f hL d V c k).left w.left hw).ι)
  infer_instance

/-- The full source square is Cartesian over the original, possibly nonreduced model. -/
theorem modelFppfOriginal_isPullback :
    IsPullback ((b₀).left ≫ (modelEffectiveToSource f hL d V c k w hw).left)
      (π).left w.left (modelFppfTargetToModel f hL d V c k w hw).left :=
  (modelFppf_isPullback f hL d V c k w hw).paste_horiz
    (IsPullback.of_hasPullback w.left _)

/-- Pull back the literal original Picard section through the whole source restriction. -/
def modelFppfSection : (F).obj (op (modelFppfSource f hL d V c k w hw)) :=
  (F).map (b₀).op (modelEffectiveSection f hL d V c k w hw)

/-- Equal target points recover equality in the original Picard sheaf on all scheme tests. -/
theorem modelFppf_equal_class {Z : Over (Spec (.of R))}
    (a b : Z ⟶ modelFppfSource f hL d V c k w hw) (hab : a ≫ π = b ≫ π) :
    (F).map a.op (modelFppfSection f hL d V c k w hw) =
      (F).map b.op (modelFppfSection f hL d V c k w hw) := by
  have he : (a ≫ b₀).left ≫ (g).left = (b ≫ b₀).left ≫ (g).left := by
    have ht : (a ≫ b₀) ≫ g = (b ≫ b₀) ≫ g := by
      rw [Category.assoc, Category.assoc, modelFppf_condition,
        ← Category.assoc a, ← Category.assoc b, hab]
    exact congrArg Over.Hom.left ht
  have hc := modelEffective_equal_class f hL d V c k w hw (a ≫ b₀) (b ≫ b₀) he
  simpa only [modelFppfSection, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply] using hc

/-- Original class equality also detects the constructed fppf target, including nilpotents. -/
theorem modelFppf_model_eq {Z : Over (Spec (.of R))}
    (a b : Z ⟶ modelFppfSource f hL d V c k w hw)
    (hab : (F).map a.op (modelFppfSection f hL d V c k w hw) =
      (F).map b.op (modelFppfSection f hL d V c k w hw)) : a ≫ π = b ≫ π := by
  have hc : (F).map (a ≫ b₀).op (modelEffectiveSection f hL d V c k w hw) =
      (F).map (b ≫ b₀).op (modelEffectiveSection f hL d V c k w hw) := by
    simpa only [modelFppfSection, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply] using hab
  have he := modelEffective_model_eq f hL d V c k w hw (a ≫ b₀) (b ≫ b₀) hc
  have ht : (a ≫ b₀) ≫ g = (b ≫ b₀) ≫ g := Over.OverMorphism.ext he
  apply Over.OverMorphism.ext
  apply (cancel_mono (RelativeFppfTargetOpen.toTarget g).left).mp
  change (a ≫ π ≫ RelativeFppfTargetOpen.toTarget g).left =
    (b ≫ π ≫ RelativeFppfTargetOpen.toTarget g).left
  rw [← modelFppf_condition, ← Category.assoc, ← Category.assoc, ht]

/-- The actual fppf target has exactly the original Picard equality relation. -/
theorem modelFppf_test_iff {Z : Over (Spec (.of R))}
    (a b : Z ⟶ modelFppfSource f hL d V c k w hw) : a ≫ π = b ≫ π ↔
    (F).map a.op (modelFppfSection f hL d V c k w hw) =
      (F).map b.op (modelFppfSection f hL d V c k w hw) :=
  ⟨modelFppf_equal_class f hL d V c k w hw a b,
    modelFppf_model_eq f hL d V c k w hw a b⟩

/-- Every pair has its unique arrow in the full original Picard relation. -/
theorem modelFppf_original_lift {Z : Over (Spec (.of R))}
    (a b : Z ⟶ modelFppfSource f hL d V c k w hw) (hab : a ≫ π = b ≫ π) :
    ∃! z : Z ⟶ relation f hL d V c k,
      z ≫ fst f hL d V c k = a ≫ b₀ ≫ modelEffectiveToSource f hL d V c k w hw ∧
      z ≫ snd f hL d V c k = b ≫ b₀ ≫ modelEffectiveToSource f hL d V c k w hw := by
  apply lift f hL d V c k
  have hc := modelFppf_equal_class f hL d V c k w hw a b hab
  simpa only [modelFppfSection, modelEffectiveSection, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply] using hc

end FLT.Mazur.HilbertChart.AffineRestriction
