/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSplitUnramifiedSourceSeed
public import FLT.Mazur.SchemeRelationMonicSeedKernel

/-!
# The original orbit as an open in the complete changed coefficient source

Keep the new coefficient coordinate explicitly. Original arrows ending on a
seed give an open subsource after coefficient base change under unramifiedness.
Reflexivity supplies a section over the entire new target, not only a nonempty
open. The old coefficient map need not be flat or surjective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationSplitOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T Z : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (w : A.left ⟶ T)
  (h : p.left ≫ w = q.left ≫ w) (a : Z ⟶ A.left)
local notation "B" => (pullback q.left a : Scheme)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p.left q.left a
local notation "π" => pullback.snd q.left a

/-- The propagated orbit inside the COMPLETE coefficient pullback, retaining its new coordinate. -/
def inclusion : B ⟶ SchemeSplitEtaleSourceSeed.source w a :=
  pullback.lift b π (SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a)

@[reassoc]
theorem inclusion_source : inclusion w h a ≫ SchemeSplitEtaleSourceSeed.toSource w a = b :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem inclusion_projection : inclusion w h a ≫ SchemeSplitEtaleSourceSeed.projection w a = π :=
  pullback.lift_snd _ _ _

/-- Reflexivity constructs a section over every point of the new coefficient target. -/
def sectionMap : Z ⟶ B := pullback.lift (a ≫ e.r.left) (𝟙 Z) (by
  rw [Category.assoc, show e.r.left ≫ q.left = 𝟙 A.left from
    congrArg Over.Hom.left e.reflexivity₂, Category.comp_id, Category.id_comp])

@[reassoc]
theorem sectionMap_projection : sectionMap e a ≫ π = 𝟙 Z := pullback.lift_snd _ _ _

@[reassoc]
theorem sectionMap_source : sectionMap e a ≫ b = a := by
  rw [sectionMap, SchemeRelationEtaleBranchPropagation.branch, pullback.lift_fst_assoc,
    Category.assoc, show e.r.left ≫ p.left = 𝟙 A.left from
      congrArg Over.Hom.left e.reflexivity₁, Category.comp_id]

include e in
/-- The orbit projection covers the ENTIRE new target, even when the old map is not flat. -/
theorem projection_surjective : Surjective π := ⟨fun z ↦
  ⟨sectionMap e a z, congrArg (fun g ↦ g z) (sectionMap_projection e a)⟩⟩

/-- The section preserves the literal original source point. -/
theorem sectionMap_point (z : Z) : b (sectionMap e a z) = a z :=
  congrArg (fun g ↦ g z) (sectionMap_source e a)

/-- The constructed section is exactly the graph seed in the complete source. -/
@[reassoc]
theorem sectionMap_inclusion : sectionMap e a ≫ inclusion w h a =
    SchemeSplitEtaleSourceSeed.seed w a := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, inclusion, pullback.lift_fst,
      SchemeSplitEtaleSourceSeed.seed] using sectionMap_source e a
  · simpa only [Category.assoc, inclusion, pullback.lift_snd,
      SchemeSplitEtaleSourceSeed.seed] using sectionMap_projection e a

include h in
/-- Equal old source and new coefficient coordinates determine the original arrow uniquely. -/
theorem inclusion_mono [Mono (pullback.lift p.left q.left h)] : Mono (inclusion w h a) := by
  constructor
  intro Y x y he
  have hb := congrArg (fun g ↦ g ≫ SchemeSplitEtaleSourceSeed.toSource w a) he
  have hz := congrArg (fun g ↦ g ≫ SchemeSplitEtaleSourceSeed.projection w a) he
  simp only [Category.assoc, inclusion_source] at hb
  simp only [Category.assoc, inclusion_projection] at hz
  apply pullback.hom_ext
  · apply (cancel_mono (pullback.lift p.left q.left h)).mp
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst,
        SchemeRelationEtaleBranchPropagation.branch] using hb
    · simpa only [Category.assoc, pullback.lift_snd, pullback.condition] using
        congrArg (fun g ↦ g ≫ a) hz
  · exact hz

include h in
/-- Unramified coefficients make the orbit an actual OPEN in the full changed source. -/
theorem inclusion_isOpenImmersion [Mono (pullback.lift p.left q.left h)]
    [Etale p.left] [Etale a] [FormallyUnramified w] [LocallyOfFiniteType w] :
    IsOpenImmersion (inclusion w h a) := by
  let _ : FormallyUnramified (a ≫ w) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  let _ : FormallyUnramified (SchemeSplitEtaleSourceSeed.toSource w a) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let _ : LocallyOfFiniteType (SchemeSplitEtaleSourceSeed.toSource w a) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst w (a ≫ w)))
  let _ : Etale (inclusion w h a ≫ SchemeSplitEtaleSourceSeed.toSource w a) := by
    rw [inclusion_source]
    infer_instance
  let _ := Etale.of_comp (inclusion w h a) (SchemeSplitEtaleSourceSeed.toSource w a)
  let _ := inclusion_mono w h a
  exact IsOpenImmersion.of_flat_of_mono _

end FLT.Mazur.SchemeRelationSplitOrbit
