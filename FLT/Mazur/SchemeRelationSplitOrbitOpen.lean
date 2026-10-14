/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationSplitOrbitQuotient

/-!
# The split quotient on the actual open coefficient pullback

Identify the original orbit with its open image in the COMPLETE changed
source. The quotient is a split surjective etale map onto the entire new
target, and retains both old source and coefficient morphisms as scheme maps.
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
  [Mono (pullback.lift p.left q.left h)] [Etale p.left] [Etale a]
  [FormallyUnramified w] [LocallyOfFiniteType w]
local notation "B" => (pullback q.left a : Scheme)
local notation "π" => pullback.snd q.left a
local notation "i" => inclusion w h a
local notation "C" => SchemeSplitEtaleSourceSeed.source w a
local instance inclusionOpen : IsOpenImmersion i := inclusion_isOpenImmersion w h a

/-- The actual selected open inside the whole changed coefficient source. -/
def sourceOpen : (C).Opens := ⟨Set.range i, (i).isOpenMap.isOpen_range⟩

/-- Its original orbit presentation is isomorphic as a scheme, including nilpotents. -/
def sourceOpenIso : B ≅ (sourceOpen w h a).toScheme :=
  IsOpenImmersion.isoOfRangeEq i (sourceOpen w h a).ι (by
    rw [Scheme.Opens.range_ι]; rfl)

@[reassoc]
theorem sourceOpenIso_hom_ι : (sourceOpenIso w h a).hom ≫ (sourceOpen w h a).ι = i :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem sourceOpenIso_inv_inclusion : (sourceOpenIso w h a).inv ≫ i = (sourceOpen w h a).ι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The quotient morphism on the actual open subscheme. -/
def openProjection : (sourceOpen w h a).toScheme ⟶ Z := (sourceOpenIso w h a).inv ≫ π

/-- The quotient has an actual section over its entire target. -/
def openSection : Z ⟶ (sourceOpen w h a).toScheme := sectionMap e a ≫ (sourceOpenIso w h a).hom

@[reassoc]
theorem openSection_projection : openSection e w h a ≫ openProjection w h a = 𝟙 Z := by
  simp only [openSection, openProjection, Category.assoc, Iso.hom_inv_id_assoc,
    sectionMap_projection]

/-- Every original seed point survives in this open with its full coefficient coordinate. -/
@[reassoc]
theorem openSection_ι : openSection e w h a ≫ (sourceOpen w h a).ι =
    SchemeSplitEtaleSourceSeed.seed w a := by
  rw [openSection, Category.assoc, sourceOpenIso_hom_ι, sectionMap_inclusion]

include e in
/-- The actual selected open has a surjective etale quotient over the whole new target. -/
theorem openProjection_cover [Etale q.left] :
    Etale (openProjection w h a) ∧ Surjective (openProjection w h a) := by
  let _ := projection_surjective e a
  exact ⟨inferInstanceAs (Etale ((sourceOpenIso w h a).inv ≫ π)),
    inferInstanceAs (Surjective ((sourceOpenIso w h a).inv ≫ π))⟩

/-- The open quotient retains the entire new coefficient coordinate. -/
@[reassoc]
theorem openProjection_eq : (sourceOpen w h a).ι ≫
    SchemeSplitEtaleSourceSeed.projection w a = openProjection w h a := by
  rw [← sourceOpenIso_inv_inclusion, Category.assoc, inclusion_projection]
  rfl

/-- The old coefficient map survives as a literal scheme morphism. -/
@[reassoc]
theorem openProjection_oldCoefficient : (sourceOpen w h a).ι ≫
    SchemeSplitEtaleSourceSeed.toSource w a ≫ w = openProjection w h a ≫ a ≫ w := by
  rw [← sourceOpenIso_inv_inclusion, Category.assoc, inclusion_source_assoc]
  simp only [openProjection, Category.assoc,
    SchemeRelationEtaleBranchPropagation.branch_comp p.left q.left w h a]

include e in
/-- The actual open quotient has the FULL original relation as its scheme kernel. -/
theorem openRelation_isPullback : IsPullback
    ((fullComparison w h a ≫ pullback.fst π π) ≫ (sourceOpenIso w h a).hom)
    ((fullComparison w h a ≫ pullback.snd π π) ≫ (sourceOpenIso w h a).hom)
    (openProjection w h a) (openProjection w h a) := by
  apply (fullRelation_isPullback e w h a).of_iso (Iso.refl _)
    (sourceOpenIso w h a) (sourceOpenIso w h a) (Iso.refl _)
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · simp only [Iso.refl_hom, openProjection, Category.comp_id,
      Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, openProjection, Category.comp_id,
      Iso.hom_inv_id_assoc]

end FLT.Mazur.SchemeRelationSplitOrbit
