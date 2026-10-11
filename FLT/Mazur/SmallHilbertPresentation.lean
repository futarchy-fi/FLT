/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmallHilbertTranslationAtlas
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# A locally surjective small Hilbert presentation

The fixed small chart family gives a presheaf of chart lifts and a natural
map to the original Picard sheaf. The constructed original-test covers prove
this map locally surjective for the original fppf topology.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard Approximation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)

/-- The presheaf of lifts into one member of the fixed small chart family. -/
def smallHilbertPresentation : (Over (Spec (.of R)))ᵒᵖ ⥤ Type 1 where
  obj T := ULift (Σ i : SmallHilbertTranslationIndex f, T.unop ⟶ smallHilbertTranslationTest f i)
  map a := ↾fun p ↦ ULift.up ⟨p.down.1, a.unop ≫ p.down.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨i, k⟩⟩
    apply ULift.ext
    exact Sigma.ext rfl (heq_of_eq (Category.id_comp k))
  map_comp a b := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨i, k⟩⟩
    apply ULift.ext
    exact Sigma.ext rfl (heq_of_eq (Category.assoc b.unop a.unop k))

/-- The original Picard class of a chart lift defines the presentation map. -/
def smallHilbertPresentationMap : smallHilbertPresentation f ⟶
    (relativeFppfSheaf f).obj ⋙ forget CommGrpCat where
  app T := ↾fun p ↦ smallHilbertTranslationPoint f hB p.down.1 T.unop p.down.2
  naturality {T U} a := by
    apply ConcreteCategory.hom_ext
    intro p
    exact smallHilbertTranslationPoint_natural f hB p.down.1 a.unop p.down.2

/-- Every original section is locally in the image of the fixed small presentation. -/
instance smallHilbertPresentationMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R)))
      (smallHilbertPresentationMap f hB) where
  imageSieve_mem {T} s := by
    obtain ⟨C, _, hC⟩ := exists_small_hilbert_translation_cover f hB T s
    have hcov : Sieve.ofArrows (relativeCoverMember T C) (relativeCoverArrow T C) ∈
        (Scheme.fppfTopology.over (Spec (.of R))) T := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact Precoverage.generate_mem_toGrothendieck C.mem₀
    apply (Scheme.fppfTopology.over (Spec (.of R))).superset_covering _ hcov
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    intro U a ha
    obtain ⟨j⟩ := ha
    obtain ⟨i, k, hk⟩ := hC j
    exact ⟨ULift.up ⟨i, k⟩, hk⟩

end FLT.Mazur.HilbertChart
