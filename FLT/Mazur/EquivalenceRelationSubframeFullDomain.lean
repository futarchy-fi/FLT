/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeGraphCorrections

/-!
# Full source domains of strict subframe embedding branches

When the entire larger chart maps into the smaller chart, its embedding branch
has exactly that source domain. The actual graph equation is then equivalent
to equality of the original section and the selected pullback, in both directions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (ι : J ↪ I) (h : U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

include h in
/-- The selected graph's domain is the whole source chart, without reduction. -/
theorem mixedSubframeDomain_eq : mixedEmbeddingDomain e o o' U V ι = U := by
  rw [mixedEmbeddingDomain_eq, inf_eq_left.mpr h]

/-- The exact identification of the whole source chart with its selected graph domain. -/
def mixedSubframeSourceIso : U.toScheme ≅ (mixedEmbeddingDomain e o o' U V ι).toScheme :=
  (Scheme.isoOfEq _ (mixedSubframeDomain_eq e o o' U V ι h)).symm

/-- The graph's first projection becomes the identity on the whole source chart. -/
@[reassoc] theorem mixedSubframeSourceIso_first :
    (mixedSubframeSourceIso e o o' U V ι h).hom ≫
      mixedEmbeddingSourceFirst e o o' U V ι = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, mixedEmbeddingSourceFirst_inclusion, Category.id_comp,
    mixedSubframeSourceIso, Iso.symm_hom, Scheme.isoOfEq_inv_ι]

/-- The other projection is exactly the chosen restricted subframe morphism. -/
@[reassoc] theorem mixedSubframeSourceIso_second :
    (mixedSubframeSourceIso e o o' U V ι h).hom ≫
      mixedEmbeddingSourceSecond e o o' U V ι =
        subframeRefinementMap e o o' ι U V h := by
  rw [← mixedEmbeddingSource_refinement e o o' U V ι h, ← Category.assoc,
    mixedSubframeSourceIso_first, Category.id_comp]

/-- The source equation is equivalent to actual equality before any graph restriction. -/
theorem mixedSubframeSource_equation_iff (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤)) :
    (mixedEmbeddingSourceFirst e o o' U V ι).appTop u =
      (mixedEmbeddingSourceSecond e o o' U V ι).appTop v ↔
        u = (subframeRefinementMap e o o' ι U V h).appTop v := by
  let a := (mixedSubframeSourceIso e o o' U V ι h).hom
  have ha : Function.Injective a.appTop := ConcreteCategory.bijective_of_isIso _ |>.injective
  rw [← ha.eq_iff]
  change (a ≫ mixedEmbeddingSourceFirst e o o' U V ι).appTop u =
    (a ≫ mixedEmbeddingSourceSecond e o o' U V ι).appTop v ↔ _
  rw [mixedSubframeSourceIso_first, mixedSubframeSourceIso_second]
  rfl

variable [Etale p]

/-- The full mixed embedding branch equation has the same exact source criterion. -/
theorem mixedSubframeBranch_equation_iff (u : Γ(U.toScheme, ⊤)) (v : Γ(V.toScheme, ⊤)) :
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartFirst o o' U V).appTop u =
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartSecond o o' U V).appTop v ↔
        u = (subframeRefinementMap e o o' ι U V h).appTop v :=
  (mixedEmbedding_equation_iff e o o' U V ι u v).trans
    (mixedSubframeSource_equation_iff e o o' U V ι h u v)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
