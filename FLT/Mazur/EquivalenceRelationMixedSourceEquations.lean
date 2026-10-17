/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedEmbeddingDomains
public import FLT.Mazur.EquivalenceRelationMixedBranchCoefficients

/-!
# The full mixed equation as residual and actual source-open equations

Embedding factors can be checked on the original first-source domains with
their exact subframe maps. The entire residual equation remains a separate
condition. This identifies the finite source equations without claiming an
extension across a residual boundary point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  [(source p q J o').IsSeparated]
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
local notation "M" => mixedChartOpen o o' U V

/-- The first projection on the actual source domain of a specified embedding. -/
def mixedEmbeddingSourceFirst (ι : J ↪ I) :
    (mixedEmbeddingDomain e o o' U V ι).toScheme ⟶ U.toScheme :=
  mixedEmbeddingChartMap e o o' U V ι ≫ mixedChartFirst o o' U V

/-- The independent second projection on the same actual source domain. -/
def mixedEmbeddingSourceSecond (ι : J ↪ I) :
    (mixedEmbeddingDomain e o o' U V ι).toScheme ⟶ V.toScheme :=
  mixedEmbeddingChartMap e o o' U V ι ≫ mixedChartSecond o o' U V

omit [Etale p] [(source p q J o').IsSeparated] in
/-- The first source map is precisely its original open inclusion. -/
@[reassoc] theorem mixedEmbeddingSourceFirst_inclusion (ι : J ↪ I) :
    mixedEmbeddingSourceFirst e o o' U V ι ≫ U.ι =
      (mixedEmbeddingDomain e o o' U V ι).ι := by
  simp only [mixedEmbeddingSourceFirst, mixedChartFirst, Category.assoc,
    Scheme.Hom.resLE_comp_ι, mixedEmbeddingChartMap_inclusion_assoc,
    subframeGraph_fst, Category.comp_id]

omit [Etale p] [(source p q J o').IsSeparated] in
/-- The second source map is precisely the specified original subframe map. -/
@[reassoc] theorem mixedEmbeddingSourceSecond_inclusion (ι : J ↪ I) :
    mixedEmbeddingSourceSecond e o o' U V ι ≫ V.ι =
      (mixedEmbeddingDomain e o o' U V ι).ι ≫ subframeMap e o o' ι := by
  simp only [mixedEmbeddingSourceSecond, mixedChartSecond, Category.assoc,
    Scheme.Hom.resLE_comp_ι, mixedEmbeddingChartMap_inclusion_assoc, subframeGraph_snd]

omit [(source p q J o').IsSeparated] in
/-- Equality on an embedding branch is exactly equality on its actual first-source domain. -/
theorem mixedEmbedding_equation_iff (ι : J ↪ I) (u : Γ(U.toScheme, ⊤))
    (v : Γ(V.toScheme, ⊤)) :
    ((mixedEmbeddingTestOpen e o o' (M).ι ι).ι ≫ mixedChartFirst o o' U V).appTop u =
      ((mixedEmbeddingTestOpen e o o' (M).ι ι).ι ≫ mixedChartSecond o o' U V).appTop v ↔
    (mixedEmbeddingSourceFirst e o o' U V ι).appTop u =
      (mixedEmbeddingSourceSecond e o o' U V ι).appTop v := by
  let h := (mixedEmbeddingDomainIso e o o' U V ι).hom
  have hf : h ≫ (mixedEmbeddingTestOpen e o o' (M).ι ι).ι ≫
      mixedChartFirst o o' U V = mixedEmbeddingSourceFirst e o o' U V ι := by
    rw [← Category.assoc, mixedEmbeddingDomainIso_inclusion]
    rfl
  have hg : h ≫ (mixedEmbeddingTestOpen e o o' (M).ι ι).ι ≫
      mixedChartSecond o o' U V = mixedEmbeddingSourceSecond e o o' U V ι := by
    rw [← Category.assoc, mixedEmbeddingDomainIso_inclusion]
    rfl
  have hh : Function.Injective h.appTop := ConcreteCategory.bijective_of_isIso _ |>.injective
  constructor
  · intro he
    have he' := congrArg (fun a ↦ h.appTop a) he
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf, hg] using he'
  · intro he
    apply hh
    simpa only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hf, hg] using he

/-- No mixed equation is lost when the finite graph equations move to actual source opens. -/
theorem mixedChart_compatible_iff_residual_source (u : Γ(U.toScheme, ⊤))
    (v : Γ(V.toScheme, ⊤)) :
    (mixedChartFirst o o' U V).appTop u = (mixedChartSecond o o' U V).appTop v ↔
    ((mixedResidualTestOpen e o o' (M).ι).ι ≫ mixedChartFirst o o' U V).appTop u =
      ((mixedResidualTestOpen e o o' (M).ι).ι ≫ mixedChartSecond o o' U V).appTop v ∧
    ∀ ι : J ↪ I, (mixedEmbeddingSourceFirst e o o' U V ι).appTop u =
      (mixedEmbeddingSourceSecond e o o' U V ι).appTop v := by
  rw [mixedChart_compatible_iff_branches e o o' U V]
  constructor
  · intro h
    exact ⟨h none, fun ι ↦ (mixedEmbedding_equation_iff e o o' U V ι u v).mp (h (some ι))⟩
  · rintro ⟨hr, hs⟩ a
    cases a with
    | none => exact hr
    | some ι => exact (mixedEmbedding_equation_iff e o o' U V ι u v).mpr (hs ι)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
