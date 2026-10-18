/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicTransitionSpan
public import FLT.Mazur.CyclicCharacteristicUnmarkedDescent

/-!
# The residual unmarked relation on the constructed finite quotient

Every invariant of actual full-curve/subgroup comparisons factors uniquely
through the already constructed disjoint finite quotient. Its remaining
condition is precisely invariance of the original lifted unmarked relation,
including the concrete cross-characteristic transition spans.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme}

/-- Restrict a morphism from the actual quotient to an original normalized characteristic chart. -/
def quotientUnmarkedPullback (k : normalizedDisjointQuotient n ⟶ Y) (b : Bool) :
    normalizedLocus n b ⟶ Y :=
  normalizedQuotientMap n b ≫ normalizedDisjointQuotientInclusion n b ≫ k

/-- The remaining relation on quotient morphisms uses the actual lifted compatible comparisons. -/
def QuotientUnmarkedInvariant (k : normalizedDisjointQuotient n ⟶ Y) : Prop :=
  UnmarkedInvariant n (quotientUnmarkedPullback n k)

variable (v : ∀ b, normalizedLocus n b ⟶ Y)

/-- A full unmarked invariant is invariant under every actual finite relabeling. -/
theorem UnmarkedInvariant.relabel (hv : UnmarkedInvariant n v) (b : Bool)
    (g : RelabelGroup n) : (normalizedRelabelAction n b g).hom ≫ v b = v b := by
  have he := hv (normalizedLocus n b) b b
    (𝟙 _ ≫ (normalizedRelabelAction n b g).hom) (𝟙 _)
    (unmarkedRelated_relabel n b (𝟙 _) g)
  simpa only [Category.id_comp] using he

/-- Every full unmarked invariant factors uniquely through the existing single quotient. -/
theorem unmarkedInvariant_quotient_existsUnique (hv : UnmarkedInvariant n v) :
    ∃! k : normalizedDisjointQuotient n ⟶ Y,
      ∀ b, quotientUnmarkedPullback n k b = v b := by
  choose k hk hu using fun b ↦ normalizedQuotientMap_existsUnique_desc n b (v b)
    (UnmarkedInvariant.relabel n v hv b)
  refine ⟨Sigma.desc k, ?_, ?_⟩
  · intro b
    change normalizedQuotientMap n b ≫ (Sigma.ι _ b ≫ Sigma.desc k) = v b
    rw [Sigma.ι_comp_desc, hk]
  · intro l hl
    apply Sigma.hom_ext
    intro b
    rw [Sigma.ι_comp_desc]
    exact hu b (Sigma.ι _ b ≫ l) (hl b)

/-- Full invariance is equivalent to unique factorization with the genuine residual relation. -/
theorem unmarkedInvariant_iff_quotient_desc :
    UnmarkedInvariant n v ↔
      ∃! k : normalizedDisjointQuotient n ⟶ Y,
        (∀ b, quotientUnmarkedPullback n k b = v b) ∧ QuotientUnmarkedInvariant n k := by
  constructor
  · intro hv
    obtain ⟨k, hk, hu⟩ := unmarkedInvariant_quotient_existsUnique n v hv
    refine ⟨k, ⟨hk, ?_⟩, fun l hl ↦ hu l hl.1⟩
    change UnmarkedInvariant n (quotientUnmarkedPullback n k)
    have he : quotientUnmarkedPullback n k = v := funext hk
    rw [he]
    exact hv
  · rintro ⟨k, ⟨hk, hv⟩, _⟩
    have he : quotientUnmarkedPullback n k = v := funext hk
    change UnmarkedInvariant n (quotientUnmarkedPullback n k) at hv
    rwa [he] at hv

/-- The actual cross-characteristic quotient spans are identified by every unmarked invariant. -/
theorem QuotientUnmarkedInvariant.transition (k : normalizedDisjointQuotient n ⟶ Y)
    (hk : QuotientUnmarkedInvariant n k) (b : Bool) (i : (transitionCover n b).I₀) :
    transitionQuotientTarget n b i ≫ k = transitionQuotientSource n b i ≫ k := by
  have he := hk _ (!b) b (transitionTarget n b i) (transitionSource n b i)
    (transition_unmarkedRelated n b i)
  simpa only [transitionQuotientTarget, transitionQuotientSource, quotientUnmarkedPullback,
    Category.assoc] using he

end FLT.Mazur.CyclicCharacteristicAtlas
