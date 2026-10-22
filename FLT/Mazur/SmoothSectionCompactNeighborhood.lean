/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveSmoothMarking
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Compact smooth neighborhoods of the original marking

Over a compact base the image of a smooth marking lies in a compact open
on which the whole-family structure map is smooth. The whole
curve need not be smooth, and its full smooth locus need not be quasi-compact.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur
universe u

/-- A marking contained in the smooth locus has a compact smooth open neighborhood. -/
theorem exists_compact_smooth_marking_neighborhood {X S : Scheme.{u}} [CompactSpace S]
    (p : X ⟶ S) [LocallyOfFinitePresentation p] (s : S ⟶ X)
    (hs : s ⁻¹ᵁ p.smoothLocus = ⊤) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ s ⁻¹ᵁ U = ⊤ ∧ Smooth (U.ι ≫ p) := by
  have hr : Set.range s ⊆ p.smoothLocus := by
    rintro _ ⟨x, rfl⟩
    exact hs.ge (Set.mem_univ x)
  obtain ⟨V, hVc, hVo, hsV, hVp⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (isCompact_range s.continuous) p.smoothLocus.isOpen hr
  let U : X.Opens := ⟨V, hVo⟩
  refine ⟨U, hVc, ?_, ?_⟩
  · apply top_unique
    intro x _
    exact hsV ⟨x, rfl⟩
  · apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact hVp x.property

/-- Every original group marking over a compact base has such a compact smooth neighborhood. -/
theorem GeneralizedEllipticCurve.exists_smoothMarking_compact_neighborhood
    {S : Scheme} [CompactSpace S] (E : GeneralizedEllipticCurve S)
    (s : 𝟙_ (Over S) ⟶ E.group) :
    ∃ U : E.curve.left.Opens, IsCompact (U : Set E.curve.left) ∧
      (s ≫ E.inclusion).left ⁻¹ᵁ U = ⊤ ∧ Smooth (U.ι ≫ E.curve.hom) := by
  apply exists_compact_smooth_marking_neighborhood (S := S) E.curve.hom
    (s ≫ E.inclusion).left
  change (s.left ≫ E.inclusion.left) ⁻¹ᵁ E.curve.hom.smoothLocus = ⊤
  have : Smooth (E.inclusion.left ≫ E.curve.hom) := by
    rw [E.inclusion.w]
    infer_instance
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    Scheme.Hom.smoothLocus_eq_top]
  simp

end FLT.Mazur
