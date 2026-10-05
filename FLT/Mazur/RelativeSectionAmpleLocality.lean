/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeAmpleRestriction
public import FLT.Mazur.RelativeSectionAmpleBaseChange

/-!
# Base-open locality of relative section ampleness

For quasi-compact separated morphisms, relative ampleness can be checked near
each point of the base. Principal refinement on an arbitrary affine base open
and exact generator extension supply the global ample sections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
variable {X Y S T : Scheme.{0}} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T} {L : X.Modules}

/-- A relatively ample restriction gives ample sections on each affine cartesian piece. -/
theorem ample_cartesian_open_of_relative [IsSeparated q]
    (sq : IsPullback p q f g) (V : S.Opens)
    (hL : RelativelyAmpleLineBundle (f ∣_ V) (L.restrict (f ⁻¹ᵁ V).ι))
    (W : T.Opens) (hW : IsAffineOpen W) (hWV : W ≤ g ⁻¹ᵁ V) :
    AmpleLineBundle (((Scheme.Modules.pullback p).obj L).restrict (q ⁻¹ᵁ W).ι) := by
  let : IsAffine W.toScheme := hW
  have hle : q ⁻¹ᵁ W ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
    exact q.preimage_mono hWV
  let p' := p.resLE (f ⁻¹ᵁ V) (q ⁻¹ᵁ W) hle
  have hs : IsPullback p' (q ∣_ W) (f ∣_ V) (g.resLE V W hWV) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE sq hWV (le_rfl : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V)
        (inf_eq_right.mpr hle).symm
  exact (hL.ample_of_isPullback_affineTarget hs).of_iso
    (modulePullbackRestrictIso p p' (q ⁻¹ᵁ W).ι (f ⁻¹ᵁ V).ι
      (p.resLE_comp_ι hle).symm L)

/-- Relative section ampleness glues from open neighborhoods on an arbitrary base. -/
theorem relativelyAmpleLineBundle_of_base_neighborhoods [QuasiCompact f] [IsSeparated f]
    (hline : LocallyFreeRankOne L)
    (h : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      RelativelyAmpleLineBundle (f ∣_ V) (L.restrict (f ⁻¹ᵁ V).ι)) :
    RelativelyAmpleLineBundle f L := by
  refine ⟨inferInstance, hline, fun U hU ↦ ?_⟩
  let : IsAffine U.toScheme := hU
  let Y := (f ⁻¹ᵁ U).toScheme
  let p := (f ⁻¹ᵁ U).ι
  let q := f ∣_ U
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  have hs : IsPullback p q f U.ι := (isPullback_morphismRestrict f U).flip
  have hA : AmpleLineBundle ((Scheme.Modules.pullback p).obj L) := by
    apply ampleLineBundle_of_principal_neighborhoods (hline.pullback p)
    intro y
    obtain ⟨V, hyV, hV⟩ := h (U.ι (q y))
    obtain ⟨r, hrV, hyr⟩ := (isAffineOpen_top U.toScheme).exists_basicOpen_le
      (⟨q y, hyV⟩ : U.ι ⁻¹ᵁ V) (show q y ∈ (⊤ : U.toScheme.Opens) from trivial)
    refine ⟨q.appTop r, ?_, ?_⟩
    · rw [← Scheme.Hom.preimage_basicOpen_top]
      exact hyr
    · have hW := ample_cartesian_open_of_relative hs V hV (U.toScheme.basicOpen r)
        ((isAffineOpen_top U.toScheme).basicOpen r) hrV
      rwa [Scheme.Hom.preimage_basicOpen_top] at hW
  exact hA.of_iso ((restrictFunctorIsoPullback p).app L)

/-- The relative section predicate is local on the base for separated quasi-compact morphisms. -/
theorem relativelyAmpleLineBundle_iff_base_neighborhoods [QuasiCompact f] [IsSeparated f]
    (hline : LocallyFreeRankOne L) : RelativelyAmpleLineBundle f L ↔
      ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
        RelativelyAmpleLineBundle (f ∣_ V) (L.restrict (f ⁻¹ᵁ V).ι) := by
  refine ⟨fun h s ↦ ⟨⊤, trivial, h.restrict ⊤⟩,
    relativelyAmpleLineBundle_of_base_neighborhoods hline⟩

/-- On a proper family, affine-local closed power presentations glue over base neighborhoods. -/
theorem relativeAmple_of_base_neighborhoods [IsProper f] (hline : LocallyFreeRankOne L)
    (h : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      RelativeAmple (f ∣_ V) (L.restrict (f ⁻¹ᵁ V).ι)) : RelativeAmple f L := by
  apply RelativelyAmpleLineBundle.relativeAmple
  apply relativelyAmpleLineBundle_of_base_neighborhoods hline
  intro s
  obtain ⟨V, hs, hV⟩ := h s
  exact ⟨V, hs, hV.relativelyAmpleLineBundle (hline.restrict _)⟩

end FLT.Mazur.FCurve
