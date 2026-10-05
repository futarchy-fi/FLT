/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedAmpleDescent
public import FLT.Mazur.RelativeAmpleFpqcRefinement
public import FLT.Mazur.RelativeAmpleRestriction

/-!
# Fpqc descent of relative ampleness on proper families

Over an affine base, refine the fpqc covering scheme to an affine faithfully
flat witness and descend the section-open ample predicate. The proper ample
converse recovers closed power presentations. Restriction to affine base
opens gives descent over an arbitrary base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y S T : Scheme.{0}} {f : X ⟶ S} {g : T ⟶ S}
  {p : Y ⟶ X} {q : Y ⟶ T} {L : X.Modules}

/-- Relative ampleness on a proper family descends along fpqc covers of an affine base. -/
theorem RelativeAmple.of_fpqc_affineBase [IsAffine S] [IsProper f]
    [Flat g] [Surjective g] [QuasiCompact g]
    (hA : RelativeAmple q ((pullback p).obj L))
    (hline : LocallyFreeRankOne L) (sq : IsPullback p q f g) : RelativeAmple f L := by
  obtain ⟨Z, hZ, k, hkflat, hksurj, W, a, b, hs, hB⟩ :=
    hA.exists_affine_fpqc_witness hline sq
  let := hZ
  let := hkflat
  let := hksurj
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from f]; infer_instance⟩
  let : Fact (LocallyFreeRankOne L) := ⟨hline⟩
  have hB' := (hB.relativelyAmpleLineBundle (hline.pullback a)).ample_of_affine
  exact ((SectionGradedAmpleDescent.ample_of_pullback hs L hB').relative_of_affine f).relativeAmple

/-- Relative ampleness on a proper family descends along an arbitrary fpqc base change. -/
theorem RelativeAmple.of_fpqc [IsProper f] [Flat g] [Surjective g] [QuasiCompact g]
    (hA : RelativeAmple q ((pullback p).obj L))
    (hline : LocallyFreeRankOne L) (sq : IsPullback p q f g) : RelativeAmple f L := by
  apply RelativelyAmpleLineBundle.relativeAmple
  refine ⟨inferInstance, hline, fun U hU ↦ ?_⟩
  let : IsAffine U.toScheme := hU
  let V := g ⁻¹ᵁ U
  have hle : q ⁻¹ᵁ V ≤ p ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    change (q ≫ g) ⁻¹ᵁ U ≤ (p ≫ f) ⁻¹ᵁ U
    rw [sq.w]
  let p' := p.resLE (f ⁻¹ᵁ U) (q ⁻¹ᵁ V) hle
  have hs : IsPullback p' (q ∣_ V) (f ∣_ U) (g ∣_ U) := by
    simpa only [p', V, Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE sq (le_rfl : V ≤ g ⁻¹ᵁ U)
        (le_rfl : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U) (inf_eq_right.mpr hle).symm
  have : Surjective (g ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U).flip
      (inferInstance : Surjective g)
  have hA' : RelativeAmple (q ∣_ V) ((pullback p').obj (L.restrict (f ⁻¹ᵁ U).ι)) :=
    (hA.restrict (hline.pullback p) V).of_iso
      (modulePullbackRestrictIso p p' (q ⁻¹ᵁ V).ι (f ⁻¹ᵁ U).ι
        (p.resLE_comp_ι hle).symm L).symm
  exact ((hA'.of_fpqc_affineBase (hline.restrict _) hs).relativelyAmpleLineBundle
    (hline.restrict _)).ample_of_affine

/-- Proper-family relative ampleness is fpqc invariant. -/
theorem relativeAmple_fpqc_iff [IsProper f] [Flat g] [Surjective g] [QuasiCompact g]
    (hline : LocallyFreeRankOne L) (sq : IsPullback p q f g) :
    RelativeAmple q ((pullback p).obj L) ↔ RelativeAmple f L :=
  ⟨fun hA ↦ hA.of_fpqc hline sq, fun hA ↦ hA.of_isPullback hline sq⟩

end FLT.Mazur.FCurve
