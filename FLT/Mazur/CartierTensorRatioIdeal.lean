/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenFrameSectionCoordinates
public import FLT.Mazur.SectionPullbackRatioGenerator

/-!
# Exact Cartier ideals from normalized tensor factors

A canonical divisor factor times a generating tensor section cuts out the full
Cartier ideal after division by a generating denominator. This comparison takes
place on the original image open and preserves multiplicity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
  (I : Y.IdealSheafData) (hI : EffectiveCartier I)
local notation "D" => divisorLineBundle I hI

/-- Generation on the image makes every pulled point lie in the generator open. -/
lemma preimage_generator_eq_top_of_image (M : Y.Modules) (s : Γ(M, ⊤))
    (hs : f ''ᵁ ⊤ ≤ sectionGeneratorOpen M s) :
    f ⁻¹ᵁ sectionGeneratorOpen M s = ⊤ := by
  apply top_unique
  intro x _
  exact hs ⟨x, trivial, rfl⟩

/-- Normalizing a single canonical factor retains the original full Cartier ideal. -/
theorem cartierTensorRatio_span (m : ℕ) (t : Γ(tensorPower (D) m, ⊤))
    (y : Γ(tensorPower (D) (m + 1), ⊤))
    (ht : f ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower (D) m) t)
    (hy : f ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower (D) (m + 1)) y)
    (e : (D).restrict f ≅ structureModule X)
    (hA : IsAffineOpen (f ''ᵁ ⊤)) (hC : CartierChart I ⟨f ''ᵁ ⊤, hA⟩) :
    Ideal.span {(sectionRatioOn (tensorPower (D) (m + 1)) y (f ''ᵁ ⊤) hy
      (SectionGradedMultiplication.cons (D) m ⊤ (divisorSection hI ⊤) t))} =
        I.ideal ⟨f ''ᵁ ⊤, hA⟩ := by
  let E := openFramePullback f (D) e
  have hL := hI.divisorLineBundle_locallyFreeRankOne
  have hty := preimage_generator_eq_top_of_image f _ y hy
  have hunit := pulledFrameCoordinate_isUnit f (D) E hL m t
    (preimage_generator_eq_top_of_image f _ t ht)
  have hm : Ideal.map (f.appIso ⊤).hom.hom
      (Ideal.span {(sectionRatioOn (tensorPower (D) (m + 1)) y (f ''ᵁ ⊤) hy
        (SectionGradedMultiplication.cons (D) m ⊤ (divisorSection hI ⊤) t))}) =
          Ideal.map (f.appIso ⊤).hom.hom (I.ideal ⟨f ''ᵁ ⊤, hA⟩) := by
    rw [Ideal.map_span, Set.image_singleton,
      ← pulledTensorRatio_eq_openRatio f (D) E hL (m + 1) y hty hy,
      pulledTensorRatio_span, pulledFrameCoordinate_cons_line,
      Ideal.span_singleton_mul_right_unit hunit]
    exact divisorSection_openFrame_span f I hI e hA hC
  have hc := congrArg (Ideal.comap (f.appIso ⊤).hom.hom) hm
  simpa only [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (f.appIso ⊤).hom)] using hc

/-- On an actual Cartier chart the normalized tensor factor has the original ideal. -/
theorem cartierTensorRatio_span_on
    (U : Y.affineOpens) (hU : CartierChart I U)
    (m : ℕ) (t : Γ(tensorPower (D) m, ⊤))
    (y : Γ(tensorPower (D) (m + 1), ⊤))
    (ht : U.1 ≤ sectionGeneratorOpen (tensorPower (D) m) t)
    (hy : U.1 ≤ sectionGeneratorOpen (tensorPower (D) (m + 1)) y) :
    Ideal.span {(sectionRatioOn (tensorPower (D) (m + 1)) y U.1 hy
      (SectionGradedMultiplication.cons (D) m ⊤ (divisorSection hI ⊤) t))} = I.ideal U := by
  have hA : IsAffineOpen (U.1.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
    exact U.2
  have hC : CartierChart I ⟨U.1.ι ''ᵁ ⊤, hA⟩ := by
    simpa only [Scheme.Opens.ι_image_top] using hU
  have ht' : U.1.ι ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower (D) m) t := by
    simpa only [Scheme.Opens.ι_image_top] using ht
  have hy' : U.1.ι ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower (D) (m + 1)) y := by
    simpa only [Scheme.Opens.ι_image_top] using hy
  have he := congrArg
    (Ideal.map (Y.presheaf.map (homOfLE U.1.ι_image_top.ge).op).hom)
    (cartierTensorRatio_span U.1.ι I hI m t y ht' hy' (hU.divisorTrivialization hI) hA hC)
  rw [Ideal.map_span, Set.image_singleton, sectionRatioOn_restrict] at he
  exact he.trans (I.map_ideal (U := U) (V := ⟨U.1.ι ''ᵁ ⊤, hA⟩) U.1.ι_image_top.ge)

end FLT.Mazur.FCurve
