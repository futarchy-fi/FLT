/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertChartFunctions

/-!
# Regular-function descent on every translated chart open

Restrict the actual kernel pair to an arbitrary open of the target. The
restricted pair is again the scheme kernel pair of the restricted smooth
cover. Thus descent identifies all chart section rings, not just global ones,
with the rings of functions satisfying the restricted original relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y P : Scheme.{u}} {g : Y ⟶ X} {a b : P ⟶ Y}
  (H : IsPullback a b g g) (W : X.Opens)

include H in
/-- Both endpoints have the same domain over an actual target open. -/
theorem kernelPair_preimage_open : a ⁻¹ᵁ (g ⁻¹ᵁ W) = b ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w]

/-- The first restricted original endpoint. -/
def openKernelFst : (a ⁻¹ᵁ (g ⁻¹ᵁ W)).toScheme ⟶ (g ⁻¹ᵁ W).toScheme :=
  a.resLE (g ⁻¹ᵁ W) _ le_rfl

/-- The second restricted endpoint on the very same original relation open. -/
def openKernelSnd : (a ⁻¹ᵁ (g ⁻¹ᵁ W)).toScheme ⟶ (g ⁻¹ᵁ W).toScheme :=
  b.resLE (g ⁻¹ᵁ W) _ (kernelPair_preimage_open H W).le

/-- Restriction retains the full scheme kernel pair. -/
theorem openKernel_isPullback :
    IsPullback (openKernelFst (a := a) (g := g) W) (openKernelSnd H W)
      (g ∣_ W) (g ∣_ W) := by
  have h : a ⁻¹ᵁ (g ⁻¹ᵁ W) = a ⁻¹ᵁ (g ⁻¹ᵁ W) ⊓ b ⁻¹ᵁ (g ⁻¹ᵁ W) := by
    rw [kernelPair_preimage_open H W, inf_idem]
  simpa only [openKernelFst, openKernelSnd, Scheme.Hom.resLE_eq_morphismRestrict] using
    Scheme.Hom.isPullback_resLE H (US := W) le_rfl le_rfl h

variable [Flat g] [Surjective g] [LocallyOfFinitePresentation g]

/-- Every actual target section ring is the compatible-function ring on its source inverse image. -/
def openSectionsRingEquiv : Γ(X, W) ≃+*
    compatibleFunctions (openKernelFst (a := a) (g := g) W) (openKernelSnd H W) := by
  let _ : Surjective (g ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance W
  exact W.topIso.symm.commRingCatIsoToRingEquiv.trans
    (sectionsRingEquiv (openKernel_isPullback H W))

end FLT.Mazur.SchemeEffectiveEpiSections

namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f) (W : (acyclicHilbertTest f i.1).left.Opens)

/-- Every open of the actual translated chart has the original restricted invariant functions. -/
def translatedChartOpenFunctionRingEquiv : Γ((acyclicHilbertTest f i.1).left, W) ≃+*
    compatibleFunctions
      (openKernelFst (a := (translatedRestrictedFst f hL i).left)
        (g := (translatedSourceParameter f hL i).left) W)
      (openKernelSnd ((translatedRestricted_isPullback f hL i).map (Over.forget _)) W) :=
  openSectionsRingEquiv (g := (translatedSourceParameter f hL i).left)
    ((translatedRestricted_isPullback f hL i).map (Over.forget _)) W

end FLT.Mazur.HilbertChart
