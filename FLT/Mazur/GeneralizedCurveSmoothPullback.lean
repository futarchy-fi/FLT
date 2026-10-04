/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurvePullback

/-!
# Comparing the pulled-back group with the new smooth open

The relative smooth open is smooth. Its pulled-back group is an open
subscheme of the new smooth locus, with a canonical comparison morphism.
Surjectivity of that comparison requires the reverse smooth-locus base-change
inclusion; no such equality is assumed in these constructions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur
variable {S T : Scheme}

/-- The actual smooth open is smooth over its base. -/
instance curveSmoothOpen_smooth (X : Over S) [LocallyOfFinitePresentation X.hom] :
    Smooth (curveSmoothOpen X).hom := by
  change Smooth (X.hom.smoothLocus.ι ≫ X.hom)
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  exact X.hom.smoothLocus.ι_preimage_self

namespace GeneralizedEllipticCurve
variable (E : GeneralizedEllipticCurve S)

instance group_smooth : Smooth E.group.hom := by
  rw [← E.smoothIso.hom.w]
  have : IsIso E.smoothIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map E.smoothIso.hom))
  infer_instance

instance inclusion_open : IsOpenImmersion E.inclusion.left := by
  have : IsIso E.smoothIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map E.smoothIso.hom))
  change IsOpenImmersion (E.smoothIso.hom.left ≫ E.curve.hom.smoothLocus.ι)
  infer_instance

variable (g : T ⟶ S)

instance pullbackCurve_lfp : LocallyOfFinitePresentation (E.pullbackCurve g).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd E.curve.hom g))

instance pullbackGroup_smooth : Smooth (E.pullbackGroup g).hom :=
  inferInstanceAs (Smooth (pullback.snd E.group.hom g))

instance pullbackInclusion_open : IsOpenImmersion (E.pullbackInclusion g).left := by
  change IsOpenImmersion (pullback.map E.group.hom g E.curve.hom g
    E.inclusion.left (𝟙 T) (𝟙 S) (by simp) (by simp))
  infer_instance

/-- The pulled-back group lies in the new relative smooth locus. -/
theorem pullbackInclusion_range_subset :
    Set.range (E.pullbackInclusion g).left ⊆ (E.pullbackCurve g).hom.smoothLocus := by
  rintro _ ⟨y, rfl⟩
  change y ∈ (E.pullbackInclusion g).left ⁻¹ᵁ (E.pullbackCurve g).hom.smoothLocus
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  rw! [Over.w]
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- The canonical open immersion from the pulled-back group into the new smooth open. -/
def smoothPullbackComparison : E.pullbackGroup g ⟶ curveSmoothOpen (E.pullbackCurve g) :=
  Over.homMk (IsOpenImmersion.lift (E.pullbackCurve g).hom.smoothLocus.ι
    (E.pullbackInclusion g).left (by
      change Set.range (E.pullbackInclusion g).left ⊆
        Set.range ((E.pullbackCurve g).hom.smoothLocus.ι :
          (E.pullbackCurve g).hom.smoothLocus.toScheme ⟶ (E.pullbackCurve g).left)
      rw [Scheme.Opens.range_ι]
      exact E.pullbackInclusion_range_subset g)) (by
        change IsOpenImmersion.lift _ _ _ ≫ (_ ≫ _) = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact (E.pullbackInclusion g).w)

/-- The comparison recovers the original pulled-back inclusion. -/
@[reassoc (attr := simp)]
theorem smoothPullbackComparison_inclusion :
    E.smoothPullbackComparison g ≫ curveSmoothInclusion (E.pullbackCurve g) =
      E.pullbackInclusion g := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (E.pullbackCurve g).hom.smoothLocus.ι
    (E.pullbackInclusion g).left _

instance smoothPullbackComparison_open : IsOpenImmersion (E.smoothPullbackComparison g).left := by
  have : IsOpenImmersion ((E.smoothPullbackComparison g).left ≫
      (E.pullbackCurve g).hom.smoothLocus.ι) := by
    change IsOpenImmersion (E.smoothPullbackComparison g ≫
      curveSmoothInclusion (E.pullbackCurve g)).left
    rw [smoothPullbackComparison_inclusion]
    infer_instance
  exact IsOpenImmersion.of_comp _ (E.pullbackCurve g).hom.smoothLocus.ι

end GeneralizedEllipticCurve
end FLT.Mazur
