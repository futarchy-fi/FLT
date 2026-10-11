/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothOrderedTranslationTests

/-!
# Recovery in the original Picard sheaf on geometric tests

The fixed ordered translations recover the represented class of every
actual line on an algebraically closed fiber. Both quotient and original
sheafification maps are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedCurvePower
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] translationLine ModuleLineBundleTensorPullback.tensorPower
variable {X S : Scheme} [IsAffine S] (f : X ⟶ S) [IsProper f]
  [SmoothOfRelativeDimension 1 f] [GeometricallyIntegral f]
  {B : X.Modules} (hB : AmpleLineBundle B)
  {k : Type} [Field k] [IsAlgClosed k] (g : Spec (.of k) ⟶ S)

include hB in
/-- Every geometric-fiber line is the pullback of a fixed translation class. -/
theorem exists_smoothTranslation_geometric_picard
    (L : LineBundle (pullback f g)) :
    ∃ (i : SmoothTranslationIndex) (a : Over.mk g ⟶ smoothTranslationTest f i),
      SchemePicard.pullback (relativeTotalMap f a) (smoothTranslationPicard f hB.2.1 i) =
        mk L.val L.property := by
  let H := IsPullback.of_hasPullback f g
  obtain ⟨n, d, p, hp, hn, _, he⟩ :=
    exists_geometricFiber_smooth_picard_parameter H hB L.property
  let i : SmoothTranslationIndex := ⟨⟨n, hn⟩, d⟩
  let a : Over.mk g ⟶ smoothTranslationTest f i :=
    Over.homMk (fiberParameter H d p hp) (fiberParameter_base H d p hp)
  refine ⟨i, a, ?_⟩
  have ha : relativeTotalMap f a = fiberCurveMap H d p hp := by
    rfl
  rw [ha]
  dsimp only [smoothTranslationPicard, i]
  exact he

include hB in
/-- The same fixed translations recover the represented section of the original sheaf. -/
theorem exists_smoothTranslation_geometric_class
    (L : LineBundle (pullback f g)) :
    ∃ (i : SmoothTranslationIndex) (a : Over.mk g ⟶ smoothTranslationTest f i),
      (relativeFppfSheaf f).obj.map a.op (smoothTranslationClass f hB.2.1 i) =
        relativeFppfClass f (Over.mk g) (relativeClass _ (mk L.val L.property)) := by
  obtain ⟨i, a, ha⟩ := exists_smoothTranslation_geometric_picard f hB g L
  exact ⟨i, a, by rw [smoothTranslationClass_map, ha]⟩

end FLT.Mazur.OrderedCurvePower
