/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryFieldNormalization
public import FLT.Mazur.PolygonCyclicBoundaryFieldNode

/-!
# Full component and node ideals in boundary field coordinates

The intrinsic translated component retains the entire original marking ideal.
At each translated node that ideal is the unit ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open PolygonMarkingBaseChange CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n]
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "F" => Over.pullback (g)
variable (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
  CyclicBoundaryParameter.parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "c" => markedSection (G K m) n (g) f (1, 1, j)

/-- The intrinsic translated component retains the full original normalization ideal. -/
theorem extendedComponent_ideal :
    (labelIdeal K m hm p q h n (g) f a i j).comap
      (extendedComponent K L m hm p q h n f j k).left =
        ((PolygonMarkedSections.sectionMap K m p a i).ker.comap
          (componentι K m k ≫ p).left).comap (pullback.fst (component K).hom (g)) := by
  rw [extendedComponent_eq, Over.comp_left, Scheme.IdealSheafData.comap_comp]
  change ((movedMarkingIdeal K m hm p q h (g) (c) a i).comap _).comap _ = _
  rw [movedMarkingIdeal_pullback]
  rw [markingIdeal]
  exact relativeCartierMorphismBaseChange_ideal (componentι K m k ≫ p) (g)
    (PolygonMarkedSections.sectionMap K m p a i).ker _ rfl

/-- Each translated original node avoids the complete marking divisor. -/
theorem extendedNode_ideal :
    (labelIdeal K m hm p q h n (g) f a i j).comap
      (extendedNode K L m hm p q h n f j k).left = ⊤ := by
  rw [extendedNode_eq, labelNode, Scheme.IdealSheafData.comap_comp]
  change ((movedMarkingIdeal K m hm p q h (g) (c) a i).comap _).comap _ = _
  rw [movedMarkingIdeal_pullback]
  exact node_ideal K m hm p q h (g) a i k

end FLT.Mazur.PolygonCyclicBoundary
