/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularBaseChange

/-!
# Fppf reconstruction of cyclic subgroups across singular families

The original Cartier-generator cover supplies an actual orbit construction
with its full compatible subgroup comparison. No smoothness of the whole
curve, faithful marking, or inversion of the subgroup degree is required.
This reconstructs objects over their original curves; it does not assert that
a universal parameter space for all singular families has been constructed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance singularOrbitCover_smooth {X Y : Scheme}
    (F : GeneralizedEllipticCurve X) [SmoothOfRelativeDimension 1 F.group.hom] (g : Y ⟶ X) :
    SmoothOfRelativeDimension 1 (F.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) F.group.hom g inferInstance

variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)

include hc in
/-- Every cyclic subgroup is fppf locally the full singular orbit construction. -/
theorem exists_singularOrbit_reconstruction :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
      ∃ (φ : Multiplicative (ZMod n) →* (𝟙_ (Over U) ⟶ (E.baseChange g).group))
        (hm : ClosedGroupIdeal.multiplicationEquation (E.baseChange g).group
          ((E.baseChange g).cyclicMarkingGroupIdeal φ) = 0),
        Nonempty (CompatibleIso ((E.baseChange g).singularCyclicDivisorSubgroup φ hm)
          (H.baseChange g)) := by
  obtain ⟨U, g, hf, hs, hl, P, hP⟩ := hc
  exact ⟨U, g, hf, hs, hl, (H.baseChange g).generatorCurveMarking hP,
    (H.baseChange g).generatorMarking_singularMultiplication (E.baseChange g) hP,
    ⟨(H.baseChange g).generatorMarkingSingularCompatibleIso (E.baseChange g) hP⟩⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
