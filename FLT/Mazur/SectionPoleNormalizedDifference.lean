/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleFrameChange

/-!
# Exact lower-pole corrections between independently normalized lifts

Two actual sections normalized in different frames differ, after the exact
unit scaling, by a unique section of the preceding pole module. The result
does not require either lift to come from the same chosen splitting.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates
variable {X S : Scheme} (p : X ⟶ S) [IsSeparated p]
  (s : S ⟶ X) (hs : s ≫ p = 𝟙 S) (hI : EffectiveCartier s.ker)
  (e f : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S)
  (m : ℕ)
  (x y : ModuleRingH p.appTop.hom
    (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0)

/-- Equal normalized leading terms leave exactly one original lower-pole correction. -/
theorem sectionPoleNormalizedDifference_existsUnique
    (hx : sectionPoleMultiplicativeCoordinates s hI f (m + 1)
      (sectionPoleLeading p s hs hI m x) = 1)
    (hy : sectionPoleMultiplicativeCoordinates s hI e (m + 1)
      (sectionPoleLeading p s hs hI m y) = 1) :
    ∃! z : ModuleRingH p.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0,
      x = (frameComparisonUnit e f ⊤ : Γ(S, ⊤)) ^ (m + 1) • y +
        divisorPowerRingStep p.appTop.hom hI m z := by
  let c : Γ(S, ⊤) := (frameComparisonUnit e f ⊤ : Γ(S, ⊤)) ^ (m + 1)
  have hz : sectionPoleLeading p s hs hI m (x - c • y) = 0 := by
    apply (sectionPoleMultiplicativeCoordinates s hI e (m + 1)).injective
    rw [_root_.map_sub, _root_.map_smul, _root_.map_sub, _root_.map_smul, map_zero,
      sectionPoleMultiplicativeCoordinates_change s hI e f, hx, hy, smul_eq_mul,
      mul_one, sub_self]
  obtain ⟨z, hz⟩ := (sectionPoleLeading_eq_zero_iff p s hs hI m _).mp hz
  refine ⟨z, ?_, ?_⟩
  · change x = c • y + divisorPowerRingStep p.appTop.hom hI m z
    rw [hz]
    abel
  · intro z' hz'
    apply divisorPowerRingStep_injective p.appTop.hom hI m
    rw [hz, eq_sub_iff_add_eq]
    exact (add_comm _ _).trans hz'.symm

end FLT.Mazur.FCurve
