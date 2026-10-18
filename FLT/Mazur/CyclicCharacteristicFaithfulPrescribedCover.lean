/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryPrescribedCover
public import FLT.Mazur.CyclicCharacteristicRetainedFaithfulness
public import FLT.Mazur.AuxiliaryDistinctSectionParameter

/-!
# Smooth characteristic covers with universally faithful original frames

The original fppf cover and its exact subgroup and generator comparisons
retain universal auxiliary faithfulness. Each frame therefore gives an
actual section of the faithful marking scheme over the original pulled family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- The smooth fppf cover retains universal faithfulness and the specified Cartier generator. -/
theorem exists_faithful_prescribed_characteristic_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (m : ∀ i : C.I₀, Labels (normalizedAuxiliaryOrder (b i)) →*
        (𝟙_ (Over (C.X i)) ⟶ (E.baseChange (C.f i)).group))
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, UniversallyDistinctSections.UniversallyDistinct (fun j ↦ m i j) ∧
        ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange (q i))
          (H.baseChange (C.f i)),
          (∀ j, pullSection (q i) (normalizedAuxiliaryMarking n (b i) j) ≫
            a.curve.hom.group = m i j) ∧
          pullSection (q i) (normalizedGenerator n (b i)) ≫ a.subgroup.hom =
            pullSection (C.f i) P := by
  obtain ⟨C, b, m, q, hq⟩ := exists_auxiliary_prescribed_characteristic_fppf_cover H hP
  refine ⟨C, b, m, q, fun i ↦ ?_⟩
  obtain ⟨_, a, hm, ha⟩ := hq i
  exact ⟨retainedAuxiliary_distinct (H.baseChange (C.f i)) (b i) (q i) a (m i) hm,
    a, hm, ha⟩

end FLT.Mazur.CyclicCharacteristicAtlas
