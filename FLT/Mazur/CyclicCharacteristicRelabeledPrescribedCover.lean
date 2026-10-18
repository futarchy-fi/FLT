/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryPrescribedCover
public import FLT.Mazur.CyclicCharacteristicRelabeledPrescribedSections

/-!
# Characteristic covers retain original sections under every common relabeling

The characteristic neighborhoods assemble into a small fppf cover. On every
member the actual atlas subgroup compares with the original full subgroup,
carrying the chosen atlas generator and all its powers to the prescribed ones.
The independent original cubic auxiliary frames remain faithful on every member.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- A small fppf cover by both actual charts retains the specified original generator. -/
theorem exists_relabeled_auxiliary_prescribed_characteristic_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (m : ∀ i : C.I₀, Labels (normalizedAuxiliaryOrder (b i)) →*
        (𝟙_ (Over (C.X i)) ⟶ (E.baseChange (C.f i)).group))
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, Function.Injective (m i) ∧
        ∀ e : RelabelGroup n, ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange
          (q i ≫ (normalizedRelabelAction n (b i) e).hom))
        (H.baseChange (C.f i)),
        (∀ j, pullSection (q i ≫ (normalizedRelabelAction n (b i) e).hom)
          (normalizedAuxiliaryMarking n (b i) j) ≫ a.curve.hom.group =
            m i ((normalizedAuxiliaryRelabel n e (b i)).symm j)) ∧
        ∀ r : ℕ, (pullSection (q i ≫ (normalizedRelabelAction n (b i) e).hom)
          (normalizedGenerator n (b i)) ^ r) ≫ a.subgroup.hom =
            pullSection (C.f i) (P ^ (e.2.2.symm (.ofAdd (r : ZMod n))).toAdd.val) := by
  obtain ⟨C, b, m, q, hq⟩ := exists_auxiliary_prescribed_characteristic_fppf_cover H hP
  refine ⟨C, b, m, q, fun i ↦ ?_⟩
  obtain ⟨hm, a, hmA, ha⟩ := hq i
  exact ⟨hm, fun e ↦ relabeled_prescribed_sections H (C.f i) (b i) (q i) a (m i) hmA ha e⟩

end FLT.Mazur.CyclicCharacteristicAtlas
