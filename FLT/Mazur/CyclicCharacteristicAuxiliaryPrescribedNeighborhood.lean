/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicAuxiliaryPrescribedNormalizedNeighborhood
public import FLT.Mazur.OddWeierstrassCyclicAuxiliaryPrescribedNormalizedNeighborhood
public import FLT.Mazur.CyclicCharacteristicNormalizedGenerator
public import FLT.Mazur.CharacteristicTwoThreeOpens
public import FLT.Mazur.CyclicCharacteristicNormalizedAuxiliary

/-!
# Independently framed prescribed-generator neighborhoods in every characteristic

Restrict the original smooth object to D(2) or D(3). The corresponding actual
normalized chart retains its specified original Cartier generator under a
full compatible comparison with the direct original subgroup pullback.
The original cubic auxiliary frames survive the same comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CharacteristicTwoThree GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- Either actual normalized chart locally retains the original prescribed Cartier generator. -/
theorem exists_auxiliary_prescribed_characteristic_neighborhood (x : S) :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g ∧ ∃ (b : Bool)
        (m : Labels (normalizedAuxiliaryOrder b) →* (𝟙_ (Over U) ⟶ (E.baseChange g).group)),
        Function.Injective m ∧ ∃ q : U ⟶ normalizedLocus n b,
        ∃ a : CompatibleIso ((normalizedSubgroup n b).baseChange q) (H.baseChange g),
          (∀ i, pullSection q (normalizedAuxiliaryMarking n b i) ≫
            a.curve.hom.group = m i) ∧
          pullSection q (normalizedGenerator n b) ≫ a.subgroup.hom = pullSection g P := by
  obtain hx | hx := mem_two_or_three S x
  · let B := unitOpen S 2
    let _ : Smooth (E.baseChange B.ι).curve.hom :=
      inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd E.curve.hom B.ι))
    obtain ⟨U, f, hf, hl, hxf, _, m, hm, q, a, hmA, ha⟩ :=
      (H.baseChange B.ι).exists_auxiliary_prescribed_normalized_neighborhood
        (hP.baseChange H B.ι) (unitOpen_isUnit S 2)
        (V := ⊤) (x := (⟨x, hx⟩ : B.toScheme)) (by trivial)
    let _ := hf
    let _ := hl
    refine ⟨U, f ≫ B.ι, inferInstance, inferInstance, ?_, false,
      ((compatibleBaseChangeComp H B.ι f).symm).transportAuxiliary m,
      ((compatibleBaseChangeComp H B.ι f).symm.transportAuxiliary_injective_iff m).mpr hm,
      q, a.trans (compatibleBaseChangeComp H B.ι f).symm, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := hxf
      exact ⟨u, by change B.ι (f u) = x; rw [hu]; rfl⟩
    · intro i
      exact CompatibleIso.group_section_trans a (compatibleBaseChangeComp H B.ι f).symm
        _ (m i) _ (hmA i) rfl
    · change pullSection q (evenNormalizedGenerator n) ≫
        (a.subgroup.hom ≫ (compatibleBaseChangeComp H B.ι f).subgroup.inv) = _
      rw [← Category.assoc, ha]
      exact compatibleBaseChangeComp_inv_section H B.ι f P
  · let B := unitOpen S 3
    let _ : Smooth (E.baseChange B.ι).curve.hom :=
      inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd E.curve.hom B.ι))
    obtain ⟨U, f, hf, hl, hxf, _, m, hm, q, a, hmA, ha⟩ :=
      OddWeierstrassParameter.exists_auxiliary_prescribed_normalized_neighborhood (H.baseChange B.ι)
        (hP.baseChange H B.ι) (unitOpen_isUnit S 3)
        (V := ⊤) (x := (⟨x, hx⟩ : B.toScheme)) (by trivial)
    let _ := hf
    let _ := hl
    refine ⟨U, f ≫ B.ι, inferInstance, inferInstance, ?_, true,
      ((compatibleBaseChangeComp H B.ι f).symm).transportAuxiliary m,
      ((compatibleBaseChangeComp H B.ι f).symm.transportAuxiliary_injective_iff m).mpr hm,
      q, a.trans (compatibleBaseChangeComp H B.ι f).symm, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := hxf
      exact ⟨u, by change B.ι (f u) = x; rw [hu]; rfl⟩
    · intro i
      exact CompatibleIso.group_section_trans a (compatibleBaseChangeComp H B.ι f).symm
        _ (m i) _ (hmA i) rfl
    · change pullSection q (oddNormalizedGenerator n) ≫
        (a.subgroup.hom ≫ (compatibleBaseChangeComp H B.ι f).subgroup.inv) = _
      rw [← Category.assoc, ha]
      exact compatibleBaseChangeComp_inv_section H B.ι f P

end FLT.Mazur.CyclicCharacteristicAtlas
