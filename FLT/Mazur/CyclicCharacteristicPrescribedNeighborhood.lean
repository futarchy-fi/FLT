/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicOriginalPrescribedNormalizedNeighborhood
public import FLT.Mazur.OddWeierstrassCyclicOriginalPrescribedNormalizedNeighborhood
public import FLT.Mazur.CyclicCharacteristicNormalizedGenerator
public import FLT.Mazur.CharacteristicTwoThreeOpens

/-!
# Prescribed-generator normalized neighborhoods in every characteristic

Restrict the original smooth object to D(2) or D(3). The corresponding actual
normalized chart retains its specified original Cartier generator under a
full compatible comparison with the direct original subgroup pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CharacteristicTwoThree GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

include hP in
/-- Either actual normalized chart locally retains the original prescribed Cartier generator. -/
theorem exists_prescribed_characteristic_neighborhood (x : S) :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g ∧ ∃ (b : Bool) (q : U ⟶ normalizedLocus n b),
        ∃ a : CompatibleIso ((normalizedSubgroup n b).baseChange q) (H.baseChange g),
          pullSection q (normalizedGenerator n b) ≫ a.subgroup.hom = pullSection g P := by
  obtain hx | hx := mem_two_or_three S x
  · let B := unitOpen S 2
    let _ : Smooth (E.baseChange B.ι).curve.hom :=
      inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd E.curve.hom B.ι))
    obtain ⟨U, f, hf, hl, hxf, _, q, a, ha⟩ :=
      (H.baseChange B.ι).exists_prescribed_normalized_neighborhood
        (hP.baseChange H B.ι) (unitOpen_isUnit S 2)
        (V := ⊤) (x := (⟨x, hx⟩ : B.toScheme)) (by trivial)
    let _ := hf
    let _ := hl
    refine ⟨U, f ≫ B.ι, inferInstance, inferInstance, ?_, false, q,
      a.trans (compatibleBaseChangeComp H B.ι f).symm, ?_⟩
    · obtain ⟨u, hu⟩ := hxf
      exact ⟨u, by change B.ι (f u) = x; rw [hu]; rfl⟩
    · change pullSection q (evenNormalizedGenerator n) ≫
        (a.subgroup.hom ≫ (compatibleBaseChangeComp H B.ι f).subgroup.inv) = _
      rw [← Category.assoc, ha]
      exact compatibleBaseChangeComp_inv_section H B.ι f P
  · let B := unitOpen S 3
    let _ : Smooth (E.baseChange B.ι).curve.hom :=
      inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd E.curve.hom B.ι))
    obtain ⟨U, f, hf, hl, hxf, _, q, a, ha⟩ :=
      OddWeierstrassParameter.exists_prescribed_normalized_neighborhood (H.baseChange B.ι)
        (hP.baseChange H B.ι) (unitOpen_isUnit S 3)
        (V := ⊤) (x := (⟨x, hx⟩ : B.toScheme)) (by trivial)
    let _ := hf
    let _ := hl
    refine ⟨U, f ≫ B.ι, inferInstance, inferInstance, ?_, true, q,
      a.trans (compatibleBaseChangeComp H B.ι f).symm, ?_⟩
    · obtain ⟨u, hu⟩ := hxf
      exact ⟨u, by change B.ι (f u) = x; rw [hu]; rfl⟩
    · change pullSection q (oddNormalizedGenerator n) ≫
        (a.subgroup.hom ≫ (compatibleBaseChangeComp H B.ι f).subgroup.inv) = _
      rw [← Category.assoc, ha]
      exact compatibleBaseChangeComp_inv_section H B.ι f P

end FLT.Mazur.CyclicCharacteristicAtlas
