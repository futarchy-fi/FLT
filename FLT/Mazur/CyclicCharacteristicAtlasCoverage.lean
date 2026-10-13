/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAtlas
public import FLT.Mazur.CharacteristicTwoThreeOpens

/-!
# Original smooth cyclic subgroups are covered in every characteristic

Restrict the original family to D(2) or D(3), then use the actual even or odd
subgroup locus. The full-family comparisons retain the original subgroup.
Only the existing locally noetherian cubic-presentation hypothesis remains.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CharacteristicTwoThree
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsLocallyNoetherian S] {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n) (hc : H.IsCyclic)

include hc in
/-- Every original point has a flat local chart retaining its complete cyclic subgroup. -/
theorem exists_original_neighborhood (x : S) :
    ∃ (U : Scheme) (g : U ⟶ S), Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g ∧ ∃ (b : Bool) (q : U ⟶ locus n b),
        Nonempty (CompatibleIso ((subgroup n b).baseChange q) (H.baseChange g)) := by
  obtain hx | hx := mem_two_or_three S x
  · let B := unitOpen S 2
    let _ : IsLocallyNoetherian B.toScheme := isLocallyNoetherian_of_isOpenImmersion B.ι
    let _ : Smooth (E.baseChange B.ι).curve.hom :=
      inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd E.curve.hom B.ι))
    obtain ⟨C, q, hq⟩ :=
      GeneralizedEllipticCurve.FiniteSubgroup.exists_universal_hom_subgroup_fppf_cover
        (H.baseChange B.ι) (hc.baseChange H B.ι) (unitOpen_isUnit S 2)
    let D : B.toScheme.Cover
        (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := C
    obtain ⟨i, y, hy⟩ := D.exists_eq (⟨x, hx⟩ : B.toScheme)
    let _ : Flat (C.f i) := (D.map_prop i).1
    let _ : LocallyOfFinitePresentation (C.f i) := (D.map_prop i).2
    obtain ⟨a⟩ := hq i
    refine ⟨C.X i, C.f i ≫ B.ι, inferInstance, inferInstance, ?_, false, q i,
      ⟨a.trans (compatibleBaseChangeComp H B.ι (C.f i)).symm⟩⟩
    exact ⟨y, by change B.ι (C.f i y) = x; rw [hy]; rfl⟩
  · let B := unitOpen S 3
    let _ : IsLocallyNoetherian B.toScheme := isLocallyNoetherian_of_isOpenImmersion B.ι
    let _ : Smooth (E.baseChange B.ι).curve.hom :=
      inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd E.curve.hom B.ι))
    obtain ⟨C, q, hq⟩ := OddWeierstrassParameter.exists_universal_hom_subgroup_fppf_cover
      (H.baseChange B.ι) (hc.baseChange H B.ι) (unitOpen_isUnit S 3)
    let D : B.toScheme.Cover
        (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := C
    obtain ⟨i, y, hy⟩ := D.exists_eq (⟨x, hx⟩ : B.toScheme)
    let _ : Flat (C.f i) := (D.map_prop i).1
    let _ : LocallyOfFinitePresentation (C.f i) := (D.map_prop i).2
    obtain ⟨a⟩ := hq i
    refine ⟨C.X i, C.f i ≫ B.ι, inferInstance, inferInstance, ?_, true, q i,
      ⟨a.trans (compatibleBaseChangeComp H B.ι (C.f i)).symm⟩⟩
    exact ⟨y, by change B.ι (C.f i y) = x; rw [hy]; rfl⟩

include hc in
/-- Both original characteristic charts together cover every original smooth cyclic object. -/
theorem exists_original_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (q : ∀ i : C.I₀, C.X i ⟶ locus n (b i)),
      ∀ i, Nonempty (CompatibleIso ((subgroup n (b i)).baseChange (q i))
        (H.baseChange (C.f i))) := by
  choose U g hg hl hx b q hq using exists_original_neighborhood H hc
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, b, q, hq⟩

end FLT.Mazur.CyclicCharacteristicAtlas
