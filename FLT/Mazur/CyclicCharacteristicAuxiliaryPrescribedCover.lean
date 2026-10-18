/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryPrescribedNeighborhood

/-!
# Both normalized charts retain original auxiliary frames and prescribed generators

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
theorem exists_auxiliary_prescribed_characteristic_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (m : ∀ i : C.I₀, Labels (normalizedAuxiliaryOrder (b i)) →*
        (𝟙_ (Over (C.X i)) ⟶ (E.baseChange (C.f i)).group))
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, Function.Injective (m i) ∧
        ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange (q i))
        (H.baseChange (C.f i)),
        (∀ j, pullSection (q i) (normalizedAuxiliaryMarking n (b i) j) ≫
          a.curve.hom.group = m i j) ∧
        pullSection (q i) (normalizedGenerator n (b i)) ≫ a.subgroup.hom =
          pullSection (C.f i) P := by
  choose U g hg hl hx b m hm q a hmA ha using
    exists_auxiliary_prescribed_characteristic_neighborhood H hP
  let C : Scheme.Cover.{0} Scheme.fppfPrecoverage S :=
    Scheme.Cover.mkOfCovers (P := @Flat ⊓ @LocallyOfFinitePresentation) S U g
      (fun x ↦ ⟨x, hx x⟩) (fun x ↦ ⟨hg x, hl x⟩)
  exact ⟨C, b, m, q, fun i ↦ ⟨hm i, a i, hmA i, ha i⟩⟩

omit [Smooth E.curve.hom] [NeZero n] in
/-- Every retained original auxiliary frame satisfies the chart's full torsion equations. -/
theorem prescribed_characteristic_auxiliary_pow {T : Scheme} (g : T ⟶ S) (b : Bool)
    (m : Labels (normalizedAuxiliaryOrder b) →* (𝟙_ (Over T) ⟶ (E.baseChange g).group))
    (i : Labels (normalizedAuxiliaryOrder b)) : m i ^ normalizedAuxiliaryOrder b = 1 := by
  rw [← map_pow, normalizedAuxiliaryLabels_pow, map_one]

end FLT.Mazur.CyclicCharacteristicAtlas
