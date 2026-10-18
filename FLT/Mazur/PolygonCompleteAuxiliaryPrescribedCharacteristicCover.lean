/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAuxiliaryPrescribedCover
public import FLT.Mazur.CyclicCharacteristicPrescribedCover
public import FLT.Mazur.PolygonCompleteNormalizedSubgroupCover

/-!
# Complete-family covers retain independent auxiliary frames and original generators

On arbitrary smooth base changes, the actual two-characteristic normalized
atlas subgroup compares with the direct complete-family subgroup pullback.
The chosen universal generator is the original complete generator, and all
its powers are retained by the same full compatible comparison. Independent
local cubic auxiliary frames descend through the direct-pullback comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open CyclicCharacteristicAtlas GroupSectionBaseChange
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "B" => Spec (CommRingCat.of (PowerSeries K))
local notation "E" => completeGeneralizedCurve K n h
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "P" => completeOriginalGenerator K n h

/-- The direct complete subgroup cover identifies the chosen normalized and original generators. -/
theorem completeOriginal_exists_auxiliary_prescribed_characteristic_cover {T : Scheme} (g : T ⟶ B)
    [Smooth ((E).baseChange g).curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage T) (b : C.I₀ → Bool)
      (m : ∀ i : C.I₀, Labels (normalizedAuxiliaryOrder (b i)) →*
        (𝟙_ (Over (C.X i)) ⟶ ((E).baseChange (C.f i ≫ g)).group))
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, Function.Injective (m i) ∧
        ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange (q i))
        ((H).baseChange (C.f i ≫ g)),
        (∀ j, pullSection (q i) (normalizedAuxiliaryMarking n (b i) j) ≫
          a.curve.hom.group = m i j) ∧
        pullSection (q i) (normalizedGenerator n (b i)) ≫ a.subgroup.hom =
          pullSection (C.f i ≫ g) (P) := by
  obtain ⟨C, b, m, q, hq⟩ :=
    exists_auxiliary_prescribed_characteristic_fppf_cover ((H).baseChange g)
    ((completeOriginalGenerator_isCartierGenerator K n h).baseChange (H) g)
  let m' := fun i ↦ ((compatibleBaseChangeComp (H) g (C.f i)).symm).transportAuxiliary
    (m i)
  refine ⟨C, b, m', q, fun i ↦ ?_⟩
  obtain ⟨hm, a, hmA, ha⟩ := hq i
  refine ⟨((compatibleBaseChangeComp (H) g (C.f i)).symm.transportAuxiliary_injective_iff
    (m i)).mpr hm, a.trans (compatibleBaseChangeComp (H) g (C.f i)).symm, ?_, ?_⟩
  · intro j
    exact CompatibleIso.group_section_trans a (compatibleBaseChangeComp (H) g (C.f i)).symm
      _ (m i j) _ (hmA j) rfl
  · change _ ≫ (a.subgroup.hom ≫ (compatibleBaseChangeComp (H) g (C.f i)).subgroup.inv) = _
    rw [← Category.assoc, ha]
    exact compatibleBaseChangeComp_inv_section (H) g (C.f i) (P)

end FLT.Mazur.PolygonInfinitesimalStages
