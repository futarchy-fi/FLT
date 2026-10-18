/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteAuxiliaryPrescribedCharacteristicCover
public import FLT.Mazur.CyclicCharacteristicRelabeledPrescribedSections

/-!
# Complete-family covers retain original frames under every common relabeling

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
theorem completeOriginal_exists_relabeled_prescribed_characteristic_cover {T : Scheme} (g : T ⟶ B)
    [Smooth ((E).baseChange g).curve.hom] :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage T) (b : C.I₀ → Bool)
      (m : ∀ i : C.I₀, Labels (normalizedAuxiliaryOrder (b i)) →*
        (𝟙_ (Over (C.X i)) ⟶ ((E).baseChange (C.f i ≫ g)).group))
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, Function.Injective (m i) ∧
        ∀ e : RelabelGroup n, ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange
          (q i ≫ (normalizedRelabelAction n (b i) e).hom))
        ((H).baseChange (C.f i ≫ g)),
        (∀ j, pullSection (q i ≫ (normalizedRelabelAction n (b i) e).hom)
          (normalizedAuxiliaryMarking n (b i) j) ≫ a.curve.hom.group =
            m i ((normalizedAuxiliaryRelabel n e (b i)).symm j)) ∧
        ∀ r : ℕ, (pullSection (q i ≫ (normalizedRelabelAction n (b i) e).hom)
          (normalizedGenerator n (b i)) ^ r) ≫ a.subgroup.hom =
            pullSection (C.f i ≫ g) ((P) ^ (e.2.2.symm (.ofAdd (r : ZMod n))).toAdd.val) := by
  obtain ⟨C, b, m, q, hq⟩ :=
    completeOriginal_exists_auxiliary_prescribed_characteristic_cover K n h g
  refine ⟨C, b, m, q, fun i ↦ ?_⟩
  obtain ⟨hm, a, hmA, ha⟩ := hq i
  exact ⟨hm, fun e ↦
    relabeled_prescribed_sections (H) (C.f i ≫ g) (b i) (q i) a (m i) hmA ha e⟩

end FLT.Mazur.PolygonInfinitesimalStages
