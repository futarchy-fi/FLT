/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRelabeledPrescribedCover
public import FLT.Mazur.CyclicCharacteristicFaithfulPrescribedCover

/-!
# Universal auxiliary faithfulness on every relabeled smooth chart

The same characteristic cover retains its original frame and every permutation
of it under the common finite relabeling action. The compatible comparisons
also retain all powers of the prescribed original cyclic generator.
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
/-- Universal faithfulness and every original generator power survive common relabeling. -/
theorem exists_faithful_relabeled_characteristic_fppf_cover :
    ∃ (C : Scheme.Cover.{0} Scheme.fppfPrecoverage S) (b : C.I₀ → Bool)
      (m : ∀ i : C.I₀, Labels (normalizedAuxiliaryOrder (b i)) →*
        (𝟙_ (Over (C.X i)) ⟶ (E.baseChange (C.f i)).group))
      (q : ∀ i : C.I₀, C.X i ⟶ normalizedLocus n (b i)),
      ∀ i, UniversallyDistinctSections.UniversallyDistinct (fun j ↦ m i j) ∧
        ∀ e : RelabelGroup n, ∃ a : CompatibleIso ((normalizedSubgroup n (b i)).baseChange
          (q i ≫ (normalizedRelabelAction n (b i) e).hom)) (H.baseChange (C.f i)),
          UniversallyDistinctSections.UniversallyDistinct
            (fun j ↦ m i ((normalizedAuxiliaryRelabel n e (b i)).symm j)) ∧
          (∀ j, pullSection (q i ≫ (normalizedRelabelAction n (b i) e).hom)
            (normalizedAuxiliaryMarking n (b i) j) ≫ a.curve.hom.group =
              m i ((normalizedAuxiliaryRelabel n e (b i)).symm j)) ∧
          ∀ r : ℕ, (pullSection (q i ≫ (normalizedRelabelAction n (b i) e).hom)
            (normalizedGenerator n (b i)) ^ r) ≫ a.subgroup.hom =
              pullSection (C.f i) (P ^ (e.2.2.symm (.ofAdd (r : ZMod n))).toAdd.val) := by
  obtain ⟨C, b, m, q, hq⟩ := exists_faithful_prescribed_characteristic_fppf_cover H hP
  refine ⟨C, b, m, q, fun i ↦ ?_⟩
  obtain ⟨hd, a, hm, ha⟩ := hq i
  refine ⟨hd, fun e ↦ ?_⟩
  obtain ⟨c, hc, hg⟩ := relabeled_prescribed_sections H (C.f i) (b i) (q i) a (m i) hm ha e
  exact ⟨c, retainedAuxiliary_distinct (H.baseChange (C.f i)) (b i)
    (q i ≫ (normalizedRelabelAction n (b i) e).hom) c _ hc, hc, hg⟩

end FLT.Mazur.CyclicCharacteristicAtlas
