/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicModularRelation

/-!
# The full closed slice represents isomorphism classes of original chart families

The equivalence uses the genuine full marked group-family relation. The inverse
is the actual inclusion of the original full closed slice, and the equivalence
commutes with arbitrary source change. This is a quotient of the smooth chart;
covering all modular objects by these presentations is a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
variable (n : ℕ) [NeZero n]

/-- Isomorphism of the actual full marked group families is an equivalence relation. -/
def cyclicMarkedFamilySetoid (T : Scheme) : Setoid (T ⟶ (cyclicAuxiliaryScheme n).left) where
  r := CyclicMarkedFamilyRelated n
  iseqv := ⟨fun f ↦ (cyclicMarkedFamilyRelated_iff_slice_eq n f f).mpr rfl,
    fun {f g} h ↦ (cyclicMarkedFamilyRelated_iff_slice_eq n g f).mpr
      ((cyclicMarkedFamilyRelated_iff_slice_eq n f g).mp h).symm,
    fun {f g k} h j ↦ (cyclicMarkedFamilyRelated_iff_slice_eq n f k).mpr
      (((cyclicMarkedFamilyRelated_iff_slice_eq n f g).mp h).trans
        ((cyclicMarkedFamilyRelated_iff_slice_eq n g k).mp j))⟩

/-- Original chart presentations modulo genuine full marked family isomorphisms. -/
def CyclicMarkedFamilyClasses (T : Scheme) := Quotient (cyclicMarkedFamilySetoid n T)

/-- The full original closed slice classifies the genuine full marked chart-family classes. -/
def cyclicMarkedFamilyClassesEquiv (T : Scheme) :
    CyclicMarkedFamilyClasses n T ≃ (T ⟶ cyclicNormalizedSlice n) where
  toFun := Quotient.lift (fun f ↦ f ≫ cyclicNormalizationSliceMap n)
    (fun f g h ↦ (cyclicMarkedFamilyRelated_iff_slice_eq n f g).mp h)
  invFun q := Quotient.mk _ (q ≫ cyclicNormalizedSliceInclusion n)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h f =>
      apply Quotient.sound
      apply (cyclicMarkedFamilyRelated_iff_slice_eq n _ _).mpr
      change ((f ≫ cyclicNormalizationSliceMap n) ≫ cyclicNormalizedSliceInclusion n) ≫
        cyclicNormalizationSliceMap n = f ≫ cyclicNormalizationSliceMap n
      simp only [Category.assoc, cyclicNormalizationSliceMap_retraction, Category.comp_id]
  right_inv q := by
    change (q ≫ cyclicNormalizedSliceInclusion n) ≫ cyclicNormalizationSliceMap n = q
    rw [Category.assoc, cyclicNormalizationSliceMap_retraction, Category.comp_id]

/-- The classifying map retains the original full slice normalization. -/
theorem cyclicMarkedFamilyClassesEquiv_mk {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    cyclicMarkedFamilyClassesEquiv n T (Quotient.mk _ f) =
      f ≫ cyclicNormalizationSliceMap n := rfl

/-- Two actual presentations have the same class exactly when their full families are isomorphic. -/
theorem cyclicMarkedFamilyClasses_mk_eq_iff {T : Scheme}
    (f g : T ⟶ (cyclicAuxiliaryScheme n).left) :
    (Quotient.mk (cyclicMarkedFamilySetoid n T) f = Quotient.mk _ g) ↔
      CyclicMarkedFamilyRelated n f g := Quotient.eq

/-- Pulling back original marked families induces a map of their isomorphism classes. -/
def cyclicMarkedFamilyClassesPullback {T U : Scheme} (k : U ⟶ T) :
    CyclicMarkedFamilyClasses n T → CyclicMarkedFamilyClasses n U :=
  Quotient.map (fun f ↦ k ≫ f) (fun f g h ↦ h.pullback n f g k)

/-- Classification by the full slice is natural in the original source scheme. -/
theorem cyclicMarkedFamilyClassesEquiv_natural {T U : Scheme} (k : U ⟶ T)
    (q : CyclicMarkedFamilyClasses n T) :
    cyclicMarkedFamilyClassesEquiv n U (cyclicMarkedFamilyClassesPullback n k q) =
      k ≫ cyclicMarkedFamilyClassesEquiv n T q := by
  induction q using Quotient.inductionOn with
  | h f => exact Category.assoc k f (cyclicNormalizationSliceMap n)

end FLT.Mazur.UniversalWeierstrass
