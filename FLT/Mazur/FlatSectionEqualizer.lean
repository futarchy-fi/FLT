/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessSectionsLocalization
public import FLT.Mazur.FlatFiniteEqualizer

/-!
# Flat scalar extension of the section equalizer

For a finite open cover, flat scalar extension of global sections is exactly
the module of compatible families of scalar-extended local sections. This is
the algebraic equalizer step in flat base change of zeroth cohomology. It does
not yet identify the local tensors with sections on a scheme base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.FCurve
open Chow
variable {X : Scheme} {R : Type} [CommRing R]
  (S : Type) [CommRing S] [Algebra R S]
  (M : X.Modules) (ρ : R →+* Γ(X, ⊤))
  {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)

/-- The overlap difference of the scalar-extended local section modules. -/
def tensorSectionDifference :
    (∀ i, S ⊗[R] baseSections M ρ (U i)) →ₗ[S]
      ∀ ij : ι × ι, S ⊗[R] baseSections M ρ (U ij.1 ⊓ U ij.2) :=
  LinearMap.pi fun ij ↦
    (AlgebraTensorModule.lTensor S S (baseRestriction M ρ inf_le_right)).comp
      (LinearMap.proj ij.2) -
    (AlgebraTensorModule.lTensor S S (baseRestriction M ρ inf_le_left)).comp
      (LinearMap.proj ij.1)

/-- The finite-product comparison respects the actual overlap restriction maps. -/
lemma tensorSectionDifference_eq :
    tensorSectionDifference S M ρ U = finiteProductBaseChange S (baseDifference M ρ U) := by
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := (piRight R S S (fun i ↦ baseSections M ρ (U i))).surjective x
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a m =>
    ext ij
    simp [tensorSectionDifference, finiteProductBaseChange, piRight_apply,
      piRightHom_tmul, piRight_symm_apply, baseDifference, tmul_sub]

/-- Flat scalar extension of actual global sections is the local compatibility kernel. -/
def flatSectionEqualizer [Module.Flat R S] (hU : ⨆ i, U i = ⊤) :
    S ⊗[R] baseSections M ρ ⊤ ≃ₗ[S] (tensorSectionDifference S M ρ U).ker :=
  LinearEquiv.baseChange R S _ _ (baseSectionsEqualizer M ρ U hU) ≪≫ₗ
    flatFiniteKernelEquiv S (baseDifference M ρ U) ≪≫ₗ
      LinearEquiv.ofEq _ _ (congrArg LinearMap.ker (tensorSectionDifference_eq S M ρ U).symm)

/-- The equalizer comparison restricts the original section on every pure tensor. -/
@[simp]
lemma flatSectionEqualizer_tmul [Module.Flat R S] (hU : ⨆ i, U i = ⊤)
    (a : S) (s : baseSections M ρ ⊤) (i : ι) :
    (flatSectionEqualizer S M ρ U hU (a ⊗ₜ[R] s)).val i =
      a ⊗ₜ[R] baseRestriction M ρ (show U i ≤ ⊤ from le_top) s := by
  simp [flatSectionEqualizer, LinearEquiv.coe_ofEq_apply]

/-- Compatible scalar-extended local sections come from a unique global tensor. -/
theorem existsUnique_global_tensor [Module.Flat R S] (hU : ⨆ i, U i = ⊤)
    (s : ∀ i, S ⊗[R] baseSections M ρ (U i))
    (hs : ∀ i j,
      AlgebraTensorModule.lTensor S S (baseRestriction M ρ inf_le_left) (s i) =
      AlgebraTensorModule.lTensor S S (baseRestriction M ρ inf_le_right) (s j)) :
    ∃! t : S ⊗[R] baseSections M ρ ⊤,
      (flatSectionEqualizer S M ρ U hU t).val = s := by
  have hz : s ∈ (tensorSectionDifference S M ρ U).ker := by
    ext ij
    exact sub_eq_zero.mpr (hs ij.1 ij.2).symm
  let z : (tensorSectionDifference S M ρ U).ker := ⟨s, hz⟩
  refine ⟨(flatSectionEqualizer S M ρ U hU).symm z, ?_, ?_⟩
  · exact congrArg Subtype.val ((flatSectionEqualizer S M ρ U hU).apply_symm_apply z)
  · intro t ht
    apply (flatSectionEqualizer S M ρ U hU).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext ht

end FLT.Mazur.FCurve
