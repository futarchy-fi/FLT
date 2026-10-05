/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianSectionRestriction

/-!
# Flat gluing of cartesian section comparisons

The finite tensor equalizer and the sheaf equalizer glue the actual chart
comparisons. Flatness is used only in the tensor equalizer.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules TensorProduct
open scoped ChangeOfRings
namespace FLT.Mazur.FlatCartesianSectionGluing
open Chow FCurve OpenModuleSectionScalars CartesianOpenSectionMap CartesianSectionRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules)
  {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)

/-- Applying a chart comparison to the tensor equalizer restricts the global comparison. -/
lemma equalizer_comparison :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ [Module.Flat Γ(S, ⊤) Γ(T, ⊤)]
      (t : Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections M f.appTop.hom ⊤) (i : ι),
      comparison h M (U i) ((flatSectionEqualizer Γ(T, ⊤) M f.appTop.hom U hU t).val i) =
        baseRestriction ((pullback p).obj M) q.appTop.hom le_top (comparison h M ⊤ t) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro _ t i
  induction t using TensorProduct.inductionOn with
  | add a b ha hb =>
    simp only [map_add, Submodule.coe_add, Pi.add_apply, ha, hb]
  | tmul b m =>
    rw [flatSectionEqualizer_tmul]
    exact (comparison_restrict h M (U i).leTop b m).symm

include hU in
omit [Fintype ι] [DecidableEq ι] in
/-- Affine charts and affine overlaps glue to flat global-section base change. -/
theorem comparison_bijective [Finite ι] [IsAffine T] [IsAffine S] [M.IsQuasicoherent]
    (hA : ∀ i, IsAffineOpen (U i))
    (hI : ∀ i j, IsAffineOpen (U i ⊓ U j)) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    Module.Flat Γ(S, ⊤) Γ(T, ⊤) → Function.Bijective (comparison h M ⊤) := by
  classical
  let := Fintype.ofFinite ι
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro hflat
  let := hflat
  let e := flatSectionEqualizer Γ(T, ⊤) M f.appTop.hom U hU
  have hb (V : X.Opens) (hV : IsAffineOpen V) : Function.Bijective (comparison h M V) := by
    let := comparison_isIso h M V hV
    exact ConcreteCategory.bijective_of_isIso _
  have hc : ⨆ i, p ⁻¹ᵁ U i = ⊤ := p.iSup_preimage_eq_top hU
  let d := baseSectionsEqualizer ((pullback p).obj M) q.appTop.hom (fun i ↦ p ⁻¹ᵁ U i) hc
  constructor
  · intro a b hab
    apply e.injective
    apply Subtype.ext
    funext i
    apply (hb (U i) (hA i)).injective
    rw [equalizer_comparison, equalizer_comparison, hab]
  · intro s
    choose t ht using fun i ↦ (hb (U i) (hA i)).surjective
      (baseRestriction ((pullback p).obj M) q.appTop.hom le_top s)
    have compat (i j : ι) :
        AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
            (baseRestriction M f.appTop.hom inf_le_left) (t i) =
          AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
            (baseRestriction M f.appTop.hom inf_le_right) (t j) := by
      apply (hb (U i ⊓ U j) (hI i j)).injective
      rw [comparison_lTensor, comparison_lTensor, ht, ht]
      change ((pullback p).obj M).presheaf.map _
          (((pullback p).obj M).presheaf.map _ s) =
        ((pullback p).obj M).presheaf.map _
          (((pullback p).obj M).presheaf.map _ s)
      simp only [← Functor.map_comp_apply]
      rfl
    obtain ⟨a, ha, _⟩ := existsUnique_global_tensor Γ(T, ⊤) M f.appTop.hom U hU t compat
    refine ⟨a, ?_⟩
    apply d.injective
    apply Subtype.ext
    funext i
    change baseRestriction ((pullback p).obj M) q.appTop.hom le_top
      (comparison h M ⊤ a) = _
    rw [← equalizer_comparison h M U hU a i, ha]
    exact ht i

end FLT.Mazur.FlatCartesianSectionGluing
