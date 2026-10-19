/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicChartResidualSections
public import FLT.Mazur.CyclicCharacteristicDisjointQuotientReduction
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Residual section rings on the actual finite characteristic quotient

The original finite quotient identifies its full residual invariant ring with
that of the normalized chart. Both equalizers use the complete same-chart
comparison scheme, retaining the arrows beyond finite relabeling.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- Scheme morphisms are determined by pullback along the actual finite quotient. -/
instance normalizedResidualQuotientMap_epi : Epi (normalizedQuotientMap n b) where
  left_cancellation {Z} a c h := by
    obtain ⟨k, _, hk⟩ := normalizedQuotientMap_existsUnique_desc n b
      (normalizedQuotientMap n b ≫ a) (by
        intro g
        rw [← Category.assoc, normalizedQuotientMap_invariant])
    exact (hk a rfl).trans (hk c h.symm).symm

/-- A full same-chart invariant respects each original finite relabeling. -/
theorem chartResidual_morphism_relabel {Y : Scheme} (f : normalizedLocus n b ⟶ Y)
    (hf : productArrowSource n b b ≫ f = productArrowTarget n b b ≫ f)
    (g : RelabelGroup n) : (normalizedRelabelAction n b g).hom ≫ f = f := by
  let q := 𝟙 (normalizedLocus n b) ≫ (normalizedRelabelAction n b g).hom
  let r := 𝟙 (normalizedLocus n b)
  let a := (unmarkedRelated_relabel n b r g).some
  let k : ProductArrow n q r := productCompatibleParameter n b b q r a
  have he := congrArg (k.val ≫ ·) hf
  simpa only [← Category.assoc, productArrow_source, productArrow_target,
    q, r, Category.id_comp] using he

/-- The full residual equalizer inside the section ring of the existing finite quotient. -/
def finiteResidualSections : Subring Γ(normalizedQuotient n b, ⊤) :=
  compatibleFunctions (productArrowSource n b b ≫ normalizedQuotientMap n b)
    (productArrowTarget n b b ≫ normalizedQuotientMap n b)

/-- Pullback from the finite quotient lands in the full chart residual equalizer. -/
def finiteResidualPullback : finiteResidualSections n b →+* chartResidualSections n b := by
  let φ := (normalizedQuotientMap n b).appTop.hom.comp (finiteResidualSections n b).subtype
  exact φ.codRestrict _ (fun s => by
      have h := s.property
      change (productArrowSource n b b ≫ normalizedQuotientMap n b).appTop s.val =
        (productArrowTarget n b b ≫ normalizedQuotientMap n b).appTop s.val at h
      change (productArrowSource n b b).appTop ((normalizedQuotientMap n b).appTop s.val) =
        (productArrowTarget n b b).appTop ((normalizedQuotientMap n b).appTop s.val)
      simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using h)

/-- The finite residual pullback is the original scheme pullback of functions. -/
theorem finiteResidualPullback_val (s : finiteResidualSections n b) :
    (finiteResidualPullback n b s).val = (normalizedQuotientMap n b).appTop s.val := rfl

/-- Every full chart residual invariant descends to the actual finite quotient. -/
theorem finiteResidualPullback_surjective : Function.Surjective (finiteResidualPullback n b) := by
  intro s
  let f := (functionEquiv (normalizedLocus n b)).symm s.val
  have hf : productArrowSource n b b ≫ f = productArrowTarget n b b ≫ f := by
    apply (functionEquiv _).injective
    simp only [functionEquiv_comp, f, Equiv.apply_symm_apply]
    exact s.property
  obtain ⟨k, hk, _⟩ := normalizedQuotientMap_existsUnique_desc n b f
    (chartResidual_morphism_relabel n b f hf)
  let t := functionEquiv (normalizedQuotient n b) k
  have ht : (normalizedQuotientMap n b).appTop t = s.val := by
    rw [← functionEquiv_comp, hk]
    exact (functionEquiv _).apply_symm_apply s.val
  have hi : t ∈ finiteResidualSections n b := by
    change (productArrowSource n b b ≫ normalizedQuotientMap n b).appTop t =
      (productArrowTarget n b b ≫ normalizedQuotientMap n b).appTop t
    simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ht]
    exact s.property
  exact ⟨⟨t, hi⟩, Subtype.ext ht⟩

/-- Passing to the finite quotient retains exactly the full residual ring, with no lost arrows. -/
def finiteResidualSectionsEquiv : finiteResidualSections n b ≃+* chartResidualSections n b :=
  RingEquiv.ofBijective (finiteResidualPullback n b) (by
    constructor
    · intro s t h
      apply Subtype.ext
      exact appTop_injective (normalizedQuotientMap n b) (congrArg Subtype.val h)
    · exact finiteResidualPullback_surjective n b)

/-- The residual equivalence preserves the original section pullback. -/
theorem finiteResidualSectionsEquiv_val (s : finiteResidualSections n b) :
    (finiteResidualSectionsEquiv n b s).val =
      (normalizedQuotientMap n b).appTop s.val := rfl

end FLT.Mazur.CyclicCharacteristicOrbit
