/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCartierGeneratorDistinct
public import FLT.Mazur.CartierGeneratorMarkedSubgroup

/-!
# Actual local marked presentations of etale cyclic subgroups

Etaleness proves faithfulness of a Cartier generator. Thus every etale cyclic
subgroup admits, on an fppf cover, a marking that reconstructs that original
subgroup in its original generalized curve. Curve coordinates and auxiliary
level markings are separate atlas constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  (H : E.FiniteSubgroup n) {P : 𝟙_ (Over S) ⟶ H.carrier}

/-- For a Cartier generator, universal distinctness is exactly subgroup etaleness. -/
theorem IsCartierGenerator.etale_iff_distinct (hP : H.IsCartierGenerator P) :
    Etale H.carrier.hom ↔ UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ H.generatorPowers P hP.1 (Multiplicative.ofAdd i)) := by
  constructor
  · intro h
    let _ := h
    exact hP.universallyDistinct H
  · exact H.etale_of_distinct_cartierGenerator hP

variable [Etale H.carrier.hom]

/-- Etaleness supplies the faithful constant presentation of every actual Cartier generator. -/
def etaleGeneratorSplitIso (hP : H.IsCartierGenerator P) :
    ConstantCyclicGroup.model S n ≅ H.carrier :=
  H.generatorSplitIso hP (hP.universallyDistinct H)

/-- The actual etale split presentation preserves the subgroup group law. -/
instance etaleGeneratorSplitIso_isMonHom (hP : H.IsCartierGenerator P) :
    IsMonHom (H.etaleGeneratorSplitIso hP).hom :=
  inferInstanceAs (IsMonHom (H.generatorSplitIso hP (hP.universallyDistinct H)).hom)

/-- Every original cyclic power is retained by the etale presentation. -/
@[reassoc] theorem etaleGeneratorSplitIso_component (hP : H.IsCartierGenerator P) (k : ℕ) :
    ConstantCyclicGroup.component S n (k : ZMod n) ≫ (H.etaleGeneratorSplitIso hP).hom =
      P ^ k := H.generatorSplitIso_component hP (hP.universallyDistinct H) k

/-- Fppf-locally, every actual etale cyclic subgroup has a faithful Cartier generator. -/
theorem IsCyclic.exists_distinct_generator (hH : H.IsCyclic) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
        ∃ (P : 𝟙_ (Over U) ⟶ (H.baseChange g).carrier)
          (hP : (H.baseChange g).IsCartierGenerator P),
          UniversallyDistinctSections.UniversallyDistinct (fun i : ZMod n ↦
            (H.baseChange g).generatorPowers P hP.1 (Multiplicative.ofAdd i)) := by
  obtain ⟨U, g, hf, hs, hl, P, hP⟩ := hH
  let _ : Etale (H.baseChange g).carrier.hom := by
    change Etale (CategoryTheory.Limits.pullback.snd H.carrier.hom g)
    infer_instance
  exact ⟨U, g, hf, hs, hl, P, hP, hP.universallyDistinct (H.baseChange g)⟩

/-- On an fppf cover the original subgroup is reconstructed by actual curve markings. -/
theorem IsCyclic.exists_marked_presentation (hH : H.IsCyclic) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
        ∃ (φ : Multiplicative (ZMod n) →* (𝟙_ (Over U) ⟶ (E.baseChange g).group))
          (hφ : UniversallyDistinctSections.UniversallyDistinct
            (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i))),
          Nonempty (CompatibleIso ((E.baseChange g).relativeCyclicSubgroup φ hφ)
            (H.baseChange g)) := by
  obtain ⟨U, g, hf, hs, hl, P, hP, hd⟩ := hH.exists_distinct_generator H
  exact ⟨U, g, hf, hs, hl, (H.baseChange g).generatorCurveMarking hP,
    (H.baseChange g).generatorCurveMarking_distinct hP hd,
    ⟨(H.baseChange g).generatorMarkedCompatibleIso hP hd⟩⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
