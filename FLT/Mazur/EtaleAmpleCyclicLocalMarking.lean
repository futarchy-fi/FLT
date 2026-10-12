/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCyclicSubgroupLocalPresentation
public import FLT.Mazur.AmpleCyclicClassEtale

/-!
# Local marked coverage of actual etale ample cyclic classes

Every intended ample cyclic object with etale subgroup has an fppf-local
faithful cyclic marking on its original pulled-back curve. The marked subgroup
is compatibly isomorphic to the original subgroup, so the resulting class is
the actual pullback class. No choice of Weierstrass coordinates is presumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} [NeZero n]

/-- The local marked representative retains the original pulled-back curve and ample level. -/
theorem ampleCyclicLevel_exists_etale_marking (a : ampleCyclicLevels S n)
    [Etale a.val.2.carrier.hom] :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
        ∃ (φ : Multiplicative (ZMod n) →*
            (𝟙_ (Over U) ⟶ (a.val.1.baseChange g).group))
          (hφ : UniversallyDistinctSections.UniversallyDistinct
            (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))
          (hc : ((a.val.1.baseChange g).relativeCyclicSubgroup φ hφ).IsCyclic)
          (ha : ((a.val.1.baseChange g).relativeCyclicSubgroup φ hφ).IsAmple),
          Quotient.mk (ampleCyclicLevelSetoid U n)
            ⟨⟨a.val.1.baseChange g, (a.val.1.baseChange g).relativeCyclicSubgroup φ hφ⟩,
              hc, ha⟩ = ampleCyclicClassesPullback g n (Quotient.mk _ a) := by
  obtain ⟨U, g, hf, hs, hl, φ, hφ, ⟨e⟩⟩ :=
    a.property.1.exists_marked_presentation a.val.2
  have hh := e.ampleCyclic_iff.mpr
    ⟨a.property.1.baseChange a.val.2 g, a.property.2.baseChange g⟩
  exact ⟨U, g, hf, hs, hl, φ, hφ, hh.1, hh.2, Quotient.sound ⟨e⟩⟩

/-- Every etale ample cyclic class locally comes from actual faithful cyclic sections. -/
theorem ampleCyclicClass_exists_etale_marking (q : ampleCyclicClasses S n)
    (hq : ampleCyclicClassEtale q) :
    ∃ (U : Scheme) (g : U ⟶ S),
      Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
        ∃ (E : GeneralizedEllipticCurve U)
          (φ : Multiplicative (ZMod n) →* (𝟙_ (Over U) ⟶ E.group))
          (hφ : UniversallyDistinctSections.UniversallyDistinct
            (fun i : ZMod n ↦ φ (Multiplicative.ofAdd i)))
          (hc : (E.relativeCyclicSubgroup φ hφ).IsCyclic)
          (ha : (E.relativeCyclicSubgroup φ hφ).IsAmple),
          Quotient.mk (ampleCyclicLevelSetoid U n)
            ⟨⟨E, E.relativeCyclicSubgroup φ hφ⟩, hc, ha⟩ =
              ampleCyclicClassesPullback g n q := by
  induction q using Quotient.inductionOn with
  | h a =>
    change Etale a.val.2.carrier.hom at hq
    let _ := hq
    obtain ⟨U, g, hf, hs, hl, φ, hφ, hc, ha, he⟩ :=
      ampleCyclicLevel_exists_etale_marking a
    exact ⟨U, g, hf, hs, hl, a.val.1.baseChange g, φ, hφ, hc, ha, he⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
