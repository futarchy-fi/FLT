/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleMultiplicativeCoordinates
public import FLT.Mazur.DivisorSectionGeneratorOpen
public import FLT.Mazur.TensorPowerGeneratorOpen
public import FLT.Mazur.SectionDivisors

/-!
# A unit leading coefficient supplies the missing projective chart

A pole section with leading coefficient one generates along the whole marking.
Together with the canonical divisor power it covers the original total space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {X S : Scheme} (s : S ⟶ X) (hI : EffectiveCartier s.ker)
  (e : (pullback s).obj (divisorLineBundle s.ker hI) ≅ structureModule S)
  (m : ℕ) (x : Γ(tensorPower (divisorLineBundle s.ker hI) m, ⊤))

/-- The basic open of a leading coefficient is the original generator open along the point. -/
theorem sectionPoleCoefficient_basicOpen :
    S.basicOpen (sectionPoleCoefficient s hI e m x) =
      s ⁻¹ᵁ sectionGeneratorOpen (tensorPower (divisorLineBundle s.ker hI) m) x := by
  change S.basicOpen ((tensorPowerTrivialization e m).hom.app ⊤
    ((tensorPowerIso s (divisorLineBundle s.ker hI) m).hom.app ⊤
      (pullGlobal s (tensorPower (divisorLineBundle s.ker hI) m) x))) = _
  rw [← sectionGeneratorOpen_structure, sectionGeneratorOpen_iso,
    sectionGeneratorOpen_iso,
    sectionGeneratorOpen_pullGlobal (hI.divisorLineBundle_locallyFreeRankOne.tensorPower m)]

/-- A normalized leading coefficient makes the original section generate all along the marking. -/
theorem sectionPoleGenerator_contains_marking (hx : sectionPoleCoefficient s hI e m x = 1) :
    Set.range s ⊆ sectionGeneratorOpen (tensorPower (divisorLineBundle s.ker hI) m) x := by
  rintro _ ⟨z, rfl⟩
  have he := sectionPoleCoefficient_basicOpen s hI e m x
  rw [hx, Scheme.basicOpen_one] at he
  exact (show z ∈ s ⁻¹ᵁ sectionGeneratorOpen
    (tensorPower (divisorLineBundle s.ker hI) m) x from he ▸ trivial)

/-- The canonical divisor power and any unit-leading pole section cover the whole family. -/
theorem sectionPoleGenerator_sup (f : X ⟶ S) [IsSeparated f] (hs : s ≫ f = 𝟙 S)
    (hm : 0 < m) (hx : sectionPoleCoefficient s hI e m x = 1) :
    sectionGeneratorOpen (tensorPower (divisorLineBundle s.ker hI) m)
        (tensorPowerSection _ ⊤ (divisorSection hI ⊤) m) ⊔
      sectionGeneratorOpen (tensorPower (divisorLineBundle s.ker hI) m) x = ⊤ := by
  rw [tensorPowerSection_generatorOpen hI.divisorLineBundle_locallyFreeRankOne _ hm,
    divisorSection_generatorOpen]
  apply top_unique
  intro z _
  by_cases hz : z ∈ s.ker.support
  · apply Or.inr
    exact sectionPoleGenerator_contains_marking s hI e m x hx
      ((support_section_ker f s hs) ▸ hz)
  · exact Or.inl hz

end FLT.Mazur.FCurve
