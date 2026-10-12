/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierOriginalSquare
public import FLT.Mazur.SectionCartesianKernel
public import FLT.Mazur.DivisorLinePullback
public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.RelativeVeryAmpleLineBundle

/-!
# Positive point powers in a varying family

The original section ideal, its dual line and every tensor power agree with
those of the retained section on any specified cartesian square. The section
image is flat over the base, so no flatness of the base-change map is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {P X T S : Scheme} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsSeparated f] (h : IsPullback p q f g)
  (s : S ⟶ X) (t : T ⟶ P) (hs : s ≫ f = 𝟙 _) (ht : t ≫ q = 𝟙 _)
  (hst : t ≫ p = g ≫ s) (hI : EffectiveCartier s.ker)

include h hs ht hst hI in
/-- The retained section remains Cartier on the actual new total space. -/
theorem sectionPoint_cartier_baseChange : EffectiveCartier t.ker := by
  rw [← section_ker_comap_of_cartesian h t s ht hs hst]
  exact (relativeCartier_originalSquare h s.ker
    ⟨hI, flat_sectionImage f s hs⟩).1

/-- The actual positive section line commutes with arbitrary base change. -/
def sectionPointLineIso (hJ : EffectiveCartier t.ker) :
    (pullback p).obj (divisorLineBundle s.ker hI) ≅ divisorLineBundle t.ker hJ := by
  let _ := relativeCartierIdealPullback_originalSquare h s.ker
    ⟨hI, flat_sectionImage f s hs⟩
  exact divisorLinePullbackIsoOfEq p hI hJ
    (section_ker_comap_of_cartesian h t s ht hs hst)

/-- The comparison preserves the canonical vanishing section of the original point. -/
@[reassoc] theorem sectionPointLineIso_section (hJ : EffectiveCartier t.ker) :
    (pullback p).map (divisorSectionMap hI) ≫
      (sectionPointLineIso h s t hs ht hst hI hJ).hom =
        (modulePullbackUnitIso p).hom ≫ divisorSectionMap hJ := by
  let _ := relativeCartierIdealPullback_originalSquare h s.ker
    ⟨hI, flat_sectionImage f s hs⟩
  exact divisorLinePullbackIsoOfEq_section p hI hJ
    (section_ker_comap_of_cartesian h t s ht hs hst)

/-- Every pole bound retains the original point-power coefficient sheaf. -/
def sectionPointPowerIso (hJ : EffectiveCartier t.ker) (m : ℕ) :
    (pullback p).obj (tensorPower (divisorLineBundle s.ker hI) m) ≅
      tensorPower (divisorLineBundle t.ker hJ) m :=
  tensorPowerIso p (divisorLineBundle s.ker hI) m ≪≫
    tensorPowerCongr (sectionPointLineIso h s t hs ht hst hI hJ) m

end FLT.Mazur.FCurve
