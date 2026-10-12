/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionDivisorQuotientLine
public import FLT.Mazur.TensorPowerGeneratorOpen
public import FLT.Mazur.SplitSheafLinePullbackComposition

/-!
# One local frame for all section pole lines

A single affine frame of the divisor line restricted along the section
trivializes every leading line by tensor powers. All degrees therefore use
the same neighborhood and the same degree-one frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {X S : Scheme} (s : S ⟶ X) (hI : EffectiveCartier s.ker)

/-- A single frame of the restricted divisor line induces all leading-line frames. -/
def sectionPoleLineFrame {U : S.Opens}
    (e : ((pullback s).obj (divisorLineBundle s.ker hI)).restrict U.ι ≅
      structureModule U.toScheme) (m : ℕ) :
    (sectionPoleLine s hI m).restrict U.ι ≅ structureModule U.toScheme :=
  (restrictFunctor U.ι).mapIso (tensorPowerIso s (divisorLineBundle s.ker hI) m) ≪≫
    (restrictFunctorIsoPullback U.ι).app _ ≪≫
    tensorPowerIso U.ι ((pullback s).obj (divisorLineBundle s.ker hI)) m ≪≫
    tensorPowerTrivialization
      (((restrictFunctorIsoPullback U.ι).app _).symm ≪≫ e) m

/-- Every base point has one affine frame that controls all pole degrees. -/
theorem sectionPoleLine_affine_frame (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧ Nonempty
      (((pullback s).obj (divisorLineBundle s.ker hI)).restrict U.ι ≅
        structureModule U.toScheme) := by
  let N := (pullback s).obj (divisorLineBundle s.ker hI)
  obtain ⟨V, hxV, ⟨e⟩⟩ := hI.divisorLineBundle_locallyFreeRankOne.pullback s x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  let eV : (pullback V.ι).obj N ≅ structureModule V.toScheme :=
    ((restrictFunctorIsoPullback V.ι).app N).symm ≪≫ e
  exact ⟨U, hxU, hU, ⟨(restrictFunctorIsoPullback (Scheme.Opens.ι (X := S) U)).app N ≪≫
    SplitSheafLinePullback.frameOver (S.homOfLE hUV) V.ι
      (S.homOfLE_ι hUV) eV⟩⟩

/-- The original leading lines in every degree are simultaneously free on one affine open. -/
theorem sectionPoleLines_simultaneously_trivial (x : S) :
    ∃ U : S.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ m : ℕ, Nonempty ((sectionPoleLine s hI m).restrict U.ι ≅ structureModule U.toScheme) := by
  obtain ⟨U, hx, hU, ⟨e⟩⟩ := sectionPoleLine_affine_frame s hI x
  exact ⟨U, hx, hU, fun m ↦ ⟨sectionPoleLineFrame s hI e m⟩⟩

end FLT.Mazur.FCurve
