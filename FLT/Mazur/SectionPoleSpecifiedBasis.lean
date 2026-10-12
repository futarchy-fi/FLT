/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPoleSplit
public import FLT.Mazur.UnitLeadingBasisExtension

/-!
# Extending the original pole basis by a specified section

Any actual section with unit leading coordinate extends the preceding basis.
No cohomological vanishing or arbitrary choice of a lift is required here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Module
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {X S : Scheme} (f : X ⟶ S) [IsSeparated f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (hI : EffectiveCartier s.ker) (m : ℕ)
  (e : Γ(sectionPoleLine s hI (m + 1), ⊤) ≃ₗ[Γ(S, ⊤)] Γ(S, ⊤))

/-- The original leading map in the specified scalar coordinate. -/
def sectionPoleLeadingCoordinate :
    ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0 →ₗ[Γ(S, ⊤)]
      Γ(S, ⊤) := e.toLinearMap.comp (sectionPoleLeading f s hs hI m)

/-- Passing to a leading coordinate preserves exactness of the original pole sequence. -/
theorem sectionPoleLeadingCoordinate_exact :
    Function.Exact (divisorPowerRingStep f.appTop.hom hI m)
      (sectionPoleLeadingCoordinate f s hs hI m e) := by
  intro x
  change e (sectionPoleLeading f s hs hI m x) = 0 ↔ _
  rw [map_eq_zero_iff e e.injective]
  exact sectionPoleLeading_exact f s hs hI m x

variable {ι : Type} (b : Basis ι Γ(S, ⊤)
    (ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0))
  (v : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0)
  (hv : e (sectionPoleLeading f s hs hI m v) = 1)

/-- Extend the basis by this actual section, retaining both the inclusion and new vector. -/
def sectionPoleSpecifiedBasis : Basis (ι ⊕ Unit) Γ(S, ⊤)
    (ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :=
  UnitLeadingBasisExtension.basis (divisorPowerRingStep f.appTop.hom hI m)
    (sectionPoleLeadingCoordinate f s hs hI m e)
    (divisorPowerRingStep_injective f.appTop.hom hI m)
    (sectionPoleLeadingCoordinate_exact f s hs hI m e) v hv b

/-- Every old vector is included by the original divisor transition. -/
theorem sectionPoleSpecifiedBasis_old (i : ι) :
    sectionPoleSpecifiedBasis f s hs hI m e b v hv (Sum.inl i) =
      divisorPowerRingStep f.appTop.hom hI m (b i) :=
  UnitLeadingBasisExtension.basis_old _ _ _ _ _ _ b i

/-- The new vector is the prescribed section itself. -/
theorem sectionPoleSpecifiedBasis_new :
    sectionPoleSpecifiedBasis f s hs hI m e b v hv (Sum.inr ()) = v :=
  UnitLeadingBasisExtension.basis_new _ _ _ _ _ _ b

/-- Expansion in this basis recovers the original leading coordinate as the last coefficient. -/
theorem sectionPoleSpecifiedBasis_repr_new
    (x : ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) (m + 1)) 0) :
    (sectionPoleSpecifiedBasis f s hs hI m e b v hv).repr x (Sum.inr ()) =
      e (sectionPoleLeading f s hs hI m x) :=
  UnitLeadingBasisExtension.basis_repr_new _ _ _ _ _ _ b x

end FLT.Mazur.FCurve
