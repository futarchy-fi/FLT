/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyRing
public import FLT.Mazur.PolygonBoundaryTensorQuotient

/-!
# The short exact sequence of actual boundary reduction

The original adjacent tensor-line map is the quotient by the last parameter
power. The long exact cohomology sequence reduces section lifting to H1
vanishing of this explicit kernel sheaf. Uniform vanishing is a further step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback IdealAdicQuotient GlobalIdealPower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance reductionHasExt (X : Scheme) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) := HasExt.standard _

variable (R : Type) [CommRing R] (m n : ℕ) (h : 2 ≤ n) (d : ℕ)

/-- The actual upper tensor line, parameter-power image and lower tensor line form a complex. -/
def boundaryReductionSequence : ShortComplex (family R (m + 1) n h).left.Modules :=
  ShortComplex.mk
    (inclusion (stageParameterIdeal R (m + 1) n h ^ (m + 1))
      (tensorPower (boundaryLine R (m + 1) n h) d))
    (SectionGradedLinePullback.powerMap (stageRestriction R m n h)
      (adjacentBoundaryLineIso R m n h) d) (by
    rw [← projection_boundaryTensorQuotientIso, ← Category.assoc]
    simp only [projection, cokernel.condition, zero_comp])

/-- The ideal-action cokernel complex is the original adjacent reduction complex. -/
def boundaryReductionSequenceIso :
    ShortComplex.cokernelSequence
      (inclusion (stageParameterIdeal R (m + 1) n h ^ (m + 1))
        (tensorPower (boundaryLine R (m + 1) n h) d)) ≅
      boundaryReductionSequence R m n h d :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (boundaryTensorQuotientIso R m n h d)
    (by simp [boundaryReductionSequence])
    (by simpa [boundaryReductionSequence, projection] using
      (projection_boundaryTensorQuotientIso R m n h d).symm)

/-- The original adjacent boundary tensor-line sequence is short exact. -/
theorem boundaryReductionSequence_shortExact :
    (boundaryReductionSequence R m n h d).ShortExact := by
  apply ShortComplex.shortExact_of_iso (boundaryReductionSequenceIso R m n h d)
  exact { exact := ShortComplex.cokernelSequence_exact _
          mono_f := inferInstanceAs (Mono (inclusion
            (stageParameterIdeal R (m + 1) n h ^ (m + 1))
            (tensorPower (boundaryLine R (m + 1) n h) d))) }

/-- Vanishing of the explicit kernel H1 lifts every actual adjacent H0 class. -/
theorem boundaryReduction_h0_surjective
    (hv : Subsingleton (ModuleH (boundaryReductionSequence R m n h d).X₁ 1)) :
    Function.Surjective (moduleHMap (boundaryReductionSequence R m n h d).g 0) := by
  let S := boundaryReductionSequence R m n h d
  have hs : (moduleAbelianComplex S).ShortExact :=
    CoherentDevissage.moduleToSheaf_shortExact (boundaryReductionSequence_shortExact R m n h d)
  have he : Function.Exact (moduleHMap S.g 0) (moduleHConnecting S hs 0) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' hs 0 1 rfl)
  intro s
  exact (he s).mp (hv.elim _ _)

/-- The same kernel vanishing lifts original sections through the specified line comparison. -/
theorem boundaryReduction_sections_surjective
    (hv : Subsingleton (ModuleH (boundaryReductionSequence R m n h d).X₁ 1)) :
    Function.Surjective
      (SectionGradedLinePullback.sectionMap (stageRestriction R m n h)
        (adjacentBoundaryLineIso R m n h) d ⊤) := by
  intro s
  let S := boundaryReductionSequence R m n h d
  obtain ⟨x, hx⟩ := boundaryReduction_h0_surjective R m n h d hv
    ((moduleH0Equiv S.X₃).symm s)
  refine ⟨moduleH0Equiv S.X₂ x, ?_⟩
  change S.g.app ⊤ (moduleH0Equiv S.X₂ x) = s
  rw [← moduleH0Equiv_naturality, hx]
  exact (moduleH0Equiv S.X₃).apply_symm_apply s

end FLT.Mazur.PolygonInfinitesimalStages
