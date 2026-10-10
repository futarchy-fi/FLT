/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCoherentVanishing
public import FLT.Mazur.CoherentSubquotient
public import FLT.Mazur.ModuleLineTensorExact
public import FLT.Mazur.ModuleSectionExactness

/-!
# Lifting sections through sufficiently positive twists

The kernel of a coherent quotient is coherent. Serre vanishing for this
actual kernel makes all sufficiently positive twisted section maps
surjective, retaining the original quotient morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleLineBundleTensorPullback ModuleSheafTensorCurrying

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] {L : X.Modules} (hL : AmpleLineBundle L)
  {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation]
  (p : M ⟶ N) [Epi p]

include f hL in
/-- All sufficiently positive twists lift sections through the original coherent quotient. -/
theorem ample_twisted_sections_surjective : ∃ B : ℕ, ∀ d ≥ B,
    Function.Surjective ((ModuleSheafTensor.map p (𝟙 (tensorPower L d))).app ⊤) := by
  let _ := Chow.source_isNoetherian f
  let _ := CoherentDevissage.coherent_kernel p
  obtain ⟨B, hB⟩ := hL.coherent_vanishing f (kernel p)
  refine ⟨B, fun d hd ↦ ?_⟩
  let S := ShortComplex.kernelSequence p
  have hS : S.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact p
      epi_g := inferInstanceAs (Epi p) }
  exact moduleSections_surjective_of_h1 (S.map (tensoring (tensorPower L d)))
    (ModuleLineTensorExact.shortExact S hS _ (hL.2.1.tensorPower d)) (hB d hd 0)

end FLT.Mazur.FCurve
