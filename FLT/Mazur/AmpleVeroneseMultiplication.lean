/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleVeroneseEvaluation
public import FLT.Mazur.AmpleTwistedSectionLifting
public import FLT.Mazur.PrincipalSectionExtension
public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.TwistedEvaluationSectionSum
public import FLT.Mazur.SectionGradedRing

/-!
# Eventual multiplication generation in every positive Veronese

One finite family in a retained positive degree generates every sufficiently
high retained degree by actual section multiplication. The family and the
uniform bound are constructed from ampleness and proper coherent vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ProjectiveSpace ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}

/-- The original graded section products generate all sufficiently large retained degrees. -/
theorem AmpleLineBundle.exists_veronese_multiplication_generators
    (f : X ⟶ Spec (.of R)) [IsProper f] {L : X.Modules} (hL : AmpleLineBundle L)
    (q : ℕ) (hq : 0 < q) :
    ∃ a : ℕ, 0 < a ∧ ∃ (I : Type) (_ : Fintype I)
      (s : I → Γ(tensorPower L (q * a), ⊤)),
      ∃ B : ℕ, ∀ d ≥ B, ∀ v : Γ(tensorPower L (q * (a + d)), ⊤),
        ∃ t : I → Γ(tensorPower L (q * d), ⊤),
          of L ⊤ (q * (a + d)) v =
            ∑ i, of L ⊤ (q * a) (s i) * of L ⊤ (q * d) (t i) := by
  obtain ⟨a, ha, I, hI, s, hs⟩ := hL.exists_multiple_finite_evaluation q hq
  let _ := hI
  let _ := Fintype.ofFinite I
  let _ := hs
  let _ := (hL.2.1.tensorPower (q * a)).isFinitePresentation
  obtain ⟨B, hB⟩ := ample_twisted_sections_surjective f hL (globalEvaluation _ s)
  refine ⟨a, ha, I, inferInstance, s, B, fun d hd ↦ ?_⟩
  have hd' : B ≤ q * d := hd.trans (Nat.le_mul_of_pos_left d hq)
  rw [Nat.mul_add]
  intro v
  obtain ⟨t, ht⟩ := section_mul_sum_of_twistedEvaluation_surjective L (q * a) (q * d)
    s (hB (q * d) hd') v
  refine ⟨t, ?_⟩
  rw [ht, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (mul_of L ⊤ (q * a) (q * d) (s i) (t i)).symm

end FLT.Mazur.FCurve
