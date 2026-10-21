/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryUniformFlatRelation

/-!
# A constructed common original multiplier at a flat branch point

A point of the fixed branch neighborhood gives a single original invariant
scalar outside its original prime. This scalar is chosen before every raw
numerator and every boundary. It simultaneously lifts arbitrary boundary
families solving the full branch equations, without a supplied test ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Y : Scheme.{0}} {p q : D ⟶ A} [IsNoetherian D]
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))
variable (g : Y ⟶ Spec (.of (compatibleFunctions p q)))
  [Flat g] [LocallyOfFinitePresentation g] (V : Y.Opens)
local notation "π" => scalarMorphism σD
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g
local notation "O" => scalarBranchSolutionOpen σD g V
attribute [local irreducible] scalarBranchSolutionOpen scalarMorphism

/-- A usable original principal neighborhood gives a uniform multiplier off the prime. -/
theorem exists_originalRelationMultiplier_off_prime (W : D.Opens)
    (P : PrimeSpectrum (compatibleFunctions p q))
    (hP : P ∈ scalarNeighborhoodLocus σD W) :
    ∃ s : compatibleFunctions p q, s ∉ P.asIdeal ∧
      s ∈ originalRelationMultiplierIdeal (p := p) (q := q) W := by
  obtain ⟨s, hs, hW⟩ := (mem_scalarNeighborhoodLocus_iff σD W P).mp hP
  obtain ⟨N, hN⟩ := exists_uniform_original_relation_multiplier W s hW
  refine ⟨s ^ N, fun hn ↦ hs (P.isPrime.mem_of_pow_mem N hn), ?_⟩
  exact hN

/-- A single original scalar outside the prime works for every boundary numerator on the branch. -/
theorem exists_uniform_originalBoundary_flat_multiplier (y : Y) (hy : y ∈ V) :
    ∃ s : compatibleFunctions p q, s ∉ (g y).asIdeal ∧
      ∀ (J : A.IdealSheafData) (a : Γ(A, ⊤)),
        (pullback π g : Scheme).presheaf.map
          (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
            ((k).appTop (p.appTop a - q.appTop a)) = 0 →
        s ∈ originalBoundaryLiftIdeal (p := p) (q := q) J (J.subschemeι.appTop a) := by
  have hp : g y ∈ scalarNeighborhoodLocus σD O :=
    (mem_scalarNeighborhoodLocus_iff σD O (g y)).mpr
      (exists_scalar_for_branchSolutionOpen σD g V y hy)
  obtain ⟨s, hs, hmult⟩ := exists_originalRelationMultiplier_off_prime O (g y) hp
  refine ⟨s, hs, fun J a ha ↦ ?_⟩
  exact originalRelationMultiplier_mem_liftIdeal O s hmult J a
    (originalRelation_equalizes_on_flat_branch_image g V a ha)

/-- An arbitrary full boundary family shares the constructed original scalar denominator. -/
theorem exists_uniform_originalBoundary_flat_family (y : Y) (hy : y ∈ V)
    (J : A.IdealSheafData) {ι : Type*} (t : ι → Γ(J.subscheme, ⊤))
    (hraw : ∀ i, ∃ a : Γ(A, ⊤), J.subschemeι.appTop a = t i ∧
      (pullback π g : Scheme).presheaf.map
        (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
          ((k).appTop (p.appTop a - q.appTop a)) = 0) :
    ∃ s : compatibleFunctions p q, s ∉ (g y).asIdeal ∧
      ∀ i, ∃ w : compatibleFunctions p q,
        J.subschemeι.appTop w.val = J.subschemeι.appTop s.val * t i := by
  obtain ⟨s, hs, hmult⟩ := exists_uniform_originalBoundary_flat_multiplier g V y hy
  refine ⟨s, hs, fun i ↦ ?_⟩
  obtain ⟨a, ha, he⟩ := hraw i
  obtain ⟨w, hw⟩ := hmult J a he
  exact ⟨w, by rwa [ha] at hw⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
