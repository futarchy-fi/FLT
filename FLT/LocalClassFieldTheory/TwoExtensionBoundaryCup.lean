/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.BoundaryCocycleRepresentatives
public import FLT.LocalClassFieldTheory.TateBoundaryLowDegree
public import FLT.LocalClassFieldTheory.TwoExtensionNegativeEvaluation
public import FLT.LocalClassFieldTheory.TateTwoClassOperation
public import FLT.LocalClassFieldTheory.TateScalarGeneratorComparison

/-!
# Negative connecting maps and the represented two-class

Summing a lifted one-cocycle's differential cancels the two translated sums.
This identifies the negative connecting composite of any two short exact
sequences with the negative cup by their ordinary degree-two class.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology

variable {G : Type} [Group G] [Fintype G]

/-- The sum of a lifted coboundary is the norm of the lift. -/
theorem boundary_two_sum (S : ShortComplex (Rep ℤ G))
    (t : G → S.X₂) (c : cocycles₂ S.X₁)
    (hc : S.f.hom ∘ c = d₁₂ S.X₂ t) (g : G) :
    S.f.hom (twoCocycleSum S.X₁ c g) = S.X₂.norm.hom (t g) := by
  classical
  change S.f.hom (∑ h : G, c (h, g)) = _
  rw [map_sum]
  have he (h : G) : S.f.hom (c (h, g)) =
      S.X₂.ρ h (t g) - t (h * g) + t h := congrFun hc (h, g)
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hr : (∑ h : G, t (h * g)) = ∑ h : G, t h :=
    Equiv.sum_comp (Equiv.mulRight g) t
  rw [hr, sub_add_cancel]
  simp [Rep.norm, Representation.norm]

/-- For an arbitrary coefficient extension, its negative boundary is cup by its H² boundary. -/
theorem boundary_negative_one_eq_cup (S : ShortComplex (Rep ℤ G)) (hS : S.ShortExact)
    (b : cocycles₁ S.X₃) (g : G)
    (hz : (tateComplex S.X₃).d (-1) (-1 + 1) ((chainsIso₀ S.X₃).inv (b g⁻¹)) = 0) :
    TateCohomology.δ hS (-1)
      (tateCocycleClass S.X₃ (-1) ((chainsIso₀ S.X₃).inv (b g⁻¹)) hz) =
    tateTwoClassMap S.X₁ (groupCohomology.δ hS 1 2 rfl (H1π S.X₃ b)) (-2)
      (tateScalarGenerator ℤ G g) := by
  obtain ⟨t, c, ht, hc, he⟩ := boundary_two_representative S hS b
  rw [he, tateTwoClassMap_class, tateTwoExtensionMap_generator]
  exact tate_boundary_negative_one S hS _ hz (t g⁻¹) (congrFun ht g⁻¹)
    (twoCocycleSumInvariant S.X₁ c g⁻¹) (boundary_two_sum S t c hc g⁻¹)

/-- Two genuine negative boundaries recover the cup by the ordinary connecting two-class. -/
theorem twoExtension_boundary_negative_cup
    (M Q X : Rep ℤ G) (i : M ⟶ X) (π : X ⟶ Q) (hi : i ≫ π = 0)
    (hC : (ShortComplex.mk i π hi).ShortExact)
    (Y : Rep ℤ G) (j : Q ⟶ Y) (p : Y ⟶ Rep.trivial ℤ G ℤ) (hj : j ≫ p = 0)
    (hD : (ShortComplex.mk j p hj).ShortExact)
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2)) :
    TateCohomology.δ hC (-1) (TateCohomology.δ hD (-2) x) =
    tateTwoClassMap M
      (groupCohomology.δ hC 1 2 rfl (groupCohomology.δ hD 0 1 rfl
        ((groupCohomology.H0Iso (Rep.trivial ℤ G ℤ)).inv ⟨(1 : ℤ), fun _ => rfl⟩))) (-2) x := by
  obtain ⟨g, rfl⟩ := tateScalarGenerator_surjective G x
  obtain ⟨y, hy⟩ := (Rep.epi_iff_surjective p).mp hD.epi_g (1 : ℤ)
  obtain ⟨b, hb, he⟩ := boundary_one_representative (ShortComplex.mk j p hj) hD
    ⟨(1 : ℤ), fun _ => rfl⟩ y hy
  obtain ⟨hz, hd⟩ := tate_boundary_negative_two (ShortComplex.mk j p hj) hD g
    (1 : ℤ) (tateScalarGenerator_cycle ℤ G g) y hy (b g⁻¹) (congrFun hb g⁻¹)
  change TateCohomology.δ hC (-1)
    (TateCohomology.δ hD (-2) (tateCocycleClass _ (-2) _ _)) = _
  rw [hd, he]
  exact boundary_negative_one_eq_cup (ShortComplex.mk i π hi) hC b g hz

end LocalClassFieldTheory
