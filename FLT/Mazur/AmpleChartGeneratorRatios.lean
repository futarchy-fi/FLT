/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleChartSectionExtension
public import FLT.Mazur.SectionChartGenerators

/-!
# Chart algebra generators as ratios in one positive degree

The global extensions represent every chosen finite chart generator as an
actual ratio. Their denominators retain exactly the original affine opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback SectionCover
variable {X : Scheme.{u}} {L : X.Modules} {ι : Type v}

/-- Finite chart functions are ratios of global sections in one positive degree. -/
theorem sectionCover_finite_ratios [Finite ι] (hL : LocallyFreeRankOne L)
    (s : ι → Γ(L, ⊤)) (haff : ∀ j, IsAffineOpen (chart s j))
    (hcover : ⨆ j, chart s j = ⊤) {κ : Type*} [Finite κ]
    (i : κ → ι) (a : ∀ k, Γ(X, chart s (i k))) :
    ∃ (D : ℕ) (_ : 0 < D) (σ : κ → Γ(tensorPower L D, ⊤))
      (hD : ∀ j, sectionGeneratorOpen (tensorPower L D) (tensorPowerSection L ⊤ (s j) D) =
        chart s j), ∀ k,
      sectionRatioOn (tensorPower L D) (tensorPowerSection L ⊤ (s (i k)) D)
        (chart s (i k)) (hD (i k)).symm.le (σ k) = a k := by
  obtain ⟨D, hD, σ, hσ⟩ := sectionCover_finite_extension s haff hcover i a
  have hopen (j : ι) := tensorPowerSection_generatorOpen hL (s j) hD
  refine ⟨D, hD, σ, hopen, fun k ↦ ?_⟩
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  rw [tensorPowerSection_restrict, hσ k]

/-- Finite-type chart algebras have finite generator sets whose elements all extend as ratios. -/
theorem sectionCover_algebra_generators [Finite ι] (hL : LocallyFreeRankOne L)
    (s : ι → Γ(L, ⊤)) (haff : ∀ j, IsAffineOpen (chart s j))
    (hcover : ⨆ j, chart s j = ⊤) {R : Type*} [CommRing R]
    (r : ∀ j, R →+* Γ(X, chart s j)) (hr : ∀ j, (r j).FiniteType) :
    ∃ (G : ∀ j, Finset Γ(X, chart s j)) (D : ℕ) (_ : 0 < D)
      (σ : (Σ j, ↥(G j)) → Γ(tensorPower L D, ⊤))
      (hD : ∀ j, sectionGeneratorOpen (tensorPower L D) (tensorPowerSection L ⊤ (s j) D) =
        chart s j),
      (∀ j, Subring.closure (Set.range (r j) ∪ (G j : Set Γ(X, chart s j))) = ⊤) ∧
      ∀ j (a : G j), sectionRatioOn (tensorPower L D) (tensorPowerSection L ⊤ (s j) D)
        (chart s j) (hD j).symm.le (σ ⟨j, a⟩) = a.val := by
  classical
  choose G hG using fun j ↦ finiteType_ring_generators (r j) (hr j)
  obtain ⟨D, hD, σ, hopen, hσ⟩ := sectionCover_finite_ratios hL s haff hcover
    (fun k : Σ j, ↥(G j) ↦ k.1) (fun k ↦ k.2.val)
  exact ⟨G, D, hD, σ, hopen, hG, fun j a ↦ hσ ⟨j, a⟩⟩

end FLT.Mazur.FCurve
