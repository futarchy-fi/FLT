/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCoefficientMaps
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Short exact sequences of continuous cochain complexes

Set-theoretic sections between discrete coefficients are continuous. Composing
with these sections proves surjectivity and exactness in every cochain degree.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory HomologicalComplex

variable {k G M P Q : Type u} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction G Q] [SMulCommClass G k Q]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k G M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)
local notation "RQ" => Rep.of (Representation.ofDistribMulAction k G Q)

/-- Injective coefficients give injective maps in each degree. -/
theorem continuousCoefficientMap_injective (φ : RM ⟶ RP) (hφ : Function.Injective φ.hom)
    (n : ℕ) : Function.Injective ((continuousCoefficientMap φ).f n).hom := by
  intro c d h
  apply Subtype.ext
  funext x
  exact hφ (congrArg (fun f => f.val x) h)

/-- Surjective discrete coefficients give surjective maps in each degree. -/
theorem continuousCoefficientMap_surjective (ψ : RP ⟶ RQ) (hψ : Function.Surjective ψ.hom)
    (n : ℕ) : Function.Surjective ((continuousCoefficientMap ψ).f n).hom := by
  intro c
  let s : Q → P := Function.surjInv hψ
  refine ⟨⟨s ∘ c.val, (continuous_of_discreteTopology (f := s)).comp c.property⟩, ?_⟩
  apply Subtype.ext
  funext x
  exact Function.surjInv_eq hψ (c.val x)

/-- Pointwise coefficient exactness lifts to continuous cochain exactness. -/
theorem continuousCoefficientMap_exact (φ : RM ⟶ RP) (ψ : RP ⟶ RQ)
    (h : ∀ y : P, ψ.hom y = 0 ↔ ∃ x : M, φ.hom x = y) (n : ℕ)
    (c : (continuousCochains k G P).X n) (hc : ((continuousCoefficientMap ψ).f n).hom c = 0) :
    ∃ b : (continuousCochains k G M).X n, ((continuousCoefficientMap φ).f n).hom b = c := by
  classical
  let s : P → M := fun y => if hy : ψ.hom y = 0 then Classical.choose ((h y).mp hy) else 0
  refine ⟨⟨s ∘ c.val, (continuous_of_discreteTopology (f := s)).comp c.property⟩, ?_⟩
  apply Subtype.ext
  funext x
  have hx : ψ.hom (c.val x) = 0 := congrArg (fun f => f.val x) hc
  change φ.hom (s (c.val x)) = c.val x
  dsimp [s]
  rw [dite_eq_left hx]
  exact Classical.choose_spec ((h (c.val x)).mp hx)

/-- A zero coefficient composite is zero on continuous cochains. -/
theorem continuousCoefficientMap_comp_zero (φ : RM ⟶ RP) (ψ : RP ⟶ RQ)
    (h : φ ≫ ψ = 0) : continuousCoefficientMap φ ≫ continuousCoefficientMap ψ = 0 := by
  ext n c : 3
  apply Subtype.ext
  funext x
  exact congrArg (fun f : RM ⟶ RQ => f.hom (c.val x)) h

/-- The short complex induced by an actual coefficient complex. -/
def continuousCoefficientShortComplex (φ : RM ⟶ RP) (ψ : RP ⟶ RQ) (h : φ ≫ ψ = 0) :
    ShortComplex (CochainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk (continuousCoefficientMap φ) (continuousCoefficientMap ψ)
    (continuousCoefficientMap_comp_zero φ ψ h)

/-- Short exact discrete coefficients induce a short exact sequence of continuous complexes. -/
theorem continuousCoefficientShortComplex_shortExact (φ : RM ⟶ RP) (ψ : RP ⟶ RQ)
    (h : φ ≫ ψ = 0) (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
    (hex : ∀ y : P, ψ.hom y = 0 ↔ ∃ x : M, φ.hom x = y) :
    (continuousCoefficientShortComplex φ ψ h).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_
           mono_f := (ModuleCat.mono_iff_injective _).mpr
             (continuousCoefficientMap_injective φ hφ n)
           epi_g := (ModuleCat.epi_iff_surjective _).mpr
             (continuousCoefficientMap_surjective ψ hψ n) }
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro c hc
  exact continuousCoefficientMap_exact φ ψ hex n c hc

end LocalClassFieldTheory
