/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechBaseComplex
public import FLT.Mazur.LocalizedHomologyComparison

/-!
# Localizing the actual bounded Cech complex

The localized terms and maps come from the original base-valued complex.
Its explicit positive cohomology is canonically the localization of actual
bounded cohomology, including the localization-ring scalar action.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.IncreasingCechScalars
open AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type u} [CommRing R]
  (ρ : R →+* Γ(X, ⊤)) (S : Submonoid R)

/-- The actual term after localization of its original base action. -/
abbrev LocalTerm (n : ℕ) := LocalizedModule S (BaseTerm M U ρ n)

/-- The actual differential after localization. -/
def localD (n : ℕ) : LocalTerm M U ρ S n →ₗ[Localization S]
    LocalTerm M U ρ S (n + 1) :=
  LocalizedModule.map S (baseD M U ρ n)

/-- The localized differential is computed on fractions by the original one. -/
lemma localD_mk (n : ℕ) (x : BaseTerm M U ρ n) (s : S) :
    localD M U ρ S n (LocalizedModule.mk x s) =
      LocalizedModule.mk (baseD M U ρ n x) s :=
  LocalizedModule.map_mk S _ x s

/-- The localized differentials still form a complex. -/
lemma localD_comp (n : ℕ) :
    (localD M U ρ S (n + 1)).comp (localD M U ρ S n) = 0 := by
  change (LocalizedModule.map S _).comp (LocalizedModule.map S _) = 0
  rw [LocalizedKernelComparison.map_comp, baseD_comp, map_zero]

/-- Localization preserves the original cover's cardinal bound. -/
lemma localTerm_subsingleton [Fintype ι] (n : ℕ) (hn : Fintype.card ι ≤ n) :
    Subsingleton (LocalTerm M U ρ S n) := by
  let _ := baseTerm_subsingleton M U ρ n hn
  infer_instance

/-- Localized actual cohomology agrees with the localized complex's explicit homology. -/
def localPositiveHomologyEquiv (n : ℕ) :
    LocalizedModule S (BaseHomology M U ρ (n + 1)) ≃ₗ[Localization S]
      ((localD M U ρ S (n + 1)).ker ⧸
        (localD M U ρ S n).range.comap (localD M U ρ S (n + 1)).ker.subtype) :=
  (IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S _)
    (LocalizedModule.mkLinearMap S _) (Localization S)
      (basePositiveHomologyEquiv M U ρ n)).trans
    (LocalizedHomologyComparison.homologyEquiv S (baseD M U ρ n)
      (baseD M U ρ (n + 1)) (baseD_comp M U ρ n))

end FLT.Mazur.IncreasingCechScalars
