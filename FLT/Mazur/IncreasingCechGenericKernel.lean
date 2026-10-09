/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechLocalization
public import FLT.Mazur.IncreasingCechBaseFlat
public import FLT.Mazur.FlatCokernelStep

/-!
# Generic universal kernel comparison for the actual bounded complex

After one nonzero scalar is inverted, every kernel in the actual bounded
structure complex commutes with arbitrary tensor coefficients. Identifying
these tensors with functions on geometric fibers is a separate geometric step.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.IncreasingCechScalars
open AlgebraicGeometry FCurve Chow.AffineBase

universe u
section General
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι] [Finite ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type u} [CommRing R]
  (ρ : R →+* Γ(X, ⊤)) (S : Submonoid R)
  [∀ n, Module.Flat R (BaseTerm M U ρ n)]

/-- Localized projective cohomology gives universal tensor kernel comparison. -/
theorem local_tensorKer_bijective
    (hH : ∀ n, Module.Projective (Localization S)
      (LocalizedModule S (BaseHomology M U ρ (n + 1))))
    (n : ℕ) (B : Type*) [AddCommGroup B] [Module (Localization S) B] :
    Function.Bijective (LinearMap.tensorKer (Localization S) B (localD M U ρ S n)) := by
  let _ := Fintype.ofFinite ι
  apply FlatCokernelStep.bounded_tensorKer_bijective (LocalTerm M U ρ S)
    (localD M U ρ S) (localD_comp M U ρ S) _ (Fintype.card ι)
    (localTerm_subsingleton M U ρ S) n B
  intro k
  let _ := hH k
  exact Module.Flat.of_linearEquiv (localPositiveHomologyEquiv M U ρ S k).symm

end General

variable {R : CommRingCat.{0}} [IsNoetherianRing R] [IsDomain R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) [IsProper f] [Flat f] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include hU hCover

/-- One generic principal open gives arbitrary-coefficient kernel comparison in every degree. -/
theorem exists_generic_structure_tensorKer_bijective :
    ∃ r : R, r ≠ 0 ∧ ∀ (n : ℕ) (B : Type) [AddCommGroup B] [Module (Localization.Away r) B],
      Function.Bijective (LinearMap.tensorKer (Localization.Away r) B
        (localD (structureModule X) U (baseCohomologyScalars f) (Submonoid.powers r) n)) := by
  let _ := Fintype.ofFinite ι
  let _ := Chow.source_isNoetherian f
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  obtain ⟨r, hr, hH⟩ := exists_generic_projective_cohomology f (structureModule X) U hU hCover
  let _ (n : ℕ) := baseStructureTerm_flat f U hU n
  exact ⟨r, hr, fun n B _ _ ↦ local_tensorKer_bijective (structureModule X) U
    (baseCohomologyScalars f) (Submonoid.powers r) (fun k ↦ hH (k + 1)) n B⟩

end FLT.Mazur.IncreasingCechScalars
