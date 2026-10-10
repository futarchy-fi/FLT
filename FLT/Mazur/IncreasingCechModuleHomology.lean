/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechBaseComplex
public import FLT.Mazur.FlatScalarHomology

/-!
# Actual bounded Cech homology as module homology

The adjacent differentials form a short complex over the original coefficient
ring. Its categorical homology agrees linearly with actual bounded Cech
cohomology, so flat scalar extension can be applied to that same complex.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechScalars
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type u} [CommRing R]
  (ρ : R →+* Γ(X, ⊤))

/-- The original adjacent bounded differentials as a module short complex. -/
def positiveModuleComplex (n : ℕ) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom (baseD M U ρ n))
    (ModuleCat.ofHom (baseD M U ρ (n + 1))) (by
      apply ModuleCat.hom_ext
      exact baseD_comp M U ρ n)

/-- The categorical incoming image is the original boundary submodule. -/
lemma positiveModuleComplex_boundaries (n : ℕ) :
    (positiveModuleComplex M U ρ n).moduleCatToCycles.range =
      (baseD M U ρ n).range.comap (baseD M U ρ (n + 1)).ker.subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- The module homology object is the actual bounded Cech cohomology with base scalars. -/
def positiveModuleHomologyEquiv (n : ℕ) :
    (positiveModuleComplex M U ρ n).homology ≃ₗ[R] BaseHomology M U ρ (n + 1) :=
  (positiveModuleComplex M U ρ n).moduleCatHomologyIso.toLinearEquiv |>.trans
    ((Submodule.quotEquivOfEq _ _ (positiveModuleComplex_boundaries M U ρ n)).trans
      (basePositiveHomologyEquiv M U ρ n).symm)

variable {S : Type u} [CommRing S] (φ : R →+* S) (hφ : φ.Flat)

/-- Flat extension tensors the original bounded cohomology, retaining the target scalar ring. -/
def flatPositiveHomologyIso (n : ℕ) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (BaseHomology M U ρ (n + 1))) ≅
      ((positiveModuleComplex M U ρ n).map (ModuleCat.extendScalars φ)).homology :=
  (ModuleCat.extendScalars φ).mapIso (positiveModuleHomologyEquiv M U ρ n).toModuleIso.symm ≪≫
    FlatScalarHomology.homologyIso φ hφ (positiveModuleComplex M U ρ n)

end FLT.Mazur.IncreasingCechScalars
