/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleGlobalSections
public import FLT.Mazur.ModuleSheafTensorAffineOpen
public import FLT.Mazur.CoherentOpenDescent
public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.SchemePicardGroup
public import Mathlib.RingTheory.PicardGroup

/-!
# Global sections of affine Picard classes

Global sections send line bundles on an affine scheme to invertible modules.
The affine reconstruction counit proves that the resulting group map is injective.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.SchemePicard

open FCurve ModuleSheafTensor AffineModuleGlobalSections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- Local rank-one trivializations give finite presentation in every universe. -/
theorem rankOne_finitePresentation (M : X.Modules) (hM : LocallyFreeRankOne M) :
    M.IsFinitePresentation := by
  apply coherent_of_neighborhoods
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x
  exact ⟨U, hx, (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
    e.symm (unitSheaf_isFinitePresentation U.toScheme)⟩

variable [IsAffine X]

/-- Global sections of an affine line bundle form an invertible module. -/
theorem sections_invertible (M : X.Modules) (hM : LocallyFreeRankOne M) :
    Module.Invertible Γ(X, ⊤) Γ(M, ⊤) := by
  have := rankOne_finitePresentation M hM
  have := rankOne_finitePresentation _ hM.dual
  exact Module.Invertible.right
    ((affineSectionsEquiv (moduleSheafDual M) M ⊤ (isAffineOpen_top X)).trans
      (sectionsCongr (lineSheafDualEvaluationIso hM) ⊤))

/-- Global sections of an affine line bundle as a ring Picard class. -/
def sectionsClass (M : X.Modules) (hM : LocallyFreeRankOne M) :
    CommRing.Pic Γ(X, ⊤) :=
  have := sections_invertible M hM
  CommRing.Pic.mk Γ(X, ⊤) Γ(M, ⊤)

/-- Isomorphic line bundles have the same section class. -/
theorem sectionsClass_eq_of_iso {M N : X.Modules}
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) (e : M ≅ N) :
    sectionsClass M hM = sectionsClass N hN := by
  have := sections_invertible M hM
  have := sections_invertible N hN
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨sectionsCongr e ⊤⟩

/-- Affine reconstruction lifts a linear equivalence of sections to a sheaf isomorphism. -/
def isoOfSections {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (e : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤)) : M ≅ N :=
  (asIso ((affineAdjunction X).counit.app M)).symm ≪≫
    (affineTilde X).mapIso e.toModuleIso ≪≫
    asIso ((affineAdjunction X).counit.app N)

/-- Equality of affine section classes detects isomorphism of line bundles. -/
theorem sectionsClass_eq_iff {M N : X.Modules}
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) :
    sectionsClass M hM = sectionsClass N hN ↔ Nonempty (M ≅ N) := by
  have := rankOne_finitePresentation M hM
  have := rankOne_finitePresentation N hN
  have := sections_invertible M hM
  have := sections_invertible N hN
  exact ⟨fun h ↦ ⟨isoOfSections (CommRing.Pic.mk_eq_mk_iff.mp h).some⟩,
    fun ⟨e⟩ ↦ sectionsClass_eq_of_iso hM hN e⟩

/-- The affine tensor comparison respects ring Picard multiplication. -/
theorem sectionsClass_tensor (M N : X.Modules)
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) :
    sectionsClass (tensor M N) (hM.tensor hN) =
      sectionsClass M hM * sectionsClass N hN := by
  have := rankOne_finitePresentation M hM
  have := rankOne_finitePresentation N hN
  have := sections_invertible M hM
  have := sections_invertible N hN
  have := sections_invertible (tensor M N) (hM.tensor hN)
  dsimp [sectionsClass]
  rw [← CommRing.Pic.mk_tensor]
  exact CommRing.Pic.mk_eq_mk_iff.mpr
    ⟨(affineSectionsEquiv M N ⊤ (isAffineOpen_top X)).symm⟩

/-- The injective comparison from scheme Picard classes to ring Picard classes. -/
def sectionsHom (X : Scheme.{u}) [IsAffine X] : Pic X →* CommRing.Pic Γ(X, ⊤) where
  toFun a := Quotient.liftOn a (fun M ↦ sectionsClass M.val M.property)
    (fun _ _ ⟨e⟩ ↦ sectionsClass_eq_of_iso _ _ e)
  map_one' := CommRing.Pic.mk_self
  map_mul' a b := by
    induction a using inductionOn with | h M hM =>
      induction b using inductionOn with | h N hN =>
        exact sectionsClass_tensor M N hM hN

/-- The comparison evaluates to global sections on a representative. -/
@[simp]
theorem sectionsHom_mk (M : X.Modules) (hM : LocallyFreeRankOne M) :
    sectionsHom X (mk M hM) = sectionsClass M hM := rfl

/-- The affine comparison is injective by reconstruction. -/
theorem sectionsHom_injective : Function.Injective (sectionsHom X) := by
  intro a b
  induction a using inductionOn with | h M hM =>
    induction b using inductionOn with | h N hN =>
      exact fun h ↦ (mk_eq_mk_iff hM hN).mpr ((sectionsClass_eq_iff hM hN).mp h)

end FLT.Mazur.SchemePicard
