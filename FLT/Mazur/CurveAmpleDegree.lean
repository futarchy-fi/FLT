/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurvePositiveDegreeAmple
public import FLT.Mazur.FiniteSupportEulerPositive
public import FLT.Mazur.FiniteDivisorComponentAvoidance

/-!
# Ampleness and positive degree on proper integral curves

An ample section generates at the generic point, giving an injection from
the structure line. Its finite-support cokernel is nonzero: otherwise the
whole curve would be affine, hence finite over the field and zero-dimensional.
Its positive Euler characteristic is the degree of the section's line power.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback CoherentDevissage FLT.Mazur.GenericIdealInjection

variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hd : topologicalKrullDim X = 1)

include hd in
/-- Ampleness on a proper integral curve of dimension one forces positive degree. -/
theorem AmpleLineBundle.curveSheafDegree_pos {L : X.Modules} (hL : AmpleLineBundle L) :
    0 < curveSheafDegree f L := by
  have := Chow.source_isNoetherian f
  obtain ⟨n, hn, s, hη, hs⟩ := hL.2.2 (genericPoint X)
  let P := tensorPower L n
  let a := globalSectionHom P s
  have hP := hL.2.1.tensorPower n
  have := hP.isFinitePresentation
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  have : IsIso ((restrictFunctor (sectionGeneratorOpen P s).ι).map a) :=
    inferInstanceAs (IsIso ((restrictFunctor (moduleHomIsoOpen a).ι).map a))
  have := stalk_isIso_of_restrict a (sectionGeneratorOpen P s) (genericPoint X) hη
  have : Mono a := mono_of_generic_mono_of_line_embedding
    structureModule_locallyFreeRankOne (𝟙 (structureModule X)) a
  have hfinite := finite_cokernel_support_of_generic_isIso hd.le a
  have := coherent_cokernel a
  have hne : ¬ IsZero (cokernel a) := by
    intro hz
    have : Epi a := Abelian.epi_of_cokernel_π_eq_zero a (hz.eq_of_tgt _ _)
    have : IsIso a := isIso_of_mono_of_epi a
    have htop : sectionGeneratorOpen P s = ⊤ :=
      top_unique (le_moduleHomIsoOpen a ⊤)
    have haff : IsAffineOpen (⊤ : X.Opens) := htop ▸ hs
    have : IsAffine (⊤ : X.Opens).toScheme := haff
    have : IsAffine X := .of_isIso X.topIso.inv
    have : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
    have hd0 := finiteScheme_dimension_le_zero f
    rw [hd] at hd0
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hd0
  have hpos := finiteSupport_euler_pos f (cokernel a) hfinite hne
  have hadd := curveEulerCharacteristic_add_finiteSupport f
    (ShortComplex.cokernelSequence a) (coherent_cokernelSequence a) hfinite
  have hdeg : 0 < curveSheafDegree f P := by
    change curveEulerCharacteristic f P =
      curveEulerCharacteristic f (structureModule X) + curveEulerCharacteristic f (cokernel a)
      at hadd
    change 0 < curveEulerCharacteristic f P - curveEulerCharacteristic f (structureModule X)
    omega
  rw [curveSheafDegree_line_power f hd.le hL.2.1] at hdeg
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  nlinarith

include hd in
/-- The positive-degree criterion for a proper integral curve (Stacks 0B5X). -/
theorem ampleLineBundle_iff_curveSheafDegree_pos {L : X.Modules}
    (hL : LocallyFreeRankOne L) : AmpleLineBundle L ↔ 0 < curveSheafDegree f L :=
  ⟨fun h ↦ h.curveSheafDegree_pos f hd,
    fun h ↦ ampleLineBundle_of_curveSheafDegree_pos f hd.le hL h⟩

end FLT.Mazur.FCurve
