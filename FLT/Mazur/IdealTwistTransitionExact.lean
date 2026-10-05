/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionGenericOpen
public import FLT.Mazur.IdealTwistCohomologySystem
public import FLT.Mazur.IdealTwistSectionOpen

/-!
# Exactness of ideal-twist transitions

A line sheaf detects zero morphisms at the generic point. The ideal twist
embeds into a line, so a generically invertible transition is injective.
Its finite-support quotient then makes the positive cohomology map surjective.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open FLT.Mazur.GenericIdealInjection CoherentDevissage

variable {X : Scheme} [IsIntegral X]

/-- A line target detects zero morphisms on the generic stalk. -/
theorem line_map_eq_zero_of_generic {M L : X.Modules} (hL : LocallyFreeRankOne L)
    (a : M ⟶ L) (ha : (stalk (genericPoint X)).map a = 0) : a = 0 := by
  choose U hx e using hL
  apply FLT.Mazur.ModuleSheafMorphismGluing.hom_ext_restrict U (by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩)
  intro x
  have : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  let y := genericPoint (U x).toScheme
  have hy : (U x).ι y = genericPoint X := genericPoint_eq_of_isOpenImmersion (U x).ι
  have hz : (stalk y).map ((restrictFunctor (U x).ι).map a) = 0 := by
    apply (cancel_mono ((restrictStalkNatIso (U x).ι y).hom.app L)).mp
    rw [zero_comp]
    have hn := (restrictStalkNatIso (U x).ι y).hom.naturality a
    change (stalk y).map ((restrictFunctor (U x).ι).map a) ≫ _ =
      (restrictStalkNatIso (U x).ι y).hom.app M ≫ (stalk ((U x).ι y)).map a at hn
    have ha' : (stalk ((U x).ι y)).map a = 0 := by rw [hy]; exact ha
    rw [hn, ha', comp_zero]
  apply (cancel_mono (e x).some.hom).mp
  rw [Functor.map_zero, zero_comp]
  apply structure_map_eq_zero
  rw [Functor.map_comp, hz, zero_comp]

/-- An embedding into a line makes generic injectivity sufficient for injectivity. -/
theorem mono_of_generic_mono_of_line_embedding {M N L : X.Modules}
    (hL : LocallyFreeRankOne L) (i : M ⟶ L) [Mono i]
    (a : M ⟶ N) [Mono ((stalk (genericPoint X)).map a)] : Mono a := by
  apply Preadditive.mono_of_cancel_zero
  intro P b hb
  have hz : (stalk (genericPoint X)).map b = 0 := by
    apply (cancel_mono ((stalk (genericPoint X)).map a)).mp
    rw [zero_comp, ← Functor.map_comp, hb, Functor.map_zero]
  apply (cancel_mono i).mp
  rw [zero_comp]
  apply line_map_eq_zero_of_generic hL
  rw [Functor.map_comp, hz, zero_comp]

namespace LineSectionTwistSystem

open ModuleSheafTensor ModuleLineBundleTensorPullback
open CoherentDevissage FLT.Mazur.GlobalIdealPower FLT.Mazur.CoherentIdealIntersection

/-- The actual ideal-twist successor map is injective for a nonzero line section. -/
theorem idealStep_mono (I : X.IdealSheafData) {L : X.Modules}
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) (n : ℕ) :
    Mono (step (idealModule I) s n) := by
  have := scalarAction_mono I (hL.tensorPower n)
  have := step_isIso_on_generatorOpen (idealModule I) s n
  have := stalk_isIso_of_restrict (step (idealModule I) s n) (sectionGeneratorOpen L s)
    (genericPoint X) (genericPoint_mem_sectionGeneratorOpen hL s hs)
  exact mono_of_generic_mono_of_line_embedding (hL.tensorPower n)
    (scalarAction I (tensorPower L n)) (step (idealModule I) s n)

/-- Every positive cohomology transition is surjective on a proper integral curve. -/
theorem idealStep_cohomology_surjective {k : Type} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) {L : X.Modules}
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (n q : ℕ) (hq : 0 < q) :
    Function.Surjective (moduleScalarHMap f (step (idealModule I) s n) q) := by
  have := Chow.source_isNoetherian f
  have := idealModule_coherent I
  have := (hL.tensorPower n).isFinitePresentation
  have := (hL.tensorPower (n + 1)).isFinitePresentation
  have := tensor_coherent (idealModule I) (tensorPower L n)
  have := tensor_coherent (idealModule I) (tensorPower L (n + 1))
  let a := step (idealModule I) s n
  have := idealStep_mono I hL s hs n
  have := coherent_cokernel a
  have hS := coherent_cokernelSequence a
  have hfin := step_cokernel_finiteSupport hd (idealModule I) hL s hs n
  have : Subsingleton (ModuleScalarH f (cokernel a) q) :=
    finiteSupport_cohomology_subsingleton f (cokernel a) hfin q hq
  have he := moduleScalarH_exact₂ (ShortComplex.cokernelSequence a)
    (moduleToSheaf_shortExact hS.shortExact) f q
  intro x
  apply (he x).mp
  change moduleScalarHMap f (cokernel.π a) q x = 0
  exact Subsingleton.elim _ _

end LineSectionTwistSystem
end FLT.Mazur.FCurve
