/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AbelianInjectiveFlasque
public import FLT.Mazur.AcyclicDirectImageResolution
public import FLT.Mazur.ModuleInjectiveFlasque

/-!
# Flasque sheaves are acyclic for direct image

The cycles of an injective resolution of a flasque sheaf are flasque, by the
short exact sequences linking consecutive cycles. Their section surjectivity
makes the direct-image complex exact in positive degrees. Computing the actual
right-derived objects on this resolution gives their vanishing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace FLT.Mazur.FlasqueDirectImageAcyclic

variable {X Y : TopCat.{u}}

/-- Flasqueness is invariant under isomorphism of abelian sheaves. -/
lemma isFlasque_of_iso {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (e : F ≅ G) [TopCat.Sheaf.IsFlasque F] : TopCat.Sheaf.IsFlasque G where
  epi {U V} i := by
    have : Epi (e.hom.hom.app U ≫ G.obj.map i) := by
      rw [← e.hom.hom.naturality i]
      infer_instance
    exact epi_of_epi (e.hom.hom.app U) (G.obj.map i)

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)

/-- Exactness of the resolution makes its maps onto positive cycles epimorphic. -/
lemma epi_toCycles (n : ℕ) : Epi (I.cocomplex.toCycles n (n + 1)) := by
  have h : (I.cocomplex.sc' n (n + 1) (n + 2)).Exact :=
    (exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).1
      (I.cocomplex_exactAt_succ n)
  have := h.epi_toCycles
  let e := I.cocomplex.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)
  have he : I.cocomplex.toCycles n (n + 1) =
      (I.cocomplex.sc' n (n + 1) (n + 2)).toCycles ≫ e.inv := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact I.cocomplex.toCycles_cyclesIsoSc'_hom n (n + 1) (n + 2) (by simp) (by simp)
  rw [he]
  infer_instance

/-- The short complex linking consecutive cycles of the resolution. -/
def cycleSequence (n : ℕ) : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (I.cocomplex.iCycles n) (I.cocomplex.toCycles n (n + 1)) (by
    rw [← cancel_mono (I.cocomplex.iCycles (n + 1)), Category.assoc,
      toCycles_i, iCycles_d, zero_comp])

/-- Consecutive cycles and the intervening injective form a short exact sequence. -/
lemma cycleSequence_shortExact (n : ℕ) : (cycleSequence I n).ShortExact := by
  have := epi_toCycles I n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  rotate_left
  · change Mono (I.cocomplex.iCycles n)
    infer_instance
  · exact epi_toCycles I n
  let S := ShortComplex.mk (I.cocomplex.iCycles n) (I.cocomplex.d n (n + 1))
    (I.cocomplex.iCycles_d n (n + 1))
  let φ : cycleSequence I n ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := I.cocomplex.iCycles (n + 1)
      comm₂₃ := by simp [cycleSequence, S] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (ShortComplex.exact_of_f_is_kernel S (I.cocomplex.cyclesIsKernel n (n + 1) (by simp)))

/-- Every cycle sheaf in a resolution of a flasque sheaf is flasque. -/
lemma isFlasque_cycles [TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    TopCat.Sheaf.IsFlasque (I.cocomplex.cycles n) := by
  induction n with
  | zero =>
    exact isFlasque_of_iso (F := F) (IsLimit.conePointUniqueUpToIso I.isLimitKernelFork
      (I.cocomplex.cyclesIsKernel 0 1 (by simp)))
  | succ n ih =>
    have : TopCat.Sheaf.IsFlasque (cycleSequence I n).X₁ := ih
    have : TopCat.Sheaf.IsFlasque (cycleSequence I n).X₂ :=
      AbelianInjectiveFlasque.isFlasque (I.cocomplex.X n)
    exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
      (cycleSequence_shortExact I n)

variable (f : X ⟶ Y)

/-- Direct image preserves epimorphisms in short exact sequences with flasque kernel. -/
lemma epi_pushforward_of_shortExact
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map S.g) := by
  apply (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).epi_of_epi_map
  have : ∀ U : (Opens Y)ᵒᵖ,
      Epi (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map S.g).hom.app U) :=
    fun _ => TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
  change Epi (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map S.g).hom)
  exact NatTrans.epi_of_epi_app _

/-- The direct-image resolution maps onto each positive cycle sheaf. -/
lemma epi_pushforward_toCycles [TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
      (I.cocomplex.toCycles n (n + 1))) := by
  have : TopCat.Sheaf.IsFlasque (cycleSequence I n).X₁ := isFlasque_cycles I n
  exact epi_pushforward_of_shortExact f (cycleSequence_shortExact I n)

/-- Pushing an injective resolution of a flasque sheaf is exact in positive degrees. -/
lemma image_exact_succ [TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    (AcyclicDirectImageResolution.imageComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) I).ExactAt (n + 1) := by
  let T := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  let S := ShortComplex.mk (I.cocomplex.iCycles (n + 1))
    (I.cocomplex.d (n + 1) (n + 2)) (I.cocomplex.iCycles_d (n + 1) (n + 2))
  have hS : (S.map T).Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    exact KernelFork.mapIsLimit _
      (I.cocomplex.cyclesIsKernel (n + 1) (n + 2) (by simp)) T
  have := epi_pushforward_toCycles I f n
  let φ : (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).map T ⟶
      S.map T :=
    { τ₁ := T.map (I.cocomplex.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, ← T.map_comp] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS

/-- A flasque abelian sheaf has zero positive derived direct images. -/
theorem isZero_rightDerived_obj (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [TopCat.Sheaf.IsFlasque F] (n : ℕ) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived (n + 1)).obj F) := by
  let I := injectiveResolution F
  have h := (exactAt_iff_isZero_homology _ _).1 (image_exact_succ I f n)
  exact h.of_iso (I.isoRightDerivedObj (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (n + 1))

/-- Underlying abelian sheaves of injective modules are acyclic for every direct image. -/
theorem isZero_rightDerived_toSheaf
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (M : SheafOfModules.{u} R) [Injective M] (n : ℕ) :
    IsZero (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived (n + 1)).obj
      ((SheafOfModules.toSheaf R).obj M)) :=
  isZero_rightDerived_obj f ((SheafOfModules.toSheaf R).obj M) n

end FLT.Mazur.FlasqueDirectImageAcyclic
