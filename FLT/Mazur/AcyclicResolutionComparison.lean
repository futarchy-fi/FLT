/-
Copyright (c) 2022 Jujian Zhang, 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project, Jujian Zhang, Kim Morrison
-/
module

public import FLT.Mazur.RightDerivedDimensionShift

/-!
# Comparisons from exact augmented resolutions

An acyclic resolution computes actual right-derived objects, naturally in
augmented resolutions and independently of the comparison. Dimension shifting
proves invertibility of the comparison constructed from exactness.
The extension and homotopy constructions generalize Mathlib's injective resolutions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex
open FLT.Mazur.RightDerivedDimensionShift

namespace FLT.Mazur.AcyclicResolutionComparison

variable {C : Type*} [Category* C] [Abelian C]

/-- A nonnegative resolution, without any injectivity condition on its terms. -/
structure ExactResolution (F : C) where
  /-- The resolving complex. -/
  cocomplex : CochainComplex C ℕ
  /-- The augmentation from the object in degree zero. -/
  ι : (CochainComplex.single₀ C).obj F ⟶ cocomplex
  /-- Exactness of the augmented complex. -/
  quasiIso : QuasiIso ι

attribute [instance] ExactResolution.quasiIso

namespace ExactResolution

variable {F : C} (I : ExactResolution F)

/-- The augmentation identifies the object with the initial kernel. -/
def isLimitKernelFork : IsLimit (KernelFork.ofι (I.ι.f 0)
    (show I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 by simp)) := by
  refine IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt I.ι 0 ≪≫ I.cocomplex.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (CochainComplex.isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp

instance mono_ι_zero : Mono (I.ι.f 0) :=
  mono_of_isLimit_fork I.isLimitKernelFork

@[reassoc (attr := simp)]
lemma ι_f_zero_comp_complex_d : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by simp

lemma exact₀ : (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).Exact :=
  ShortComplex.exact_of_f_is_kernel _ I.isLimitKernelFork

lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact := by
  have h : I.cocomplex.ExactAt (n + 1) := by
    rw [← quasiIsoAt_iff_exactAt I.ι (n + 1)
      (CochainComplex.exactAt_succ_single_obj _ _)]
    infer_instance
  exact (exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).1 h

/-- An injective resolution supplies an exact augmented resolution. -/
def ofInjective (J : InjectiveResolution F) : ExactResolution F where
  cocomplex := J.cocomplex
  ι := J.ι
  quasiIso := inferInstance

/-- A recursive component of the comparison or its homotopy. -/
def descFZero {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : ExactResolution Z) :
    J.cocomplex.X 0 ⟶ I.cocomplex.X 0 :=
  Injective.factorThru (f ≫ I.ι.f 0) (J.ι.f 0)

set_option backward.isDefEq.respectTransparency false in
/-- A recursive component of the comparison or its homotopy. -/
def descFOne {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : ExactResolution Z) :
    J.cocomplex.X 1 ⟶ I.cocomplex.X 1 :=
  J.exact₀.descToInjective (descFZero f I J ≫ I.cocomplex.d 0 1)
    (by dsimp; simp only [← assoc, descFZero]; simp [assoc])

@[simp]
theorem descFOne_zero_comm {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : ExactResolution Z) :
    J.cocomplex.d 0 1 ≫ descFOne f I J = descFZero f I J ≫ I.cocomplex.d 0 1 := by
  apply J.exact₀.comp_descToInjective

/-- A recursive component of the comparison or its homotopy. -/
def descFSucc {Y Z : C} (I : InjectiveResolution Y) (J : ExactResolution Z) (n : ℕ)
    (g : J.cocomplex.X n ⟶ I.cocomplex.X n) (g' : J.cocomplex.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : J.cocomplex.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ' g'' : J.cocomplex.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      J.cocomplex.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(J.exact_succ n).descToInjective
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (J.exact_succ n).comp_descToInjective _ _⟩

/-- A morphism in `C` descends to a cochain map to an injective resolution. -/
def desc {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y) (J : ExactResolution Z) :
    J.cocomplex ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descFZero f _ _) (descFOne f _ _) (descFOne_zero_comm f I J).symm
    fun n ⟨g, g', w⟩ => ⟨(descFSucc I J n g g' w.symm).1, (descFSucc I J n g g' w.symm).2.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The resolution maps intertwine the descent of a morphism and that morphism. -/
@[reassoc (attr := simp)]
theorem desc_commutes {Y Z : C} (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : ExactResolution Z) : J.ι ≫ desc f I J = (CochainComplex.single₀ C).map f ≫ I.ι := by
  ext
  simp [desc, descFOne, descFZero]

/-- A recursive component of the comparison or its homotopy. -/
def descHomotopyZeroZero {Y Z : C} {I : ExactResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : I.cocomplex.X 1 ⟶ J.cocomplex.X 0 :=
  I.exact₀.descToInjective (f.f 0) (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroZero {Y Z : C} {I : ExactResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) :
    I.cocomplex.d 0 1 ≫ descHomotopyZeroZero f comm = f.f 0 :=
  I.exact₀.comp_descToInjective _ _

/-- A recursive component of the comparison or its homotopy. -/
def descHomotopyZeroOne {Y Z : C} {I : ExactResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.X 2 ⟶ J.cocomplex.X 1 :=
  (I.exact_succ 0).descToInjective (f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, comp_descHomotopyZeroZero_assoc f comm,
          HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroOne {Y Z : C} {I : ExactResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = (0 : _ ⟶ J.cocomplex)) :
    I.cocomplex.d 1 2 ≫ descHomotopyZeroOne f comm =
      f.f 1 - descHomotopyZeroZero f comm ≫ J.cocomplex.d 0 1 :=
  (I.exact_succ 0).comp_descToInjective _ _

/-- A recursive component of the comparison or its homotopy. -/
def descHomotopyZeroSucc {Y Z : C} {I : ExactResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.X (n + 3) ⟶ J.cocomplex.X (n + 2) :=
  (I.exact_succ (n + 1)).descToInjective (f.f (n + 2) - g' ≫ J.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])

@[reassoc (attr := simp)]
lemma comp_descHomotopyZeroSucc {Y Z : C} {I : ExactResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (n : ℕ) (g : I.cocomplex.X (n + 1) ⟶ J.cocomplex.X n)
    (g' : I.cocomplex.X (n + 2) ⟶ J.cocomplex.X (n + 1))
    (w : f.f (n + 1) = I.cocomplex.d (n + 1) (n + 2) ≫ g' + g ≫ J.cocomplex.d n (n + 1)) :
    I.cocomplex.d (n + 2) (n + 3) ≫ descHomotopyZeroSucc f n g g' w =
      f.f (n + 2) - g' ≫ J.cocomplex.d _ _ :=
  (I.exact_succ (n + 1)).comp_descToInjective _ _

/-- Any descent of the zero morphism is homotopic to zero. -/
def descHomotopyZero {Y Z : C} {I : ExactResolution Y} {J : InjectiveResolution Z}
    (f : I.cocomplex ⟶ J.cocomplex) (comm : I.ι ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (descHomotopyZeroZero f comm) (by simp)
    (descHomotopyZeroOne f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨descHomotopyZeroSucc f n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two descents of the same morphism are homotopic. -/
def descHomotopy {Y Z : C} (f : Y ⟶ Z) {I : ExactResolution Y} {J : InjectiveResolution Z}
    (g h : I.cocomplex ⟶ J.cocomplex) (g_comm : I.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (h_comm : I.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (descHomotopyZero _ (by simp [g_comm, h_comm]))


/-- Comparisons of the identity are quasi-isomorphisms before applying a functor. -/
lemma quasiIso_desc (J : InjectiveResolution F) : QuasiIso (desc (𝟙 F) J I) := by
  rw [← quasiIso_iff_comp_left I.ι, desc_commutes]
  simpa using J.quasiIso

variable {D : Type*} [Category* D] [Abelian D] (T : C ⥤ D) [T.Additive]

/-- Homology after applying the additive functor. -/
abbrev imageHomology (n : ℕ) : CochainComplex C ℕ ⥤ D :=
  T.mapHomologicalComplex _ ⋙ homologyFunctor D _ n

/-- The induced homology map does not depend on the chosen extension. -/
lemma homologyMap_eq {Y Z : C} (f : Y ⟶ Z) (K : ExactResolution Y)
    (J : InjectiveResolution Z) (g h : K.cocomplex ⟶ J.cocomplex)
    (hg : K.ι ≫ g = (CochainComplex.single₀ C).map f ≫ J.ι)
    (hh : K.ι ≫ h = (CochainComplex.single₀ C).map f ≫ J.ι) (n : ℕ) :
    (imageHomology T n).map g = (imageHomology T n).map h :=
  (T.mapHomotopy (descHomotopy f g h hg hh)).homologyMap_eq n

variable [HasInjectiveResolutions C]

/-- A canonical map from the homology of an exact resolution to derived objects. -/
def toRightDerived (n : ℕ) :
    (imageHomology T n).obj I.cocomplex ⟶ (T.rightDerived n).obj F :=
  (imageHomology T n).map (desc (𝟙 F) (injectiveResolution F) I) ≫
    ((injectiveResolution F).isoRightDerivedObj T n).inv

/-- Naturality for every map of augmented exact resolutions. -/
@[reassoc]
lemma toRightDerived_naturality {G : C} (J : ExactResolution G) (f : F ⟶ G)
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ J.ι) (n : ℕ) :
    (imageHomology T n).map φ ≫ J.toRightDerived T n =
      I.toRightDerived T n ≫ (T.rightDerived n).map f := by
  let g := InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)
  have h := homologyMap_eq T f I (injectiveResolution G)
    (φ ≫ desc (𝟙 G) (injectiveResolution G) J)
    (desc (𝟙 F) (injectiveResolution F) I ≫ g)
    (by rw [← assoc, hφ, assoc]; simp)
    (by simp [← assoc, g]) n
  rw [toRightDerived, toRightDerived, assoc,
    (injectiveResolution F).isoRightDerivedObj_inv_naturality f
      (injectiveResolution G) g (InjectiveResolution.desc_commutes_zero _ _ _) T n]
  simpa only [Functor.map_comp, assoc] using
    congrArg (fun u => u ≫ ((injectiveResolution G).isoRightDerivedObj T n).inv) h

/-- Compute the canonical map using any target injective resolution and extension. -/
lemma toRightDerived_eq (J : InjectiveResolution F) (g : I.cocomplex ⟶ J.cocomplex)
    (hg : I.ι ≫ g = J.ι) (n : ℕ) :
    I.toRightDerived T n =
      (imageHomology T n).map g ≫ (J.isoRightDerivedObj T n).inv := by
  let f := InjectiveResolution.desc (𝟙 F) (injectiveResolution F) J
  have h := homologyMap_eq T (𝟙 F) I (injectiveResolution F)
    (desc (𝟙 F) (injectiveResolution F) I) (g ≫ f)
    (by simp) (by simp [← assoc, hg, f]) n
  rw [toRightDerived, h, Functor.map_comp, assoc]
  have hJ := J.isoRightDerivedObj_inv_naturality (𝟙 F) (injectiveResolution F)
    f (InjectiveResolution.desc_commutes_zero _ _ _) T n
  simpa using congrArg ((imageHomology T n).map g ≫ ·) hJ.symm

end ExactResolution

variable {D : Type*} [Category* D] [Abelian D]
  {F G : C} (I : ExactResolution F)

/-- Exactness of the resolution makes its maps onto positive cycles epimorphic. -/
lemma epi_toCycles (n : ℕ) : Epi (I.cocomplex.toCycles n (n + 1)) := by
  have h : (I.cocomplex.sc' n (n + 1) (n + 2)).Exact :=
    I.exact_succ n
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
def cycleSequence (n : ℕ) : ShortComplex C :=
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


/-- Every complex map induces a map of successive cycle sequences. -/
def cycleSequenceMap (J : ExactResolution G) (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) :
    cycleSequence I n ⟶ cycleSequence J n where
  τ₁ := cyclesMap φ n
  τ₂ := φ.f n
  τ₃ := cyclesMap φ (n + 1)
  comm₁₂ := cyclesMap_i φ n
  comm₂₃ := by
    dsimp [cycleSequence]
    simp only [← cancel_mono (J.cocomplex.iCycles (n + 1)), assoc, cyclesMap_i,
      toCycles_i_assoc, toCycles_i, HomologicalComplex.Hom.comm]

variable [EnoughInjectives C] (T : C ⥤ D) [T.Additive]

/-- Termwise acyclicity refers to the actual positive right-derived objects. -/
def IsAcyclic : Prop :=
  ∀ n q : ℕ, IsZero ((T.rightDerived (q + 1)).obj (I.cocomplex.X n))

omit [EnoughInjectives C] in
/-- A quasi-isomorphism induces an isomorphism on initial cycles. -/
lemma isIso_cyclesMap_zero (J : ExactResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    [QuasiIso φ] : IsIso (cyclesMap φ 0) := by
  have : IsIso (cyclesMap φ 0 ≫ J.cocomplex.homologyπ 0) := by
    rw [← homologyπ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (J.cocomplex.homologyπ 0)

/-- Dimension shifting propagates the initial comparison to positive derived cycles. -/
lemma isIso_rightDerived_cyclesMap (hI : IsAcyclic I T) (J : ExactResolution G)
    (hJ : IsAcyclic J T) (φ : I.cocomplex ⟶ J.cocomplex) [QuasiIso φ] (n q : ℕ) :
    IsIso ((T.rightDerived (q + 1)).map (cyclesMap φ n)) := by
  induction n generalizing q with
  | zero =>
    have := isIso_cyclesMap_zero I J φ
    infer_instance
  | succ n ih =>
    have := ih (q + 1)
    have := isIso_δ_succ (cycleSequence I n) (cycleSequence_shortExact I n) T (hI n) q
    have := isIso_δ_succ (cycleSequence J n) (cycleSequence_shortExact J n) T (hJ n) q
    have h := δ_naturality (cycleSequence I n) (cycleSequence_shortExact I n) T
      (cycleSequence J n) (cycleSequence_shortExact J n) (cycleSequenceMap I J φ n) (q + 1)
    change (T.rightDerived (q + 1)).map (cyclesMap φ (n + 1)) ≫ _ =
      _ ≫ (T.rightDerived (q + 2)).map (cyclesMap φ n) at h
    have : IsIso ((T.rightDerived (q + 1)).map (cyclesMap φ (n + 1)) ≫
        δ (cycleSequence J n) (cycleSequence_shortExact J n) T (q + 1)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (δ (cycleSequence J n) (cycleSequence_shortExact J n) T (q + 1))

variable [PreservesFiniteLimits T]

/-- The first connecting morphism for consecutive cycles. -/
abbrev cycleδ (n : ℕ) := δ₀ (cycleSequence I n) (cycleSequence_shortExact I n) T

lemma epi_cycleδ (hI : IsAcyclic I T) (n : ℕ) : Epi (cycleδ I T n) :=
  (exact_after_δ₀ (cycleSequence I n) (cycleSequence_shortExact I n) T).epi_f
    ((hI n 0).eq_of_tgt _ _)

/-- The short complex computing positive image homology. -/
abbrev imageShortComplex (n : ℕ) : ShortComplex D :=
  ((T.mapHomologicalComplex _).obj I.cocomplex).sc' n (n + 1) (n + 2)

omit [EnoughInjectives C] [PreservesFiniteLimits T] in
lemma imageCycles_condition (n : ℕ) :
    T.map (I.cocomplex.iCycles (n + 1)) ≫ (imageShortComplex I T n).g = 0 := by
  change T.map _ ≫ T.map _ = 0
  rw [← T.map_comp, iCycles_d, T.map_zero]

/-- Left exactness transports the kernel of the outgoing differential. -/
def imageCyclesIsKernel (n : ℕ) :
    IsLimit (KernelFork.ofι _ (imageCycles_condition I T n)) :=
  KernelFork.mapIsLimit _ (I.cocomplex.cyclesIsKernel (n + 1) (n + 2) (by simp)) T

omit [EnoughInjectives C] in
lemma imageCycles_lift (n : ℕ) :
    (imageCyclesIsKernel I T n).lift
      (KernelFork.ofι _ (imageShortComplex I T n).zero) =
        T.map (I.cocomplex.toCycles n (n + 1)) := by
  apply (cancel_mono (T.map (I.cocomplex.iCycles (n + 1)))).1
  have h := (imageCyclesIsKernel I T n).fac
    (KernelFork.ofι _ (imageShortComplex I T n).zero) WalkingParallelPair.zero
  change _ ≫ T.map (I.cocomplex.iCycles (n + 1)) = _ at h
  rw [h]
  change T.map _ = T.map _ ≫ T.map _
  rw [← T.map_comp, toCycles_i]

/-- The first derived cycle object is the homology of the image in the next degree. -/
def positiveHomologyData (hI : IsAcyclic I T) (n : ℕ) :
    (imageShortComplex I T n).LeftHomologyData where
  K := T.obj (I.cocomplex.cycles (n + 1))
  H := (T.rightDerived 1).obj (I.cocomplex.cycles n)
  i := T.map (I.cocomplex.iCycles (n + 1))
  π := cycleδ I T n
  wi := imageCycles_condition I T n
  hi := imageCyclesIsKernel I T n
  wπ := by
    rw [imageCycles_lift]
    exact map_g_δ₀ (cycleSequence I n) (cycleSequence_shortExact I n) T
  hπ := by
    have := epi_cycleδ I T hI n
    exact CokernelCofork.isColimitOfIsColimitOfIff'
      (exact_before_δ₀ (cycleSequence I n) (cycleSequence_shortExact I n) T).gIsCokernel
      _ (fun _ _ => by rw [imageCycles_lift]; rfl)

lemma positiveHomologyData_f' (hI : IsAcyclic I T) (n : ℕ) :
    (positiveHomologyData I T hI n).f' = T.map (I.cocomplex.toCycles n (n + 1)) :=
  imageCycles_lift I T n

/-- Cycle and connecting-map naturality identify the induced homology map. -/
def positiveHomologyMapData (hI : IsAcyclic I T) (J : ExactResolution G)
    (hJ : IsAcyclic J T) (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' D (ComplexShape.up ℕ) n (n + 1) (n + 2)).map
        ((T.mapHomologicalComplex _).map φ))
      (positiveHomologyData I T hI n) (positiveHomologyData J T hJ n) where
  φK := T.map (cyclesMap φ (n + 1))
  φH := (T.rightDerived 1).map (cyclesMap φ n)
  commi := by
    change T.map _ ≫ T.map _ = T.map _ ≫ T.map _
    rw [← T.map_comp, ← T.map_comp, cyclesMap_i]
  commf' := by
    rw [positiveHomologyData_f', positiveHomologyData_f']
    change T.map _ ≫ T.map _ = T.map _ ≫ T.map _
    rw [← T.map_comp, ← T.map_comp]
    exact T.congr_map (cycleSequenceMap I J φ n).comm₂₃.symm
  commπ := (δ₀_naturality _ _ T _ _ (cycleSequenceMap I J φ n)).symm

lemma quasiIsoAt_image_succ (hI : IsAcyclic I T) (J : ExactResolution G)
    (hJ : IsAcyclic J T) (φ : I.cocomplex ⟶ J.cocomplex) [QuasiIso φ] (n : ℕ) :
    QuasiIsoAt ((T.mapHomologicalComplex _).map φ) (n + 1) := by
  rw [quasiIsoAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    (positiveHomologyMapData I T hI J hJ φ n).quasiIso_iff]
  exact isIso_rightDerived_cyclesMap I T hI J hJ φ n 0

/-- Left exactness computes degree-zero homology by the image of the initial cycles. -/
def zeroHomologyData :
    (((T.mapHomologicalComplex _).obj I.cocomplex).sc' 0 0 1).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsLimitKernelFork _
    (by change T.map (I.cocomplex.d 0 0) = 0; simp)
    (KernelFork.ofι (T.map (I.cocomplex.iCycles 0)) (by
      change T.map _ ≫ T.map _ = 0
      rw [← T.map_comp, iCycles_d, T.map_zero]))
    (KernelFork.mapIsLimit _ (I.cocomplex.cyclesIsKernel 0 1 (by simp)) T)

/-- The degree-zero homology map is the functor applied to the initial cycle map. -/
def zeroHomologyMapData (J : ExactResolution G) (φ : I.cocomplex ⟶ J.cocomplex) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' D (ComplexShape.up ℕ) 0 0 1).map
        ((T.mapHomologicalComplex _).map φ))
      (zeroHomologyData I T) (zeroHomologyData J T) where
  φK := T.map (cyclesMap φ 0)
  φH := T.map (cyclesMap φ 0)
  commi := by
    change T.map _ ≫ T.map _ = T.map _ ≫ T.map _
    rw [← T.map_comp, ← T.map_comp, cyclesMap_i]
  commf' := by
    simp only [zeroHomologyData, ShortComplex.LeftHomologyData.ofIsLimitKernelFork_f',
      zero_comp, comp_zero]
  commπ := by change 𝟙 _ ≫ _ = _ ≫ 𝟙 _; simp

omit [EnoughInjectives C] in
lemma quasiIsoAt_image_zero (J : ExactResolution G) (φ : I.cocomplex ⟶ J.cocomplex)
    [QuasiIso φ] : QuasiIsoAt ((T.mapHomologicalComplex _).map φ) 0 := by
  rw [quasiIsoAt_iff' _ 0 0 1 (by simp) (by simp),
    (zeroHomologyMapData I T J φ).quasiIso_iff]
  have := isIso_cyclesMap_zero I J φ
  change IsIso (T.map (cyclesMap φ 0))
  infer_instance

/-- Applying a left exact additive functor preserves comparisons of acyclic resolutions. -/
lemma quasiIso_image (hI : IsAcyclic I T) (J : ExactResolution G)
    (hJ : IsAcyclic J T) (φ : I.cocomplex ⟶ J.cocomplex) [QuasiIso φ] :
    QuasiIso ((T.mapHomologicalComplex _).map φ) := by
  constructor
  rintro (_ | n)
  · exact quasiIsoAt_image_zero I T J φ
  · exact quasiIsoAt_image_succ I T hI J hJ φ n

/-- The canonical comparison is invertible for a resolution by acyclic objects. -/
lemma isIso_toRightDerived (hI : IsAcyclic I T) (n : ℕ) :
    IsIso (I.toRightDerived T n) := by
  let J := injectiveResolution F
  have hJ : IsAcyclic (ExactResolution.ofInjective J) T :=
    fun m q => T.isZero_rightDerived_obj_injective_succ q (J.cocomplex.X m)
  have := I.quasiIso_desc J
  have := quasiIso_image I T hI (ExactResolution.ofInjective J) hJ
    (ExactResolution.desc (𝟙 F) J I)
  dsimp [ExactResolution.toRightDerived, ExactResolution.imageHomology]
  infer_instance

/-- Actual right-derived objects computed on an exact acyclic resolution. -/
def isoRightDerivedObj (hI : IsAcyclic I T) (n : ℕ) :
    (T.rightDerived n).obj F ≅ ((T.mapHomologicalComplex _).obj I.cocomplex).homology n :=
  have := isIso_toRightDerived I T hI n
  (asIso (I.toRightDerived T n)).symm

/-- The comparison isomorphism is natural for every map of augmented resolutions. -/
@[reassoc]
lemma isoRightDerivedObj_naturality (hI : IsAcyclic I T) (J : ExactResolution G)
    (hJ : IsAcyclic J T) (f : F ⟶ G) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map f ≫ J.ι) (n : ℕ) :
    (T.rightDerived n).map f ≫ (isoRightDerivedObj J T hJ n).hom =
      (isoRightDerivedObj I T hI n).hom ≫
        homologyMap ((T.mapHomologicalComplex _).map φ) n := by
  rw [← cancel_epi (isoRightDerivedObj I T hI n).inv]
  simp only [Iso.inv_hom_id_assoc]
  change I.toRightDerived T n ≫ (T.rightDerived n).map f ≫ _ = _
  rw [← assoc, ← I.toRightDerived_naturality T J f φ hφ n, assoc]
  change _ ≫ (isoRightDerivedObj J T hJ n).inv ≫ _ = _
  simp

end FLT.Mazur.AcyclicResolutionComparison
