/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.CoherentIdealPowerFiltration
public import FLT.Mazur.GenericIdealSupport
public import FLT.Mazur.IntegralClosedSupport

/-!
# Geometric filtrations of coherent sheaves

Stacks 01YF and 01YG: closed-support induction constructs a finite filtration
whose factors are nonzero ideals on integral closed subschemes. Every closed
image lies inside the support of the original sheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ZeroObject
open Scheme.Modules FLT.Mazur.CommonIdealDirectSum FLT.Mazur.CoherentIdealIntersection

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}}

/-- A nonzero ideal on an integral reduced closed subscheme within a given bound. -/
def IntegralIdealFactor (Z : Set X) (M : X.Modules) : Prop :=
  ∃ (W : Closeds X), IsIrreducible (W : Set X) ∧ (W : Set X) ⊆ Z ∧
    ∃ I : (reducedClosedSubscheme W).IdealSheafData, I ≠ ⊥ ∧
      Nonempty (M ≅ (pushforward (reducedClosedSubschemeι W)).obj (idealModule I))

/-- Enlarging the bound keeps every constructed integral ideal factor. -/
theorem IntegralIdealFactor.mono {Z W : Set X} {M : X.Modules}
    (h : IntegralIdealFactor Z M) (hZW : Z ⊆ W) : IntegralIdealFactor W M := by
  obtain ⟨V, hV, hVZ, I, hI, e⟩ := h
  exact ⟨V, hV, hVZ.trans hZW, I, hI, e⟩

namespace CoherentFiltration

variable [IsLocallyNoetherian X] {P Q : X.Modules → Prop} {M : X.Modules}

/-- Refine each factor by a constructed filtration, using pullback splicing. -/
def refine (c : CoherentFiltration P M)
    (h : ∀ N : X.Modules, N.IsFinitePresentation → P N → Nonempty (CoherentFiltration Q N)) :
    CoherentFiltration Q M := by
  obtain ⟨A, hz, c⟩ := c
  induction c with
  | nil hA e => exact ⟨A, hz, .nil hA e⟩
  | snoc S hS c hp ih => exact ih.splice hS (Classical.choice (h _ hS.finite₃ hp))

/-- Enlarge the closed bound on a geometric filtration. -/
def enlarge {Z W : Set X} (c : CoherentFiltration (IntegralIdealFactor Z) M)
    (hZW : Z ⊆ W) : CoherentFiltration (IntegralIdealFactor W) M :=
  ⟨c.initial, c.initial_zero, c.chain.map (fun _ h ↦ h.mono hZW)⟩

end CoherentFiltration

section IdealSums

variable (I : X.IdealSheafData) (n : ℕ)

/-- The explicit split sequence adding one ideal summand. -/
def idealSumSequence : ShortComplex X.Modules :=
  ShortComplex.mk
    (Sigma.desc (fun j : ULift.{u} (Fin n) ↦
      Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ idealModule I) ⟨j.down.succ⟩))
    (Sigma.desc (fun j : ULift.{u} (Fin (n + 1)) ↦
      Fin.cases (𝟙 (idealModule I)) (fun _ ↦ 0) j.down)) (by
        apply Sigma.hom_ext
        intro j
        simp)

/-- Coordinate projection and inclusion split the actual ideal-sum sequence. -/
def idealSumSplitting : (idealSumSequence I n).Splitting where
  r := Sigma.desc (fun j : ULift.{u} (Fin (n + 1)) ↦
    Fin.cases (0 : idealModule I ⟶ idealSum I n)
      (fun k ↦ Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ idealModule I) ⟨k⟩) j.down)
  s := Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ idealModule I) ⟨0⟩
  f_r := by
    apply Sigma.hom_ext
    intro j
    simp [idealSumSequence]
  s_g := by simp [idealSumSequence]
  id := by
    apply Sigma.hom_ext
    intro j
    rcases j with ⟨j⟩
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [idealSumSequence, Preadditive.comp_add]

/-- An empty sum is an actual zero sheaf. -/
theorem idealSum_zero : IsZero (idealSum I 0) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro j
  exact Fin.elim0 j.down

end IdealSums

variable [IsNoetherian X]

/-- The finite sum source in the generic embedding has a single-ideal filtration. -/
def closedIdealSumFiltration (Z : Closeds X) (hZ : IsIrreducible (Z : Set X))
    (I : (reducedClosedSubscheme Z).IdealSheafData) (hI : I ≠ ⊥) (n : ℕ) :
    CoherentFiltration (IntegralIdealFactor (Z : Set X))
      ((pushforward (reducedClosedSubschemeι Z)).obj (idealSum I n)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian (reducedClosedSubschemeι Z)
  let F := pushforward (reducedClosedSubschemeι Z)
  induction n with
  | zero =>
    have hz : IsZero (F.obj (idealSum I 0)) := F.map_isZero (idealSum_zero I)
    exact ⟨_, hz, .nil (GenericIdealInjection.closedIdealSum_coherent
      (Scheme.IdealSheafData.vanishingIdeal Z) I 0) (Iso.refl _)⟩
  | succ n ih =>
    let S := (idealSumSequence I n).map F
    have hS : CoherentSequence S :=
      ⟨(idealSumSplitting I n).shortExact.map_of_exact F,
        GenericIdealInjection.closedIdealSum_coherent (Scheme.IdealSheafData.vanishingIdeal Z) I n,
        GenericIdealInjection.closedIdealSum_coherent
          (Scheme.IdealSheafData.vanishingIdeal Z) I (n + 1),
        GenericIdealSupport.closedIdeal_coherent (Scheme.IdealSheafData.vanishingIdeal Z) I⟩
    exact ⟨ih.initial, ih.initial_zero, .snoc S hS ih.chain
      ⟨Z, hZ, Set.Subset.refl _, I, hI, ⟨Iso.refl _⟩⟩⟩

/-- Geometric filtration within any closed support bound (Stacks 01YF). -/
theorem exists_geometricFiltration (Z : Closeds X) (M : X.Modules)
    [M.IsFinitePresentation] (hs : support M ⊆ Z) :
    Nonempty (CoherentFiltration (IntegralIdealFactor (Z : Set X)) M) := by
  let Q (Z : Closeds X) := ∀ (M : X.Modules), M.IsFinitePresentation → support M ⊆ Z →
    Nonempty (CoherentFiltration (IntegralIdealFactor (Z : Set X)) M)
  suffices h : Q Z from h M inferInstance hs
  apply closed_induction_on_irreducible Q _ _ _ Z
  · intro M hM hs
    have hz : IsZero M := (support_eq_empty_iff_isZero M).mp (Set.eq_empty_of_subset_empty hs)
    exact ⟨⟨M, hz, .nil hM (Iso.refl _)⟩⟩
  · intro Z W hZ hW M hM hs
    obtain ⟨A, B, f, g, w, h, hA, hB⟩ := exists_supported_decomposition M Z W hs
    let c := Classical.choice (hZ A h.finite₁ hA)
    let d := Classical.choice (hW B h.finite₃ hB)
    exact ⟨(c.enlarge Set.subset_union_left).splice h (d.enlarge Set.subset_union_right)⟩
  · intro Z hZ ih M hM hs
    let I := Scheme.IdealSheafData.vanishingIdeal Z
    have : IsIntegral I.subscheme := reducedClosedSubscheme_isIntegral Z hZ
    have hI : support M ⊆ I.support := hs
    let c := supportedIdealPowerFiltration I M hI
    refine ⟨c.refine (fun N hN hkill ↦ ?_)⟩
    have hsN : support N ⊆ Set.range I.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hkill.2.trans hs
    obtain ⟨J, hJ, f, hseq, _, _, hsmall⟩ :=
      GenericIdealSupport.exists_supported_embedding I N hkill.1.generic_stalk hsN
    have : (cokernel f).IsFinitePresentation := hseq.finite₃
    have hlt : closedSupport (cokernel f) < Z := by
      change support (cokernel f) ⊂ (Z : Set X)
      simpa [I, Scheme.IdealSheafData.range_subschemeι] using hsmall
    let d := Classical.choice (ih _ hlt (cokernel f) inferInstance (Set.Subset.refl _))
    let a := closedIdealSumFiltration Z hZ J hJ
      (Module.finrank I.subscheme.functionField
        ((CoherentClosedReduction.descent I N).presheaf.stalk (genericPoint I.subscheme)))
    exact ⟨a.splice hseq (d.enlarge hlt.le)⟩

/-- In particular every integral closed image lies in the original support. -/
def geometricFiltration (M : X.Modules) [M.IsFinitePresentation] :
    CoherentFiltration (IntegralIdealFactor (support M)) M :=
  Classical.choice (exists_geometricFiltration (closedSupport M) M (Set.Subset.refl _))

/-- The zero sheaf is coherent on a locally Noetherian scheme. -/
theorem coherent_zero : (0 : X.Modules).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (isZero_kernel_of_mono (𝟙 (SheafOfModules.unit X.ringCatSheaf))).isoZero
    (coherent_kernel (𝟙 (SheafOfModules.unit X.ringCatSheaf)))

/-- Extension closure and the zero base case imply invariance under coherent isomorphisms. -/
theorem extension_iso_of_zero {P : X.Modules → Prop}
    (hext : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → P S.X₁ → P S.X₃ → P S.X₂)
    (hzero : P 0) {M N : X.Modules} (hM : M.IsFinitePresentation) (e : M ≅ N)
    (pM : P M) : P N := by
  let S := ShortComplex.mk (0 : (0 : X.Modules) ⟶ N) e.inv (by simp)
  have hS : CoherentSequence S :=
    ⟨(ShortComplex.Splitting.ofIsZeroOfIsIso
      (S := S) (isZero_zero _) (inferInstanceAs (IsIso e.inv))).shortExact,
      coherent_zero,
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e hM, hM⟩
  exact hext hS hzero pM

/-- Finite-extension criterion (Stacks 01YG), requiring only extension closure and zero. -/
theorem geometric_finite_extension_of_extensions {P : X.Modules → Prop}
    (hext : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → P S.X₁ → P S.X₃ → P S.X₂)
    (hzero : P 0) (Z : Set X)
    (hfactor : ∀ N : X.Modules, N.IsFinitePresentation → IntegralIdealFactor Z N → P N)
    (M : X.Modules) [M.IsFinitePresentation] (hs : support M ⊆ Z) : P M := by
  let c := (geometricFiltration M).enlarge hs
  have pA : P c.initial := extension_iso_of_zero hext hzero coherent_zero
    c.initial_zero.isoZero.symm hzero
  have h : ∀ {A N : X.Modules}, (d : CoherentChain (IntegralIdealFactor Z) A N) →
      P A → P N := by
    intro A N d hp
    induction d with
    | nil h e => exact extension_iso_of_zero hext hzero h e hp
    | snoc S h d hf ih => exact hext h ih (hfactor _ h.finite₃ hf)
  exact h c.chain pA

/-- The finite-extension criterion specialized to a two-out-of-three class. -/
theorem geometric_finite_extension {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    (hzero : P 0) (Z : Set X)
    (hfactor : ∀ N : X.Modules, N.IsFinitePresentation → IntegralIdealFactor Z N → P N)
    (M : X.Modules) [M.IsFinitePresentation] (hs : support M ⊆ Z) : P M :=
  geometric_finite_extension_of_extensions hP.middle hzero Z hfactor M hs

/-- Stacks 01YG phrased solely in terms of properties of actual pushed-forward ideals. -/
theorem geometric_ideal_criterion {P : X.Modules → Prop}
    (hext : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → P S.X₁ → P S.X₃ → P S.X₂)
    (hzero : P 0) (Z : Set X)
    (hideal : ∀ W : Closeds X, IsIrreducible (W : Set X) → (W : Set X) ⊆ Z →
      ∀ I : (reducedClosedSubscheme W).IdealSheafData, I ≠ ⊥ →
        P ((pushforward (reducedClosedSubschemeι W)).obj (idealModule I)))
    (M : X.Modules) [M.IsFinitePresentation] (hs : support M ⊆ Z) : P M := by
  apply geometric_finite_extension_of_extensions hext hzero Z _ M hs
  intro N _ hf
  obtain ⟨W, hW, hWZ, I, hI, ⟨e⟩⟩ := hf
  exact extension_iso_of_zero hext hzero
    (GenericIdealSupport.closedIdeal_coherent (Scheme.IdealSheafData.vanishingIdeal W) I)
    e.symm (hideal W hW hWZ I hI)

end FLT.Mazur.FCurve.CoherentDevissage
