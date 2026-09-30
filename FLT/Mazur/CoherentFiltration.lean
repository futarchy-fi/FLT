/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentComparisonLocus

/-!
# Finite coherent filtrations

Finite chains carry actual coherent short exact sequences. Pulling back a
quotient chain along an epimorphism constructs a chain starting at its kernel;
splicing inserts any filtration of that kernel. Factors are preserved exactly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}}

/-- A finite chain from `A` to `M`, with coherent terms and factors satisfying `P`.
Every step contains its actual injection, quotient map and exactness proof. -/
inductive CoherentChain (P : X.Modules → Prop) : X.Modules → X.Modules → Type (u + 1)
  | nil {A M : X.Modules} (finite : A.IsFinitePresentation) (iso : A ≅ M) :
      CoherentChain P A M
  | snoc {A : X.Modules} (S : ShortComplex X.Modules) (seq : CoherentSequence S)
      (previous : CoherentChain P A S.X₁) (factor : P S.X₃) : CoherentChain P A S.X₂

namespace CoherentChain

variable {P Q : X.Modules → Prop} {A M : X.Modules}

/-- Number of factors in the chain. -/
def length : {M : X.Modules} → CoherentChain P A M → ℕ
  | _, .nil _ _ => 0
  | _, .snoc _ _ c _ => c.length + 1

/-- The composite inclusion of the initial term. -/
def inclusion : {M : X.Modules} → CoherentChain P A M → (A ⟶ M)
  | _, .nil _ e => e.hom
  | _, .snoc S _ c _ => c.inclusion ≫ S.f

instance inclusion_mono (c : CoherentChain P A M) : Mono c.inclusion := by
  induction c with
  | nil h e => dsimp [inclusion]; infer_instance
  | snoc S h c hp ih =>
    have := h.shortExact.mono_f
    dsimp [inclusion]
    infer_instance

/-- All chain terms, including the final term, are coherent. -/
theorem finite (c : CoherentChain P A M) : M.IsFinitePresentation := by
  cases c with
  | nil h e => exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e h
  | snoc S h c hp => exact h.finite₂

/-- Change only the identification of the initial term. -/
def rebase (c : CoherentChain P A M) {B : X.Modules} (e : B ≅ A) :
    CoherentChain P B M := by
  induction c with
  | nil h f =>
    exact .nil ((SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e.symm h) (e ≪≫ f)
  | snoc S h c hp ih => exact .snoc S h ih hp

/-- Change only the identification of the final term. -/
def transport (c : CoherentChain P A M) {N : X.Modules} (e : M ≅ N) :
    CoherentChain P A N := by
  cases c with
  | nil h f => exact .nil h (f ≪≫ e)
  | snoc S h c hp =>
    let T := ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) (by simp)
    let t : S ≅ T := ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp [T]) (by simp [T])
    exact .snoc T ⟨ShortComplex.shortExact_of_iso t h.shortExact, h.finite₁,
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e h.finite₂, h.finite₃⟩ c hp

/-- Weaken the predicate without altering any term or factor. -/
def map (c : CoherentChain P A M) (h : ∀ N, P N → Q N) : CoherentChain Q A M := by
  induction c with
  | nil h e => exact .nil h e
  | snoc S hs c hp ih => exact .snoc S hs ih (h _ hp)

/-- Terms in their chain order, including both endpoints. -/
def terms : {M : X.Modules} → CoherentChain P A M → List X.Modules
  | M, .nil _ _ => [A, M]
  | _, .snoc S _ c _ => c.terms ++ [S.X₂]

/-- Every listed term is an actual subobject of the ambient sheaf. -/
theorem term_embedding (c : CoherentChain P A M) {N : X.Modules} (hN : N ∈ c.terms) :
    ∃ f : N ⟶ M, Mono f := by
  induction c with
  | nil h e =>
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with rfl | rfl
    · exact ⟨e.hom, inferInstance⟩
    · exact ⟨𝟙 _, inferInstance⟩
  | snoc S h c hp ih =>
    simp only [terms, List.mem_append, List.mem_singleton] at hN
    rcases hN with hN | rfl
    · obtain ⟨f, hf⟩ := ih hN
      have := h.shortExact.mono_f
      exact ⟨f ≫ S.f, inferInstance⟩
    · exact ⟨𝟙 _, inferInstance⟩

/-- Every stage, not only the endpoints, is coherent. -/
theorem term_finite (c : CoherentChain P A M) {N : X.Modules} (hN : N ∈ c.terms) :
    N.IsFinitePresentation := by
  induction c with
  | nil h e =>
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with rfl | rfl
    · exact h
    · exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e h
  | snoc S h c hp ih =>
    simp only [terms, List.mem_append, List.mem_singleton] at hN
    rcases hN with hN | rfl
    · exact ih hN
    · exact h.finite₂

/-- All stages inherit every support bound on the ambient sheaf. -/
theorem term_support (c : CoherentChain P A M) {N : X.Modules} (hN : N ∈ c.terms) :
    support N ⊆ support M := by
  obtain ⟨f, hf⟩ := c.term_embedding hN
  exact support_subset_of_mono f

/-- Record a support bound on every factor, using its actual quotient map. -/
def boundFactors (c : CoherentChain P A M) (Z : Set X) (hM : support M ⊆ Z) :
    CoherentChain (fun N ↦ P N ∧ support N ⊆ Z) A M := by
  induction c with
  | nil h e => exact .nil h e
  | snoc S h c hp ih =>
    have := h.shortExact.mono_f
    have := h.shortExact.epi_g
    exact .snoc S h (ih ((support_subset_of_mono S.f).trans hM))
      ⟨hp, (support_subset_of_epi S.g).trans hM⟩

end CoherentChain

/-- A filtration is a finite coherent chain with an actual zero initial term. -/
structure CoherentFiltration (P : X.Modules → Prop) (M : X.Modules) where
  /-- The chosen initial zero sheaf. -/
  initial : X.Modules
  initial_zero : IsZero initial
  /-- The finite chain ending at the given ambient sheaf. -/
  chain : CoherentChain P initial M

section Pullback

variable [IsLocallyNoetherian X]

variable {S : ShortComplex X.Modules} (hS : CoherentSequence S)
  {M : X.Modules} [M.IsFinitePresentation] (p : M ⟶ S.X₂) [Epi p]

/-- The inverse image of a coherent subobject is the kernel of the composite quotient. -/
def inverseImageKernel :
    IsLimit (KernelFork.ofι (pullback.fst p S.f)
      (show pullback.fst p S.f ≫ (p ≫ S.g) = 0 by
        rw [← Category.assoc, pullback.condition, Category.assoc, S.zero, comp_zero])) := by
  have := hS.shortExact.mono_f
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  let l := hS.shortExact.fIsKernel.lift (KernelFork.ofι (k ≫ p) (by
    simpa only [Category.assoc] using hk))
  have hl : l ≫ S.f = k ≫ p := hS.shortExact.fIsKernel.fac _ WalkingParallelPair.zero
  exact ⟨pullback.lift k l hl.symm, by simp⟩

include hS in
omit [Epi p] in
/-- Pullbacks of coherent inclusions along coherent epimorphisms are coherent. -/
theorem coherent_inverseImage : (pullback p S.f).IsFinitePresentation := by
  have := hS.finite₃
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    ((kernelIsKernel (p ≫ S.g)).conePointUniqueUpToIso (inverseImageKernel hS p))
    (coherent_kernel (p ≫ S.g))

/-- The inverse-image inclusion has the very same quotient as the original inclusion. -/
def inverseImageSequence : ShortComplex X.Modules :=
  ShortComplex.mk (pullback.fst p S.f) (p ≫ S.g) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, S.zero, comp_zero])

include hS in
/-- Exactness and coherence of the inverse-image sequence. -/
theorem coherent_inverseImageSequence : CoherentSequence (inverseImageSequence p) := by
  have := hS.shortExact.mono_f
  have := hS.shortExact.epi_g
  refine {
    shortExact := ?_
    finite₁ := coherent_inverseImage hS p
    finite₂ := inferInstanceAs M.IsFinitePresentation
    finite₃ := hS.finite₃ }
  exact {
    exact := ShortComplex.exact_of_f_is_kernel _ (inverseImageKernel hS p)
    mono_f := inferInstanceAs (Mono (pullback.fst p S.f))
    epi_g := inferInstanceAs (Epi (p ≫ S.g)) }

/-- The successive quotient is canonically the cokernel of the pulled-back inclusion. -/
def inverseImageCokernelIso : cokernel (pullback.fst p S.f) ≅ S.X₃ :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso
    (coherent_inverseImageSequence hS p).shortExact.gIsCokernel

end Pullback

section BaseChange

variable (S : ShortComplex X.Modules) {N : X.Modules} (t : N ⟶ S.X₃)

/-- The actual base change of a short complex along a map into its quotient. -/
def baseChangeSequence : ShortComplex X.Modules :=
  ShortComplex.mk (pullback.lift S.f 0 (by simp)) (pullback.snd S.g t) (by simp)

/-- Base change preserves short exactness; the left term is unchanged. -/
theorem baseChange_shortExact (hS : S.ShortExact) : (baseChangeSequence S t).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hm : Mono (pullback.lift S.f (0 : S.X₁ ⟶ N)
      (show S.f ≫ S.g = (0 : S.X₁ ⟶ N) ≫ t by simp)) :=
    mono_of_mono_fac (pullback.lift_fst S.f 0
      (show S.f ≫ S.g = (0 : S.X₁ ⟶ N) ≫ t by simp))
  refine { exact := ?_, mono_f := hm, epi_g := inferInstanceAs (Epi (pullback.snd S.g t)) }
  dsimp [baseChangeSequence]
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  let l := hS.fIsKernel.lift (KernelFork.ofι (k ≫ pullback.fst S.g t) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]))
  have hl : l ≫ S.f = k ≫ pullback.fst S.g t :=
    hS.fIsKernel.fac _ WalkingParallelPair.zero
  refine ⟨l, ?_⟩
  apply pullback.hom_ext
  · simpa using hl
  · simpa using hk.symm

end BaseChange

namespace CoherentChain

variable [IsLocallyNoetherian X] {P : X.Modules → Prop} {B₀ B Z : X.Modules}

/-- Splice a filtration of the kernel with the inverse images of a quotient
filtration. Each recursive step constructs a pullback and its two sequences. -/
def splice (d : CoherentChain P B₀ B) (hz : IsZero B₀)
    {A M : X.Modules} (f : A ⟶ M) (g : M ⟶ B) (w : f ≫ g = 0)
    (h : CoherentSequence (ShortComplex.mk f g w)) (c : CoherentChain P Z A) :
    CoherentChain P Z M := by
  induction d generalizing A M with
  | nil hB e =>
    have hf : IsIso f := h.shortExact.isIso_f_iff.mpr (hz.of_iso e.symm)
    exact c.transport (asIso f)
  | snoc T hT d hp ih =>
    have := h.finite₂
    have := h.shortExact.epi_g
    let S := ShortComplex.mk f g w
    let U := baseChangeSequence S T.f
    have hU : CoherentSequence U :=
      ⟨baseChange_shortExact S T.f h.shortExact, h.finite₁,
        coherent_inverseImage hT g, hT.finite₁⟩
    exact .snoc (inverseImageSequence g) (coherent_inverseImageSequence hT g)
      (ih U.f U.g U.zero hU c) hp

/-- Pulling a zero-initial chain back along an epimorphism gives a chain
starting at the actual kernel, with exactly the same factor predicate. -/
def pullback (d : CoherentChain P B₀ B) (hz : IsZero B₀)
    {M : X.Modules} [M.IsFinitePresentation] (p : M ⟶ B) [Epi p] :
    CoherentChain P (kernel p) M := by
  have := d.finite
  exact d.splice hz (kernel.ι p) p (kernel.condition p)
    (coherent_kernelSequence p) (.nil (coherent_kernel p) (Iso.refl _))

end CoherentChain

/-- Two-out-of-three transfers across coherent isomorphisms once zero has the property. -/
theorem TwoOutOfThree.iso_of_zero {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    {Z M N : X.Modules} (hZ : Z.IsFinitePresentation) (hz : IsZero Z) (pZ : P Z)
    (hM : M.IsFinitePresentation) (e : M ≅ N) (pM : P M) : P N := by
  let S := ShortComplex.mk (0 : Z ⟶ N) e.inv (by simp)
  have hS : CoherentSequence S :=
    { shortExact :=
        { exact := (S.exact_iff_mono rfl).mpr (inferInstanceAs (Mono e.inv))
          mono_f := ⟨fun _ _ _ ↦ hz.eq_of_tgt _ _⟩
          epi_g := inferInstanceAs (Epi e.inv) }
      finite₁ := hZ
      finite₂ := (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e hM
      finite₃ := hM }
  exact hP.middle hS pZ pM

namespace CoherentChain

variable {P : X.Modules → Prop} {A M : X.Modules}

/-- A zero-initial chain propagates a two-out-of-three property through its actual sequences. -/
theorem property (c : CoherentChain P A M) (hP : TwoOutOfThree P)
    (hA : A.IsFinitePresentation) (hz : IsZero A) (pA : P A) : P M := by
  induction c with
  | nil h e => exact hP.iso_of_zero hA hz pA h e pA
  | snoc S h c hp ih => exact hP.middle h ih hp

end CoherentChain

namespace CoherentFiltration

variable [IsLocallyNoetherian X] {P : X.Modules → Prop}

/-- Splicing filtrations of the outer terms constructs a filtration of the middle. -/
def splice {S : ShortComplex X.Modules} (h : CoherentSequence S)
    (c : CoherentFiltration P S.X₁) (d : CoherentFiltration P S.X₃) :
    CoherentFiltration P S.X₂ :=
  ⟨c.initial, c.initial_zero, d.chain.splice d.initial_zero S.f S.g S.zero h c.chain⟩

end CoherentFiltration

end FLT.Mazur.FCurve.CoherentDevissage
