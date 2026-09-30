/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentGeometricFiltration

/-!
# Transfer from a generic rank-one witness

Stacks 01YH: retain the given witness, derive the zero base case from it, and
use actual ideal intersections to transfer its property to all ideal factors.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ZeroObject
open Scheme.Modules FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.CoherentGenericIdealEmbedding

universe u

namespace FLT.Mazur.FCurve.CoherentDevissage

variable {X : Scheme.{u}}

/-- The original generic-rank-one witness on an integral closed subscheme. -/
structure GenericRankOneWitness (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (P : X.Modules → Prop) where
  /-- The given coherent sheaf. -/
  sheaf : X.Modules
  finite : sheaf.IsFinitePresentation
  support_eq : support sheaf = Set.range J.subschemeι
  annihilated : StalkAnnihilated sheaf (J.subschemeι (genericPoint J.subscheme))
  rank_one : letI := residueModule sheaf _ annihilated
    Module.finrank (X.residueField (J.subschemeι (genericPoint J.subscheme)))
      (sheaf.presheaf.stalk (J.subschemeι (genericPoint J.subscheme))) = 1
  property : P sheaf

/-- The same witness on the canonically reduced structure of an irreducible closed subset. -/
abbrev ClosedRankOneWitness (P : X.Modules → Prop) (Z : Closeds X)
    (hZ : IsIrreducible (Z : Set X)) :=
  @GenericRankOneWitness X (Scheme.IdealSheafData.vanishingIdeal Z)
    (reducedClosedSubscheme_isIntegral Z hZ) P

variable [IsNoetherian X]

/-- A single coherent member of a two-out-of-three class forces the zero base case. -/
theorem TwoOutOfThree.zero_of_member {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    (G : X.Modules) [G.IsFinitePresentation] (hG : P G) : P 0 := by
  let S := ShortComplex.mk (𝟙 G) (0 : G ⟶ (0 : X.Modules)) (by simp)
  have hS : CoherentSequence S :=
    ⟨(ShortComplex.Splitting.ofIsIsoOfIsZero
      (S := S) (inferInstanceAs (IsIso (𝟙 G))) (isZero_zero _)).shortExact,
      inferInstance, inferInstance, coherent_zero⟩
  exact hP.right hS hG hG

/-- The geometric filtration transfers the smaller-ideal hypothesis to smaller supports. -/
theorem property_of_strict_support {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    (hzero : P 0) (Z : Closeds X)
    (hsmall : ∀ W : Closeds X, W < Z → IsIrreducible (W : Set X) →
      ∀ I : (reducedClosedSubscheme W).IdealSheafData,
        P ((pushforward (reducedClosedSubschemeι W)).obj (idealModule I)))
    (N : X.Modules) [N.IsFinitePresentation] (hN : support N ⊂ (Z : Set X)) : P N := by
  apply geometric_ideal_criterion hP.middle hzero (support N) _ N (Set.Subset.refl _)
  intro W hW hWN I _
  exact hsmall W (lt_of_le_of_lt (show W ≤ closedSupport N from hWN) hN) hW I

/-- The support part of the constructed rank-one embedding, without comparison-open data. -/
theorem rank_one_error_sequence (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (G : X.Modules) [G.IsFinitePresentation]
    (hAnn : StalkAnnihilated G (J.subschemeι (genericPoint J.subscheme)))
    (hd : letI := residueModule G _ hAnn
      Module.finrank (X.residueField (J.subschemeι (genericPoint J.subscheme)))
        (G.presheaf.stalk (J.subschemeι (genericPoint J.subscheme))) = 1)
    (hs : support G ⊆ Set.range J.subschemeι) :
    ∃ (I : J.subscheme.IdealSheafData), I ≠ ⊥ ∧ ∃ f :
      (pushforward J.subschemeι).obj (idealModule I) ⟶ G,
      CoherentSequence (ShortComplex.cokernelSequence f) ∧
      support (cokernel f) ⊂ Set.range J.subschemeι := by
  obtain ⟨I, hI, f, hseq, _, _, hq, _⟩ :=
    GenericIdealSupport.exists_supported_rank_one_embedding J G hAnn hd hs
  exact ⟨I, hI, f, hseq, hq⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Common-source cokernel sequences transfer a property when both errors have it. -/
theorem TwoOutOfThree.common_cokernels {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    {A B C : X.Modules} (f : A ⟶ B) (g : A ⟶ C)
    (hf : CoherentSequence (ShortComplex.cokernelSequence f))
    (hg : CoherentSequence (ShortComplex.cokernelSequence g))
    (hqf : P (cokernel f)) (hqg : P (cokernel g)) : P B ↔ P C :=
  hP.common_subobject (S := ShortComplex.cokernelSequence f)
    (T := ShortComplex.cokernelSequence g) hf hg rfl hqf hqg

/-- Actual ideal intersections transfer a property through the common subobject. -/
theorem ideal_intersection_transfer {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (hsmall : ∀ N : X.Modules, N.IsFinitePresentation →
      support N ⊂ Set.range J.subschemeι → P N)
    (I I' : J.subscheme.IdealSheafData) (hI : I ≠ ⊥) (hI' : I' ≠ ⊥)
    (hp : P ((pushforward J.subschemeι).obj (idealModule I))) :
    P ((pushforward J.subschemeι).obj (idealModule I')) := by
  have h := intersection_sequences J.subschemeι I I' hI hI'
  exact (hP.common_cokernels
    (pushedIdealMap J.subschemeι (inf_le_left : I ⊓ I' ≤ I))
    (pushedIdealMap J.subschemeι (inf_le_right : I ⊓ I' ≤ I')) h.2.1 h.2.2.1
    (hsmall _ h.2.1.finite₃ h.2.2.2.1)
    (hsmall _ h.2.2.1.finite₃ h.2.2.2.2)).mp hp

/-- A fixed witness gives the property for every nonzero ideal on the same closed subscheme. -/
theorem ideals_of_generic_rank_one {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    (J : X.IdealSheafData) [IsIntegral J.subscheme] (w : GenericRankOneWitness J P)
    (hsmall : ∀ N : X.Modules, N.IsFinitePresentation →
      support N ⊂ Set.range J.subschemeι → P N)
    (I' : J.subscheme.IdealSheafData) (hI' : I' ≠ ⊥) :
    P ((pushforward J.subschemeι).obj (idealModule I')) := by
  obtain ⟨G, hG, hs, hAnn, hd, pG⟩ := w
  obtain ⟨I, hI, f, hseq, hq⟩ := rank_one_error_sequence J G hAnn hd hs.le
  exact ideal_intersection_transfer hP J hsmall I I' hI hI'
    (hP.left hseq pG (hsmall _ hseq.finite₃ hq))

/-- The rank-one witness transfers to every coherent sheaf supported in its closed image. -/
theorem rank_one_supported {P : X.Modules → Prop} (hP : TwoOutOfThree P)
    (Z : Closeds X) (hZ : IsIrreducible (Z : Set X))
    (hsmall : ∀ W : Closeds X, W < Z → IsIrreducible (W : Set X) →
      ∀ I : (reducedClosedSubscheme W).IdealSheafData,
        P ((pushforward (reducedClosedSubschemeι W)).obj (idealModule I)))
    (w : ClosedRankOneWitness P Z hZ) (M : X.Modules) [M.IsFinitePresentation]
    (hM : support M ⊆ Z) : P M := by
  let : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    reducedClosedSubscheme_isIntegral Z hZ
  have := w.finite
  have hzero : P 0 := hP.zero_of_member w.sheaf w.property
  have hi := ideals_of_generic_rank_one hP (Scheme.IdealSheafData.vanishingIdeal Z) w
    (fun N hN hs ↦ property_of_strict_support hP hzero Z hsmall N (by
      simpa only [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] using hs))
  apply geometric_ideal_criterion hP.middle hzero (Z : Set X) _ M hM
  intro W hW hWZ I hI
  rcases lt_or_eq_of_le (show W ≤ Z from hWZ) with hlt | rfl
  · exact hsmall W hlt hW I
  · exact hi I hI

/-- Two-out-of-three restricted to sequences supported in the specified closed set. -/
structure TwoOutOfThreeOn (P : X.Modules → Prop) (Z : Set X) : Prop where
  left : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → support S.X₂ ⊆ Z →
    P S.X₂ → P S.X₃ → P S.X₁
  middle : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → support S.X₂ ⊆ Z →
    P S.X₁ → P S.X₃ → P S.X₂
  right : ∀ {S : ShortComplex X.Modules}, CoherentSequence S → support S.X₂ ⊆ Z →
    P S.X₁ → P S.X₂ → P S.X₃

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Extend a supported property class to the ambient category by retaining its support bound. -/
theorem TwoOutOfThreeOn.supported {P : X.Modules → Prop} {Z : Set X}
    (hP : TwoOutOfThreeOn P Z) : TwoOutOfThree (fun N ↦ support N ⊆ Z ∧ P N) where
  left {S} h h₂ h₃ := by
    have := h.shortExact.mono_f
    exact ⟨(support_subset_of_mono S.f).trans h₂.1, hP.left h h₂.1 h₂.2 h₃.2⟩
  middle {S} h h₁ h₃ := by
    have hs : support S.X₂ ⊆ Z := by
      rw [support_shortExact h.shortExact]
      exact Set.union_subset h₁.1 h₃.1
    exact ⟨hs, hP.middle h hs h₁.2 h₃.2⟩
  right {S} h h₁ h₂ := by
    have := h.shortExact.epi_g
    exact ⟨(support_subset_of_epi S.g).trans h₂.1, hP.right h h₂.1 h₁.2 h₂.2⟩

/-- Stacks 01YH with two-out-of-three assumed only on the given closed support. -/
theorem rank_one_supported_on {P : X.Modules → Prop}
    (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) (hP : TwoOutOfThreeOn P Z)
    (hsmall : ∀ W : Closeds X, W < Z → IsIrreducible (W : Set X) →
      ∀ I : (reducedClosedSubscheme W).IdealSheafData,
        P ((pushforward (reducedClosedSubschemeι W)).obj (idealModule I)))
    (w : ClosedRankOneWitness P Z hZ) (M : X.Modules) [M.IsFinitePresentation]
    (hM : support M ⊆ Z) : P M := by
  let : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    reducedClosedSubscheme_isIntegral Z hZ
  let Q := fun N : X.Modules ↦ support N ⊆ (Z : Set X) ∧ P N
  let wQ : ClosedRankOneWitness Q Z hZ :=
    { sheaf := w.sheaf
      finite := w.finite
      support_eq := w.support_eq
      annihilated := w.annihilated
      rank_one := w.rank_one
      property := ⟨by simpa [Scheme.IdealSheafData.range_subschemeι]
        using w.support_eq.le, w.property⟩ }
  have hs : ∀ W : Closeds X, W < Z → IsIrreducible (W : Set X) →
      ∀ I : (reducedClosedSubscheme W).IdealSheafData,
        Q ((pushforward (reducedClosedSubschemeι W)).obj (idealModule I)) := by
    intro W hW hWirr I
    refine ⟨?_, hsmall W hW hWirr I⟩
    have h := support_closedPushforward_subset_range (reducedClosedSubschemeι W) (idealModule I)
    rw [range_reducedClosedSubschemeι] at h
    exact h.trans hW.le
  exact (rank_one_supported hP.supported Z hZ hs wQ M hM).2

end FLT.Mazur.FCurve.CoherentDevissage
