/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationIncompleteFrameGrowth

/-!
# Maximal frame sizes over an unchanged scalar character

The size set consists of actual normalized frames with endpoints in the given
open and with the specified scalar map. A uniform geometric rank bound makes
this set finite. Incompleteness at a maximal size contradicts strict growth.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (e : CategoryTheory.EquivalenceRelation p q) (E : A.Opens)
  {R : Type} [CommRing R] (s : R →+* Γ(E.toScheme, ⊤))
  {F : Type} [Field F] (t : Spec (.of F) ⟶ Spec (.of R))
local instance scalarRanksOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarRanksOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarRanksOver_quasiCompact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] source Complete

/-- Sizes realized by actual frames over the fixed original scalar character. -/
@[irreducible] def scalarFrameSizes : Set ℕ :=
  {n | ∃ (o : Fin n) (u : Spec (.of F) ⟶ source p q (Fin n) o)
    (b : Spec (.of F) ⟶ E.toScheme),
    u ≫ first p q (Fin n) o = b ≫ E.ι ∧ b ≫ scalarMorphism s = t}

omit [Etale p] [QuasiCompact p] in
/-- A frame and its original endpoint exhibit a realized scalar size. -/
theorem mem_scalarFrameSizes (n : ℕ) (o : Fin n)
    (u : Spec (.of F) ⟶ source p q (Fin n) o) (b : Spec (.of F) ⟶ E.toScheme)
    (hu : u ≫ first p q (Fin n) o = b ≫ E.ι) (hb : b ≫ scalarMorphism s = t) :
    n ∈ scalarFrameSizes (p := p) (q := q) E s t := by
  rw [scalarFrameSizes]
  exact ⟨o, u, b, hu, hb⟩

/-- The geometric uniform rank bound bounds every realized scalar size. -/
theorem scalarFrameSizes_bounded [TopologicalSpace.NoetherianSpace A] :
    ∃ N : ℕ, ∀ n ∈ scalarFrameSizes (p := p) (q := q) E s t, n ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound (Over.mk p)
  refine ⟨N, ?_⟩
  intro n hn
  rw [scalarFrameSizes] at hn
  obtain ⟨o, u, b, hu, hb⟩ := hn
  apply hN ((u ≫ first p q (Fin n) o) default) n
  exact ⟨(testFrame (Fin n) o u).left (default : Spec (.of F)),
    congrArg (fun g : Spec (.of F) ⟶ A ↦ g default) (testFrame (Fin n) o u).w⟩

include e in
/-- Every original endpoint character supplies a nonempty set of realized sizes. -/
theorem scalarFrameSizes_nonempty [IsSepClosed F]
    (b : Spec (.of F) ⟶ E.toScheme) (hb : b ≫ scalarMorphism s = t) :
    (scalarFrameSizes (p := p) (q := q) E s t).Nonempty := by
  obtain ⟨n, o, u, hu, _⟩ := exists_complete_normalized_lift e (b ≫ E.ι)
  exact ⟨n, mem_scalarFrameSizes E s t n o u b hu hb⟩

/-- An inhabited original scalar size set has an attained greatest size. -/
theorem exists_maximal_scalarFrameSize [TopologicalSpace.NoetherianSpace A]
    (h : (scalarFrameSizes (p := p) (q := q) E s t).Nonempty) :
    ∃ n ∈ scalarFrameSizes (p := p) (q := q) E s t,
      ∀ m ∈ scalarFrameSizes (p := p) (q := q) E s t, m ≤ n := by
  obtain ⟨N, hN⟩ := scalarFrameSizes_bounded (p := p) (q := q) E s t
  have hf : (scalarFrameSizes (p := p) (q := q) E s t).Finite :=
    (Set.finite_Iic N).subset hN
  obtain ⟨n, hn, hm⟩ := Finset.exists_max_image hf.toFinset id
    (by simpa only [Set.Finite.toFinset_nonempty] using h)
  exact ⟨n, hf.mem_toFinset.mp hn, fun m hm' ↦ hm m (hf.mem_toFinset.mpr hm')⟩

include e in
/-- Every realized frame at the greatest original scalar size is complete. -/
theorem complete_of_maximal_scalarFrameSize [IsSepClosed F] (n : ℕ)
    (hmax : ∀ m ∈ scalarFrameSizes (p := p) (q := q) E s t, m ≤ n)
    (o : Fin n) (u : Spec (.of F) ⟶ source p q (Fin n) o)
    (b : Spec (.of F) ⟶ E.toScheme)
    (hu : u ≫ first p q (Fin n) o = b ≫ E.ι) (hb : b ≫ scalarMorphism s = t) :
    Complete (Fin n) o u := by
  by_contra hc
  obtain ⟨m, j, v, hnm, hv, _⟩ := exists_strictly_larger_complete_frame e n o u hc
  have hm := mem_scalarFrameSizes E s t m j v b (hv.trans hu) hb
  exact (Nat.not_le_of_gt hnm) (hmax m hm)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
