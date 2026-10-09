/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnionGluing

/-!
# Literal covers of pullbacks of ambient unions

The full intersection of two image unions is covered by the actual
pairwise pullbacks of their source schemes in the ambient scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v w

variable {X : Scheme.{u}} {ι : Type v} {κ : Type w}
  {V : ι → Scheme.{u}} {W : κ → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) (g : ∀ j, W j ⟶ X)
  [∀ i, IsOpenImmersion (f i)] [∀ j, IsOpenImmersion (g j)]

/-- A literal pairwise pullback maps to the pullback of the whole unions. -/
def openImageUnionPullbackMap (i : ι) (j : κ) :
    pullback (f i) (g j) ⟶ pullback (openImageUnion f).ι (openImageUnion g).ι :=
  pullback.lift (pullback.fst _ _ ≫ openImageUnionMap f i)
    (pullback.snd _ _ ≫ openImageUnionMap g j) (by simp [pullback.condition])

/-- The first projection retains the literal first overlap. -/
@[reassoc (attr := simp)] theorem openImageUnionPullbackMap_fst (i : ι) (j : κ) :
    openImageUnionPullbackMap f g i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ openImageUnionMap f i := pullback.lift_fst _ _ _

/-- The second projection retains the literal second overlap. -/
@[reassoc (attr := simp)] theorem openImageUnionPullbackMap_snd (i : ι) (j : κ) :
    openImageUnionPullbackMap f g i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ openImageUnionMap g j := pullback.lift_snd _ _ _

/-- Every literal pairwise pullback is open in the full ambient intersection. -/
instance openImageUnionPullbackMap_isOpenImmersion (i : ι) (j : κ) :
    IsOpenImmersion (openImageUnionPullbackMap f g i j) := by
  have : IsOpenImmersion (openImageUnionPullbackMap f g i j ≫ pullback.fst _ _) := by
    rw [openImageUnionPullbackMap_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst (openImageUnion f).ι (openImageUnion g).ι)

/-- Pairwise literal pullbacks cover the entire pullback of the two unions. -/
def openImageUnionPullbackCover :
    (pullback (openImageUnion f).ι (openImageUnion g).ι).OpenCover where
  I₀ := ι × κ
  X p := pullback (f p.1) (g p.2)
  f p := openImageUnionPullbackMap f g p.1 p.2
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    let d := pullback.fst (openImageUnion f).ι (openImageUnion g).ι ≫ (openImageUnion f).ι
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((pullback.fst (openImageUnion f).ι (openImageUnion g).ι) z).2
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((pullback.snd (openImageUnion f).ι (openImageUnion g).ι) z).2
    have hz : d z ∈ Set.range (pullback.fst (f i) (g j) ≫ f i) := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      refine ⟨hi, ?_⟩
      change (pullback.fst (openImageUnion f).ι (openImageUnion g).ι ≫
        (openImageUnion f).ι) z ∈ _
      rw [pullback.condition]
      exact hj
    obtain ⟨w, hw⟩ := hz
    refine ⟨(i, j), w, ?_⟩
    apply d.isOpenEmbedding.injective
    change (openImageUnionPullbackMap f g i j ≫ d) w = d z
    simpa only [d, openImageUnionPullbackMap_fst_assoc, Category.assoc,
      openImageUnionMap_fac] using hw

/-- Equality on every literal double overlap detects equality on the full union pullback. -/
theorem openImageUnionPullback_hom_ext {T : Scheme.{u}}
    (a b : pullback (openImageUnion f).ι (openImageUnion g).ι ⟶ T)
    (h : ∀ i j, openImageUnionPullbackMap f g i j ≫ a =
      openImageUnionPullbackMap f g i j ≫ b) : a = b :=
  (openImageUnionPullbackCover f g).hom_ext a b (fun p ↦ h p.1 p.2)

end FLT.Mazur
