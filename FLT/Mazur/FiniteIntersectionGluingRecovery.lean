/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionDiagramGluing

/-!
# Recovering a covered scheme by intersection gluing

The actual finite intersection diagram has the original covered scheme as
its colimit. Consequently the glue data constructed from its cartesian
union squares recovers that scheme. The proof checks compatibility on the
actual pairwise pullbacks, rather than assuming a gluing conclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)

/-- The union intersection is the pullback of two intersection opens over the ambient scheme. -/
theorem finiteIntersectionOpen_isPullback_over (s t : NonemptyChartSet ι) :
    IsPullback
      (X.homOfLE (finiteIntersectionOpen_antitone U (le_unionChartSet_left s t)))
      (X.homOfLE (finiteIntersectionOpen_antitone U (le_unionChartSet_right s t)))
      (finiteIntersectionOpen U s).ι (finiteIntersectionOpen U t).ι := by
  apply (isPullback_opens_inf (finiteIntersectionOpen U s)
    (finiteIntersectionOpen U t)).of_iso
    (X.isoOfEq (finiteIntersectionOpen_union U s t).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [← cancel_mono (finiteIntersectionOpen U s).ι]
  · simp [← cancel_mono (finiteIntersectionOpen U t).ι]
  · simp
  · simp

/-- The canonical cocone of intersection inclusions into the covered scheme. -/
def finiteIntersectionSchemeCocone : Cocone (finiteIntersectionSchemeDiagram U) where
  pt := X
  ι.app s := (finiteIntersectionOpen U s.unop).ι
  ι.naturality {s t} f := by
    change X.homOfLE (finiteIntersectionOpen_antitone U (leOfHom f.unop)) ≫ _ = _ ≫ 𝟙 X
    simp

/-- A cover by the original opens makes the intersection cocone a colimit. -/
def finiteIntersectionSchemeCoconeIsColimit (hcover : iSup U = ⊤) :
    IsColimit (finiteIntersectionSchemeCocone U) := by
  let C := X.openCoverOfIsOpenCover (finiteIntersectionOpen U)
    (finiteIntersectionOpen_cover U hcover)
  let compat (c : Cocone (finiteIntersectionSchemeDiagram U))
      (s t : NonemptyChartSet ι) :
      pullback.fst (C.f s) (C.f t) ≫ c.ι.app (Opposite.op s) =
        pullback.snd (C.f s) (C.f t) ≫ c.ι.app (Opposite.op t) := by
    change pullback.fst (finiteIntersectionOpen U s).ι (finiteIntersectionOpen U t).ι ≫ _ =
      pullback.snd (finiteIntersectionOpen U s).ι (finiteIntersectionOpen U t).ι ≫ _
    rw [← cancel_epi (finiteIntersectionOpen_isPullback_over U s t).isoPullback.hom]
    rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    exact (c.w (homOfLE (le_unionChartSet_left s t)).op).trans
      (c.w (homOfLE (le_unionChartSet_right s t)).op).symm
  refine
    { desc := fun c ↦ C.glueMorphisms (fun s ↦ c.ι.app (Opposite.op s)) (compat c)
      fac := ?_
      uniq := ?_ }
  · intro c s
    exact C.ι_glueMorphisms _ _ s.unop
  · intro c m hm
    apply C.hom_ext
    intro s
    exact (hm (Opposite.op s)).trans
      (C.ι_glueMorphisms (fun s ↦ c.ι.app (Opposite.op s)) (compat c) s).symm

/-- The actual intersection diagram satisfies the locally directed gluing condition. -/
instance finiteIntersectionSchemeDiagram_isLocallyDirected :
    (finiteIntersectionSchemeDiagram U ⋙ Scheme.forget).IsLocallyDirected :=
  intersectionDiagram_isLocallyDirected _ (finiteIntersectionOpen_isPullback U)

/-- Gluing the intersection diagram recovers the original covered scheme. -/
def finiteIntersectionGluingIso [Finite ι] (hcover : iSup U = ⊤) :
    (intersectionDiagramGlueData (finiteIntersectionSchemeDiagram U)
      (finiteIntersectionOpen_isPullback U)).glued ≅ X :=
  (Scheme.IsLocallyDirected.isColimit (finiteIntersectionSchemeDiagram U)).coconePointUniqueUpToIso
    (finiteIntersectionSchemeCoconeIsColimit U hcover)

end FLT.Mazur.Approximation
