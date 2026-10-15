/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranscendentalResidueMorphismConjugacy
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Independent larger-field lifts over the unchanged original base

A residue-field preimmersion transports whole-morphism conjugacy back to the
original coefficient scheme. The larger field may be transcendental; the
chosen algebraic-closure lift supplies the residue algebraicity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OriginalTranscendentalResidueConjugacy
set_option backward.isDefEq.respectTransparency false
variable {k L K : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [IsAlgClosed L] [Algebra.IsAlgebraic k L] {S X : Scheme}
  (t : Spec (.of k) ⟶ S) [IsPreimmersion t]

/-- All independent lifts at the same original support factor through a closure conjugate. -/
theorem exists_conjugacy (f : X ⟶ S)
    (p : Spec (.of L) ⟶ X) (q : Spec (.of K) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ t)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ t)
    (hx : p default = q default) :
    ∃ σ : L ≃ₐ[k] L, Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p = q := by
  let cL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let cK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let P := pullback f t
  let p' : Spec (.of L) ⟶ P := pullback.lift p cL hp
  let q' : Spec (.of K) ⟶ P := pullback.lift q cK hq
  have hsame : p' default = q' default := by
    apply (pullback.fst f t).isEmbedding.injective
    change (p' ≫ pullback.fst f t) default = (q' ≫ pullback.fst f t) default
    simpa only [p', q', pullback.lift_fst] using hx
  obtain ⟨σ, hσ⟩ := TranscendentalResidueMorphismConjugacy.exists_conjugacy
    (pullback.snd f t) p' q' (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hsame
  refine ⟨σ, ?_⟩
  have h := congrArg (fun v : Spec (.of K) ⟶ P ↦ v ≫ pullback.fst f t) hσ
  simpa only [Category.assoc, p', q', pullback.lift_fst] using h

end FLT.Mazur.OriginalTranscendentalResidueConjugacy
