/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseEnvelope

/-!
# Tensor envelopes for Cartesian translation restrictions

If the localized translation is the full base change of the original
translation, its envelope comparison is a base change of the source
comparison. An unchanged source therefore gives an isomorphism of envelopes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.HilbertChart.AffineRestriction
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  (a : Spec (.of R') ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V)
  {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (u : (Over.map a).obj B ⟶ A)

/-- A Cartesian independent translation gives a Cartesian envelope comparison. -/
theorem fixedBaseEnvelopeMap_isPullback
    (ht : IsPullback t.left W.hom V.hom a) :
    IsPullback (fixedBaseEnvelopeMap a V W t u).left
      (prod.fst : prod B W ⟶ B).left (prod.fst : prod A V ⟶ A).left u.left := by
  have hB := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd B W)).flip
  have hA := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A V)).flip
  have hs := hB.paste_horiz ht
  have hu : B.hom ≫ a = u.left ≫ A.hom := u.w.symm
  have h₁ := congrArg Over.Hom.left (fixedBaseEnvelopeMap_fst a V W t u)
  have h₂ := congrArg Over.Hom.left (fixedBaseEnvelopeMap_snd a V W t u)
  simp only [Over.comp_left, Over.map_map_left] at h₁ h₂
  simp only [BinaryFan.mk_fst, BinaryFan.mk_snd] at hs hA
  rw [hu, ← h₂] at hs
  exact hs.of_right h₁ hA

/-- With the original source retained, full translation base change retains the entire envelope. -/
theorem fixedBaseEnvelopeMap_isIso [IsIso u]
    (ht : IsPullback t.left W.hom V.hom a) :
    IsIso (fixedBaseEnvelopeMap a V W t u).left :=
  (fixedBaseEnvelopeMap_isPullback a V W t u ht).isIso_fst_of_isIso

end FLT.Mazur.HilbertChart.AffineRestriction
