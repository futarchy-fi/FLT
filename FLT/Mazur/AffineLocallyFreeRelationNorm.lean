/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNormCartesianGluing
public import FLT.Mazur.EquivalenceRelationFiberRebase

/-!
# Invariant norms from local bases of the whole original relation

Whole-fiber rebasing preserves the glued norm. The original first projection
only needs a cover by finite free charts, whose bases and ranks may vary.
The charts need not themselves be invariant under the relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffineNormGluing

/-- An isomorphism over the target preserves norms computed on unrelated local free covers. -/
theorem norm_transport {E F T : Scheme.{u}} [IsAffine T] (p : E ⟶ T) (q : F ⟶ T)
    [IsAffineHom p] [IsAffineHom q] {ι : Type v} {κ : Type w}
    (U : ι → T.affineOpens) (hU : ∀ i, AffineOpenNorm.HasBasis p (U i))
    (hcoverU : ⨆ i, (U i).1 = ⊤) (V : κ → T.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis q (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (e : E ≅ F) (he : e.hom ≫ q = p) (s : Γ(F, ⊤)) :
    norm p U hU hcoverU (e.hom.appTop s) = norm q V hV hcoverV s := by
  have H : IsPullback e.hom p q (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id p).symm⟩
  simpa only [Scheme.Hom.id_appTop, CommRingCat.id_apply] using
    AffineNormCartesianGluing.norm_pullback_any H V hV hcoverV U hU hcoverU s

end FLT.Mazur.AffineNormGluing

namespace FLT.Mazur.AffineLocallyFreeRelationNorm
open AffineNormCartesianGluing
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- The whole original relation norm constructed using its actual finite free charts. -/
def relationNorm (s : Γ(A, ⊤)) : Γ(A, ⊤) :=
  AffineNormGluing.norm p U hU hcover (q.appTop s)

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Whole-fiber rebasing gives the norm equation on any original affine relation test. -/
theorem relationNorm_test {T : Scheme.{u}} [IsAffine T] (a : T ⟶ D) (s : Γ(A, ⊤)) :
    (a ≫ p).appTop (relationNorm p q U hU hcover s) =
      (a ≫ q).appTop (relationNorm p q U hU hcover s) := by
  let i := EquivalenceRelationFiber.rebaseIso e a
  have hi : i.hom ≫ pullback.snd p (a ≫ q) = pullback.snd p (a ≫ p) :=
    EquivalenceRelationFiber.rebase_snd e a
  have hq : i.hom ≫ pullback.fst p (a ≫ q) ≫ q =
      pullback.fst p (a ≫ p) ≫ q := by
    change EquivalenceRelationFiber.rebase e a ≫ pullback.fst p (a ≫ q) ≫ q = _
    rw [EquivalenceRelationFiber.rebase_fst_assoc,
      EquivalenceRelationFiber.rebaseArrow_snd]
  have hs := congrArg (fun h ↦ h.appTop s) hq
  change i.hom.appTop ((pullback.fst p (a ≫ q)).appTop (q.appTop s)) =
    (pullback.fst p (a ≫ p)).appTop (q.appTop s) at hs
  let Hp := IsPullback.of_hasPullback p (a ≫ p)
  let Hq := IsPullback.of_hasPullback p (a ≫ q)
  unfold relationNorm
  rw [← norm_pullback Hp U hU hcover, ← norm_pullback Hq U hU hcover, ← hs]
  exact AffineNormGluing.norm_transport _ _
    (changedChart U) (changedChart_basis Hp U hU) (changedChart_cover U hcover)
    (changedChart U) (changedChart_basis Hq U hU) (changedChart_cover U hcover) i hi _

include e in
/-- The locally constructed norm is invariant under both original projections. -/
theorem relationNorm_invariant (s : Γ(A, ⊤)) :
    p.appTop (relationNorm p q U hU hcover s) =
      q.appTop (relationNorm p q U hU hcover s) := by
  simpa only [Category.id_comp] using relationNorm_test p q U hU hcover e (𝟙 D) s

/-- The relation norm tests all original second endpoints in the first-projection fiber. -/
theorem mem_basicOpen_relationNorm_iff (s : Γ(A, ⊤)) (x : A) :
    x ∈ A.basicOpen (relationNorm p q U hU hcover s) ↔
      ∀ z : D, p z = x → q z ∈ A.basicOpen s := by
  rw [relationNorm, AffineNormGluing.mem_basicOpen_norm_iff]
  rw [← Scheme.preimage_basicOpen_top q s]
  rfl

end FLT.Mazur.AffineLocallyFreeRelationNorm
