/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCharpolyCoefficientGluing
public import FLT.Mazur.AffineLocallyFreeRelationNorm

/-!
# Full relation invariance from independent local bases

Every glued characteristic coefficient commutes with arbitrary cartesian base
change. Whole-fiber rebasing therefore proves invariance under both original
projections without a global basis or an invariant finite free cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffineCharpolyCoefficientGluing
open AffineNormCartesianGluing
variable {P X T Y : Scheme.{u}} [IsAffine T] [IsAffine Y]
  {a : P ⟶ X} {b : P ⟶ T} {f : X ⟶ Y} {g : T ⟶ Y}
  (H : IsPullback a b f g) [IsAffineHom f] [IsAffineHom b]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- Each glued coefficient commutes with an arbitrary affine cartesian change of target. -/
theorem coefficient_pullback (s : Γ(X, ⊤)) (n : ℕ) :
    coefficient b (changedChart (g := g) U) (changedChart_basis H U hU)
      (changedChart_cover U hcover) (a.appTop s) n =
        g.appTop (coefficient f U hU hcover s n) := by
  symm
  apply eq_coefficient
  intro i
  rw [AffineCharpolyCharts.chart_pullback f H (U i) (changedChart U i) le_rfl (hU i)]
  dsimp only [changedChart]
  rw [Scheme.Hom.appLE_eq_app]
  have hn := congrArg (g.app (U i).1) (coefficient_chart f U hU hcover s n i)
  exact (ConcreteCategory.congr_hom (g.naturality (homOfLE le_top).op)
    (coefficient f U hU hcover s n)).symm.trans hn

include H in
/-- Independent covers on the changed target compute the same pulled-back coefficient. -/
theorem coefficient_pullback_any {κ : Type w} (V : κ → T.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis b (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) (n : ℕ) :
    coefficient b V hV hcoverV (a.appTop s) n =
      g.appTop (coefficient f U hU hcover s n) := by
  rw [coefficient_independent b V hV hcoverV (changedChart U)
    (changedChart_basis H U hU) (changedChart_cover U hcover)]
  exact coefficient_pullback H U hU hcover s n

/-- Isomorphic whole source algebras preserve coefficients across unrelated local covers. -/
theorem coefficient_transport {E F T : Scheme.{u}} [IsAffine T]
    (p : E ⟶ T) (q : F ⟶ T) [IsAffineHom p] [IsAffineHom q]
    {ι : Type v} {κ : Type w} (U : ι → T.affineOpens)
    (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcoverU : ⨆ i, (U i).1 = ⊤)
    (V : κ → T.affineOpens) (hV : ∀ j, AffineOpenNorm.HasBasis q (V j))
    (hcoverV : ⨆ j, (V j).1 = ⊤) (e : E ≅ F) (he : e.hom ≫ q = p)
    (s : Γ(F, ⊤)) (n : ℕ) :
    coefficient p U hU hcoverU (e.hom.appTop s) n = coefficient q V hV hcoverV s n := by
  have H : IsPullback e.hom p q (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id p).symm⟩
  simpa only [Scheme.Hom.id_appTop, CommRingCat.id_apply] using
    coefficient_pullback_any H V hV hcoverV U hU hcoverU s n

end FLT.Mazur.AffineCharpolyCoefficientGluing

namespace FLT.Mazur.AffineLocallyFreeRelationCharpoly
open AffineCharpolyCoefficientGluing AffineNormCartesianGluing
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- A global multiplication coefficient of the whole original relation. -/
def relationCoefficient (s : Γ(A, ⊤)) (n : ℕ) : Γ(A, ⊤) :=
  coefficient p U hU hcover (q.appTop s) n

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Whole-fiber rebasing proves coefficient equality on every original affine relation test. -/
theorem relationCoefficient_test {T : Scheme.{u}} [IsAffine T] (a : T ⟶ D)
    (s : Γ(A, ⊤)) (n : ℕ) :
    (a ≫ p).appTop (relationCoefficient p q U hU hcover s n) =
      (a ≫ q).appTop (relationCoefficient p q U hU hcover s n) := by
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
  unfold relationCoefficient
  rw [← coefficient_pullback Hp U hU hcover,
    ← coefficient_pullback Hq U hU hcover, ← hs]
  exact coefficient_transport _ _
    (changedChart U) (changedChart_basis Hp U hU) (changedChart_cover U hcover)
    (changedChart U) (changedChart_basis Hq U hU) (changedChart_cover U hcover) i hi _ n

include e in
/-- Every coefficient lies in the unchanged equalizer of both full original projections. -/
theorem relationCoefficient_invariant (s : Γ(A, ⊤)) (n : ℕ) :
    p.appTop (relationCoefficient p q U hU hcover s n) =
      q.appTop (relationCoefficient p q U hU hcover s n) := by
  simpa only [Category.id_comp] using
    relationCoefficient_test p q U hU hcover e (𝟙 D) s n

end FLT.Mazur.AffineLocallyFreeRelationCharpoly
