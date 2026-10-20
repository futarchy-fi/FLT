/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTraceGluing
public import FLT.Mazur.AffineLocallyFreeRelationNorm

/-!
# Invariant traces from the entire original relation

Whole-fiber rebasing makes the glued trace invariant. Cartesian transport
uses independent local bases on both sides and retains every original arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffineTraceGluing
open AffineNormCartesianGluing
variable {P X T Y : Scheme.{u}} [IsAffine T] [IsAffine Y]
  {a : P ⟶ X} {b : P ⟶ T} {f : X ⟶ Y} {g : T ⟶ Y}
  (H : IsPullback a b f g) [IsAffineHom f] [IsAffineHom b]
  {ι : Type v} (U : ι → Y.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis f (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- Each glued trace commutes with an arbitrary affine cartesian change of target. -/
theorem trace_pullback (s : Γ(X, ⊤)) :
    trace b (changedChart (g := g) U) (changedChart_basis H U hU)
      (changedChart_cover U hcover) (a.appTop s) =
        g.appTop (trace f U hU hcover s) := by
  symm
  apply eq_trace
  intro i
  rw [AffineTraceCharts.chart_pullback f H (U i) (changedChart U i) le_rfl (hU i)]
  dsimp only [changedChart]
  rw [Scheme.Hom.appLE_eq_app]
  have hn := congrArg (g.app (U i).1) (trace_chart f U hU hcover s i)
  exact (ConcreteCategory.congr_hom (g.naturality (homOfLE le_top).op)
    (trace f U hU hcover s)).symm.trans hn

include H in
/-- Independent covers on the changed target compute the same pulled-back trace. -/
theorem trace_pullback_any {κ : Type w} (V : κ → T.affineOpens)
    (hV : ∀ j, AffineOpenNorm.HasBasis b (V j)) (hcoverV : ⨆ j, (V j).1 = ⊤)
    (s : Γ(X, ⊤)) :
    trace b V hV hcoverV (a.appTop s) =
      g.appTop (trace f U hU hcover s) := by
  rw [trace_independent b V hV hcoverV (changedChart U)
    (changedChart_basis H U hU) (changedChart_cover U hcover)]
  exact trace_pullback H U hU hcover s

/-- Isomorphic whole source algebras preserve traces across unrelated local covers. -/
theorem trace_transport {E F T : Scheme.{u}} [IsAffine T]
    (p : E ⟶ T) (q : F ⟶ T) [IsAffineHom p] [IsAffineHom q]
    {ι : Type v} {κ : Type w} (U : ι → T.affineOpens)
    (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcoverU : ⨆ i, (U i).1 = ⊤)
    (V : κ → T.affineOpens) (hV : ∀ j, AffineOpenNorm.HasBasis q (V j))
    (hcoverV : ⨆ j, (V j).1 = ⊤) (e : E ≅ F) (he : e.hom ≫ q = p)
    (s : Γ(F, ⊤)) :
    trace p U hU hcoverU (e.hom.appTop s) = trace q V hV hcoverV s := by
  have H : IsPullback e.hom p q (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id p).symm⟩
  simpa only [Scheme.Hom.id_appTop, CommRingCat.id_apply] using
    trace_pullback_any H V hV hcoverV U hU hcoverU s

end FLT.Mazur.AffineTraceGluing

namespace FLT.Mazur.AffineLocallyFreeRelationTrace
open AffineTraceGluing AffineNormCartesianGluing
variable {D A : Scheme.{u}} [IsAffine D] [IsAffine A] (p q : D ⟶ A)
  {ι : Type v} (U : ι → A.affineOpens)
  (hU : ∀ i, AffineOpenNorm.HasBasis p (U i)) (hcover : ⨆ i, (U i).1 = ⊤)

/-- A global multiplication trace of the whole original relation. -/
def relationTrace (s : Γ(A, ⊤)) : Γ(A, ⊤) :=
  trace p U hU hcover (q.appTop s)

variable (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Whole-fiber rebasing proves trace equality on every original affine relation test. -/
theorem relationTrace_test {T : Scheme.{u}} [IsAffine T] (a : T ⟶ D)
    (s : Γ(A, ⊤)) :
    (a ≫ p).appTop (relationTrace p q U hU hcover s) =
      (a ≫ q).appTop (relationTrace p q U hU hcover s) := by
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
  unfold relationTrace
  rw [← trace_pullback Hp U hU hcover,
    ← trace_pullback Hq U hU hcover, ← hs]
  exact trace_transport _ _
    (changedChart U) (changedChart_basis Hp U hU) (changedChart_cover U hcover)
    (changedChart U) (changedChart_basis Hq U hU) (changedChart_cover U hcover) i hi _

include e in
/-- Every trace lies in the unchanged equalizer of both full original projections. -/
theorem relationTrace_invariant (s : Γ(A, ⊤)) :
    p.appTop (relationTrace p q U hU hcover s) =
      q.appTop (relationTrace p q U hU hcover s) := by
  simpa only [Category.id_comp] using
    relationTrace_test p q U hU hcover e (𝟙 D) s

end FLT.Mazur.AffineLocallyFreeRelationTrace
