/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkedCubicComparison

/-!
# Coherence of the constructed marked cubic comparisons

Independent frames on three marked families satisfy the cubic cocycle whenever
the actual family isomorphisms compose. The whole original curve maps determine
the transition, so the result retains higher polygons and nilpotent bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FCurve.divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve markedCubicComparison
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {E F G : GeneralizedEllipticCurve S}
  (e : E ≅ F) (d : F ≅ G)
  (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
  (u : 𝟙_ (Over S) ⟶ G.group)
  (hs : s ≫ e.hom.group = t) (ht : t ≫ d.hom.group = u)
  (a : SmoothMarkingFrame E s) (b : SmoothMarkingFrame F t) (c : SmoothMarkingFrame G u)

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
include hs ht in
/-- The actual marked family composite carries the original marking to the third one. -/
theorem markedFamily_comp_section : s ≫ (e ≪≫ d).hom.group = u := by
  change s ≫ (e.hom.group ≫ d.hom.group) = u
  rw [← Category.assoc, hs, ht]

/-- The constructed cubic comparisons obey composition for independent marking frames. -/
theorem markedCubicComparison_comp :
    markedCubicComparison d t u ht b c ≪≫ markedCubicComparison e s t hs a b =
      markedCubicComparison (e ≪≫ d) s u (markedFamily_comp_section e d s t u hs ht) a c := by
  apply Iso.ext
  apply markedCubicComparison_unique
  · rw [Iso.trans_hom, Category.assoc, markedCubicComparison_over,
      markedCubicComparison_over]
  · rw [Iso.trans_hom, ← Category.assoc, markedCubicComparison_whole,
      Category.assoc, markedCubicComparison_whole]
    rfl

/-- Recomputing a cubic with the identical family, marking and frame is the identity. -/
theorem markedCubicComparison_refl (E : GeneralizedEllipticCurve S)
    (s : 𝟙_ (Over S) ⟶ E.group) (a : SmoothMarkingFrame E s) :
    markedCubicComparison (Iso.refl E) s s (Category.comp_id s) a a =
      Iso.refl (integralCurve (smoothMarkingWeierstrassCurve E s a)) := by
  apply Iso.ext
  symm
  apply markedCubicComparison_unique
  · exact Category.id_comp _
  · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]

end FLT.Mazur.GeneralizedEllipticCurve
