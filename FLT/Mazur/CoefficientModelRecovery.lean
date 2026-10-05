/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelLimit
public import FLT.Mazur.ModuleLineBundlePullback

/-!
# Cartesian and line-sheaf recovery through coefficient enlargement

A cartesian recovery square at the initial stage induces one at every finite
coefficient enlargement. The line sheaf pulls back along the same recovery
map, so an eventual-property theorem can enlarge the coefficients without
losing the original sheaf identification.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {A : Type u} [CommRing A] {S₀ : Subalgebra ℤ A}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {p : X ⟶ Spec (.of A)}
  {q : Y ⟶ Spec (.of S₀)}
  (h : IsPullback f p q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
  (i : (CoefficientStage S₀)ᵒᵖ)

/-- The original scheme maps to every coefficient enlargement of the fixed model. -/
def coefficientModelRecovery : X ⟶ (coefficientModelDiagram S₀ q).obj i :=
  pullback.lift f (p ≫ (coefficientSpectrumCone S₀).π.app i) (by
    rw [Category.assoc, coefficientSpectrumCone_toInitial]
    exact h.w)

/-- Enlargement does not change the composite recovery map to the initial model. -/
theorem coefficientModelRecovery_fst :
    coefficientModelRecovery h i ≫
      pullback.fst q ((coefficientSpectrumToInitial S₀).app i) = f := by
  simp [coefficientModelRecovery]

/-- The recovery square at every enlarged coefficient stage is cartesian. -/
theorem coefficientModelRecovery_isPullback :
    IsPullback (coefficientModelRecovery h i) p
      (pullback.snd q ((coefficientSpectrumToInitial S₀).app i))
      ((coefficientSpectrumCone S₀).π.app i) := by
  apply IsPullback.of_right _ (by simp [coefficientModelRecovery])
    (IsPullback.of_hasPullback q ((coefficientSpectrumToInitial S₀).app i))
  simpa [coefficientModelRecovery_fst, coefficientSpectrumCone_toInitial] using h

/-- The model line sheaf at an enlarged stage is its actual sheaf pullback. -/
def coefficientModelSheaf (M : Y.Modules) : ((coefficientModelDiagram S₀ q).obj i).Modules :=
  (Scheme.Modules.pullback (pullback.fst q ((coefficientSpectrumToInitial S₀).app i))).obj M

/-- Rank one persists under coefficient enlargement. -/
theorem coefficientModelSheaf_rankOne {M : Y.Modules}
    (hM : FLT.Mazur.FCurve.LocallyFreeRankOne M) :
    FLT.Mazur.FCurve.LocallyFreeRankOne (coefficientModelSheaf (q := q) i M) :=
  hM.pullback _

/-- The actual recovery map pulls the enlarged model sheaf back to the original sheaf. -/
def coefficientModelSheafRecoveryIso {M : Y.Modules} {L : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ L) :
    (Scheme.Modules.pullback (coefficientModelRecovery h i)).obj
      (coefficientModelSheaf (q := q) i M) ≅ L :=
  (Scheme.Modules.pullbackComp (coefficientModelRecovery h i)
    (pullback.fst q ((coefficientSpectrumToInitial S₀).app i))).app M ≪≫
    (Scheme.Modules.pullbackCongr (coefficientModelRecovery_fst h i)).app M ≪≫ e

end FLT.Mazur.Approximation
