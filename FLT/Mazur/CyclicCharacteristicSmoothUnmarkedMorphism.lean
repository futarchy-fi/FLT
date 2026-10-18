/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicSmoothUnmarkedClass
public import FLT.Mazur.CyclicCharacteristicUnmarkedSchemeDescent

/-!
# Scheme-valued evaluation on original smooth modular objects

Evaluating the constructed sheaf morphism on an original smooth family's
canonical class gives an actual scheme morphism. It commutes with base change
and is uniquely characterized by all genuine normalized comparisons. Thus
the sheaf construction recovers the earlier concrete fppf descent morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme} (v : ∀ b, normalizedLocus n b ⟶ Y)
  (hv : UnmarkedInvariant n v)
  {S : Scheme} {E : GeneralizedEllipticCurve S} [Smooth E.curve.hom]
  (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)

/-- Evaluate the invariant's actual sheaf morphism on the original smooth modular object. -/
def smoothUnmarkedMorphism : S ⟶ Y :=
  ((unmarkedSchemeDesc n v hv).hom.app (Opposite.op S)
    (smoothUnmarkedClass n H hc ha)).down

/-- The actual scheme-valued evaluation commutes with arbitrary base change. -/
theorem smoothUnmarkedMorphism_pullback {T : Scheme} (g : T ⟶ S)
    [Smooth (E.baseChange g).curve.hom] :
    g ≫ smoothUnmarkedMorphism n v hv H hc ha =
      smoothUnmarkedMorphism n v hv (H.baseChange g) (hc.baseChange H g) (ha.baseChange g) := by
  have he := (unmarkedSchemeDesc n v hv).hom.naturality_apply g.op
    (smoothUnmarkedClass n H hc ha)
  rw [smoothUnmarkedClass_pullback] at he
  exact congrArg ULift.down he.symm

/-- Every genuine normalized comparison evaluates to the supplied chart morphism. -/
theorem smoothUnmarkedMorphism_evaluation {T : Scheme} (g : T ⟶ S) (b : Bool)
    (q : T ⟶ normalizedLocus n b)
    (hq : Nonempty (CompatibleIso ((normalizedSubgroup n b).baseChange q) (H.baseChange g))) :
    g ≫ smoothUnmarkedMorphism n v hv H hc ha = q ≫ v b := by
  let _ : Smooth (E.baseChange g).curve.hom :=
    inferInstanceAs (Smooth (pullback.snd E.curve.hom g))
  rw [smoothUnmarkedMorphism_pullback]
  have hp : (normalizedModuliMap n b).app (Opposite.op T) (ULift.up q) =
      Quotient.mk _ ⟨⟨E.baseChange g, H.baseChange g⟩,
        hc.baseChange H g, ha.baseChange g⟩ := by
    rw [normalizedModuliMap_eq_pullback]
    exact Quotient.sound hq
  unfold smoothUnmarkedMorphism
  rw [smoothUnmarkedClass_parameter n _ _ _ b q hp]
  exact congrArg ULift.down (unmarkedSchemeDesc_evaluation n v hv b q)

/-- Sheaf evaluation is the unique actual morphism detected by all original normalized tests. -/
theorem smoothUnmarkedMorphism_unique
    (d : S ⟶ Y)
    (hd : ∀ (T : Scheme) (g : T ⟶ S) (b : Bool) (q : T ⟶ normalizedLocus n b),
      Nonempty (CompatibleIso ((normalizedSubgroup n b).baseChange q) (H.baseChange g)) →
        g ≫ d = q ≫ v b) : d = smoothUnmarkedMorphism n v hv H hc ha := by
  obtain ⟨e, _, hu⟩ := unmarkedInvariant_smooth_unique_evaluation n v hv H hc ha
  exact (hu d hd).trans (hu _ (fun _ g b q hq ↦
    smoothUnmarkedMorphism_evaluation n v hv H hc ha g b q hq)).symm

end FLT.Mazur.CyclicCharacteristicAtlas
