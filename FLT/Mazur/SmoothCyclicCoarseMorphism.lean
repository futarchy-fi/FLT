/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicCoarseTransformation
public import FLT.Mazur.CyclicCharacteristicSmoothUnmarkedClass

/-!
# Actual normalized coarse morphisms of original smooth ample cyclic families

Evaluating the proved coarse transformation on the original family's canonical
unmarked class gives a scheme morphism. It retains every normalized chart,
commutes with arbitrary base change, and respects full compatible isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {S : Scheme} {E : GeneralizedEllipticCurve S}
  [Smooth E.curve.hom] (H : E.FiniteSubgroup n) (hc : H.IsCyclic) (ha : H.IsAmple)

/-- The actual scheme morphism of an original smooth ample cyclic family to the coarse scheme. -/
def smoothCoarseMorphism : S ⟶ invariantOrbitScheme n :=
  ((normalizedCoarseTransformation n).hom.app (Opposite.op S)
    (smoothUnmarkedClass n H hc ha)).down

/-- Every normalized presentation retains its prescribed original coarse chart morphism. -/
theorem smoothCoarseMorphism_parameter (b : Bool) (q : S ⟶ normalizedLocus n b)
    (hq : (normalizedModuliMap n b).app (Opposite.op S) (ULift.up q) =
      Quotient.mk _ ⟨⟨E, H⟩, hc, ha⟩) :
    smoothCoarseMorphism n H hc ha = q ≫ normalizedCoarseChart n b := by
  unfold smoothCoarseMorphism
  rw [smoothUnmarkedClass_parameter n H hc ha b q hq]
  exact congrArg ULift.down (normalizedCoarseTransformation_evaluation n b q)

/-- The original coarse morphism commutes with arbitrary scheme base change. -/
theorem smoothCoarseMorphism_pullback {T : Scheme} (g : T ⟶ S)
    [Smooth (E.baseChange g).curve.hom] :
    smoothCoarseMorphism n (H.baseChange g) (hc.baseChange H g) (ha.baseChange g) =
      g ≫ smoothCoarseMorphism n H hc ha := by
  have h := NatTrans.naturality_apply (normalizedCoarseTransformation n).hom g.op
    (smoothUnmarkedClass n H hc ha)
  rw [smoothUnmarkedClass_pullback] at h
  exact congrArg ULift.down h

/-- Full compatible original subgroup isomorphisms preserve the coarse scheme morphism. -/
theorem smoothCoarseMorphism_compatible {F : GeneralizedEllipticCurve S}
    [Smooth F.curve.hom] (J : F.FiniteSubgroup n) (jc : J.IsCyclic) (ja : J.IsAmple)
    (a : CompatibleIso H J) :
    smoothCoarseMorphism n H hc ha = smoothCoarseMorphism n J jc ja := by
  unfold smoothCoarseMorphism
  rw [smoothUnmarkedClass_compatible n H hc ha J jc ja a]

end FLT.Mazur.CyclicCharacteristicOrbit
