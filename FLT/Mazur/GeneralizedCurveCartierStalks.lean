/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealStalkDescent
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup

/-!
# Cartier stalk generators for fppf-cyclic subgroups

The local Cartier witnesses descend regular generators of the actual ideal
stalks. Flatness of the subgroup divisor is already unconditional. Obtaining
Cartier neighborhoods still requires finite-presentation/local-freeness descent.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ} (H : E.FiniteSubgroup n)

/-- The subgroup divisor is flat over the base, independently of cyclicity. -/
instance ideal_flat : Flat (H.ideal.subschemeι ≫ E.curve.hom) := H.ideal_degree.2.1

/-- For a finite subgroup, only the effective Cartier half remains to prove. -/
theorem relativeCartier_iff_effectiveCartier :
    FCurve.RelativeEffectiveCartier E.curve.hom H.ideal ↔ FCurve.EffectiveCartier H.ideal :=
  ⟨And.left, fun h ↦ ⟨h, inferInstance⟩⟩

/-- Fppf-local Cartier generators give regular generators of every actual ideal stalk. -/
theorem IsCyclic.ideal_stalk_generator (hH : H.IsCyclic) (x : E.curve.left) :
    ∃ a : E.curve.left.presheaf.stalk x, IsRegular a ∧
      AnnihilatorSubsheaf.stalkIdeal H.ideal x = Ideal.span {a} := by
  obtain ⟨U, g, hg, hs, _hl, P, hP⟩ := hH
  let := hg
  let := hs
  apply FCurve.stalk_generators_of_flat_surjective_comap H.ideal (pullback.fst E.curve.hom g)
    (y := x)
  simpa only [baseChange_ideal] using hP.2.1.1

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
