/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAcyclicRankOneUniversalDivisor
public import FLT.Mazur.RelativeAcyclicClassDivisor

/-!
# Full relative nonspecial divisors near a geometric nonspecial restriction

The cohomological open contains the specified test and carries the actual
relative Cartier divisor. Both maps of the original test square factor through
the open family; its full ideal and its relative Picard class are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] properLineAcyclicRankOneOpen

variable {P X T S : Scheme} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S} (H : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include H in
/-- The nonspecial geometric test factors through an open carrying a full acyclic divisor. -/
theorem exists_nonspecial_divisor_neighborhood
    (hA : GeometricAcyclicRankOne q ((Scheme.Modules.pullback p).obj L)) :
    ∃ (V : S.Opens) (a : T ⟶ V.toScheme) (b : P ⟶ (f ⁻¹ᵁ V).toScheme)
      (D : AcyclicRankOneRelativeDivisor (f ∣_ V)),
      a ≫ V.ι = g ∧ b ≫ (f ⁻¹ᵁ V).ι = p ∧ IsPullback b q (f ∣_ V) a ∧
      abel (f ∣_ V) D.val = SchemePicard.relativeClass (f ∣_ V)
        (SchemePicard.mk ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L) (hL.pullback _)) := by
  let V := properLineAcyclicRankOneOpen f L hL
  obtain ⟨a, ha, _⟩ := (properLineAcyclicRankOneOpen_represents f L hL H).mp hA
  change a ≫ V.ι = g at ha
  let b := acyclicRankOneOpenFamilyMap f L hL H a ha
  have hb : b ≫ (f ⁻¹ᵁ V).ι = p := acyclicRankOneOpenFamilyMap_fst f L hL H a ha
  have hq : b ≫ (f ∣_ V) = q ≫ a := acyclicRankOneOpenFamilyMap_snd f L hL H a ha
  have HB : IsPullback b q (f ∣_ V) a := by
    apply IsPullback.of_right (h₁₂ := (f ⁻¹ᵁ V).ι) (h₂₂ := V.ι) (v₁₃ := f)
      ?_ hq (isPullback_morphismRestrict f V).flip
    simpa only [hb, ha] using H
  let E := acyclicRankOneOpenDivisor f L hL
  have hC : AcyclicRankOne (f ∣_ V) ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L) :=
    ⟨acyclicRankOneOpen_fibers f L hL, properLineAcyclicRankOneOpen_directImage_rankOne f L hL⟩
  have hD : AcyclicRankOne (f ∣_ V)
      (divisorLineBundle E.val.val.val E.val.val.property) :=
    (acyclicRankOne_relativeClass_iff (f ∣_ V) (hL.pullback _)
      E.val.val.property.divisorLineBundle_locallyFreeRankOne E.val.property.symm).mp hC
  exact ⟨V, a, b, ⟨E.val.val, E.property, hD⟩, ha, hb, HB, E.val.property⟩

end FLT.Mazur.CartierAbel
