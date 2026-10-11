/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGlobalRankOneDivisorNaturality
public import FLT.Mazur.ProperAcyclicDirectImageRepresentation

/-!
# The canonical full divisor on the varying acyclic rank-one open

The constructed open carries an actual relative Cartier divisor. On every
unrestricted test factoring through that open, the canonical full divisor
is its geometric comap along the constructed map of total spaces.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
  properLineAcyclicRankOneOpen properLineGlobalAcyclicOpen
variable {X S : Scheme.{0}} [IsLocallyNoetherian S]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)

local notation "V" => properLineAcyclicRankOneOpen f L hL
local notation "H" => IsPullback.flip (isPullback_morphismRestrict f V)

omit [GeometricallyIntegral f] in
/-- Every fiber of the original line restricted to the simultaneous open is acyclic. -/
lemma acyclicRankOneOpen_fibers (t : (V).toScheme) (n : ℕ) :
    Subsingleton (ModuleH ((pullback ((f ∣_ V).fiberι t)).obj
      ((pullback (f ⁻¹ᵁ V).ι).obj L)) (n + 1)) :=
  (properLine_fiber_vanishing_iff H L hL t (n + 1)).mpr
    ((mem_properLineGlobalAcyclicOpen f L hL ((V).ι t)).mp
      (properLineAcyclicRankOneOpen_le f L hL t.property) n)

/-- The actual full relative Cartier divisor on the constructed varying-family open. -/
@[irreducible] def acyclicRankOneOpenDivisor :
    RelativeFiber (f ∣_ V) ((pullback (f ⁻¹ᵁ V).ι).obj L) (hL.pullback _) :=
  acyclicRankOneFamilyDivisor H L hL (acyclicRankOneOpen_fibers f L hL)
    (properLineAcyclicRankOneOpen_directImage_rankOne f L hL)

variable {P T : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
  (h : IsPullback p q f g)
  (a : T ⟶ (properLineAcyclicRankOneOpen f L hL).toScheme)
  (ha : a ≫ (properLineAcyclicRankOneOpen f L hL).ι = g)

/-- The actual map from a factored test total space to the restricted universal family. -/
def acyclicRankOneOpenFamilyMap : P ⟶ (f ⁻¹ᵁ V).toScheme := by
  have w : p ≫ f = (q ≫ a) ≫ (V).ι := by rw [Category.assoc, ha, h.w]
  exact (H).lift p (q ≫ a) w

omit [GeometricallyIntegral f] in
/-- The universal total-space map retains the original map to the total space. -/
lemma acyclicRankOneOpenFamilyMap_fst :
    acyclicRankOneOpenFamilyMap f L hL h a ha ≫ (f ⁻¹ᵁ V).ι = p := (H).lift_fst _ _ _

omit [GeometricallyIntegral f] in
/-- The universal total-space map retains the independently specified test factorization. -/
lemma acyclicRankOneOpenFamilyMap_snd :
    acyclicRankOneOpenFamilyMap f L hL h a ha ≫ (f ∣_ V) = q ≫ a := (H).lift_snd _ _ _

/-- Any canonical divisor on a factored test is comap of the full divisor on the actual open. -/
theorem acyclicRankOneFamilyDivisor_eq_open_comap
    (hV : ∀ t : T, ∀ n, Subsingleton
      (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1)))
    (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L))) :
    (acyclicRankOneFamilyDivisor h L hL hV hN).val.val.val =
      (acyclicRankOneOpenDivisor f L hL).val.val.val.comap
        (acyclicRankOneOpenFamilyMap f L hL h a ha) := by
  unfold acyclicRankOneOpenDivisor
  exact acyclicRankOneFamilyDivisor_natural_ideal H h a
    (acyclicRankOneOpenFamilyMap f L hL h a ha)
    (acyclicRankOneOpenFamilyMap_fst f L hL h a ha)
    (acyclicRankOneOpenFamilyMap_snd f L hL h a ha) ha L hL
    (acyclicRankOneOpen_fibers f L hL)
    (properLineAcyclicRankOneOpen_directImage_rankOne f L hL) hV hN

end FLT.Mazur.CartierAbel
