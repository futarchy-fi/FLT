/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeWholeFiberOpenComposition
public import FLT.Mazur.SchemeOpenPairSectionRestriction
public import FLT.Mazur.SchemeAdicVanishingOpen

/-!
# Source sections constructed from relation neighborhoods

An equality on a relation open constructs an equality on both-endpoint
restrictions to its first-endpoint whole-fiber open. Restricting an ambient
boundary lift keeps the exact boundary value. The source open may be empty;
its scalar avoidance is a separate condition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open SchemeWholeFiberOpen SchemeAdicVanishingNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {X Z Y : Scheme} (f g : Z ⟶ X) (L : Z.Opens) (a : Γ(X, ⊤))

/-- The full two-endpoint open lies in the given good relation open. -/
theorem pairOpenDomain_wholeFiber_le : pairOpenDomain (locus f L) f g ≤ L :=
  inf_le_left.trans (preimage_le f L)

/-- An ambient equation on the relation constructs a raw compatible source section. -/
theorem wholeFiber_restricted_pair_equation
    (h : (L.ι ≫ f).appTop a = (L.ι ≫ g).appTop a) :
    (pairOpenFirst (locus f L) f g).appTop ((locus f L).ι.appTop a) =
      (pairOpenSecond (locus f L) f g).appTop ((locus f L).ι.appTop a) := by
  have he := congrArg (fun t ↦
    (Z.homOfLE (pairOpenDomain_wholeFiber_le f g L)).appTop t) h
  change ((Z.homOfLE (pairOpenDomain_wholeFiber_le f g L) ≫ L.ι) ≫ f).appTop a =
    ((Z.homOfLE (pairOpenDomain_wholeFiber_le f g L) ≫ L.ι) ≫ g).appTop a at he
  rw [Scheme.homOfLE_ι] at he
  change (pairOpenFirst (locus f L) f g ≫ (locus f L).ι).appTop a =
    (pairOpenSecond (locus f L) f g ≫ (locus f L).ι).appTop a
  simpa only [pairOpenFirst, pairOpenSecond, Scheme.Hom.resLE_comp_ι] using he

/-- Restricting a global lift preserves its exact boundary, including nilpotents. -/
theorem restricted_global_boundary_equation (O : X.Opens) (i : Y ⟶ X)
    (t : Γ(Y, ⊤)) (h : i.appTop a = t) :
    (i ∣_ O).appTop (O.ι.appTop a) = (i ⁻¹ᵁ O).ι.appTop t := by
  change ((i ∣_ O) ≫ O.ι).appTop a = _
  rw [morphismRestrict_ι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h]

/-- A fixed coefficient supplies a canonical good source open from its actual zero germs. -/
def coefficientRelationSourceOpen : X.Opens :=
  locus f (vanishingOpen (f.appTop a - g.appTop a))

/-- The canonical source section equalizes the entire restricted relation. -/
theorem coefficientRelationSourceOpen_pair_equation :
    (pairOpenFirst (coefficientRelationSourceOpen f g a) f g).appTop
        ((coefficientRelationSourceOpen f g a).ι.appTop a) =
      (pairOpenSecond (coefficientRelationSourceOpen f g a) f g).appTop
        ((coefficientRelationSourceOpen f g a).ι.appTop a) := by
  apply wholeFiber_restricted_pair_equation
  have h := vanishingOpen_inclusion_zero (f.appTop a - g.appTop a)
  rw [map_sub, sub_eq_zero] at h
  exact h

end FLT.Mazur.SchemeFiniteGroupQuotient
