/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierComplementRestriction
public import FLT.Mazur.ChowProductOpenGluing

/-!
# The Cartier complement detects maps to separated targets

Faithful restriction on every open proves schematic density of the original
Cartier complement. Consequently agreement there extends across the divisor,
including on nonreduced schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)

local notation "j" => Scheme.Opens.ι (X := X) (TopologicalSpace.Closeds.compl
  (Scheme.IdealSheafData.support I))

include hI

/-- The actual complement inclusion is injective on every structure-sheaf section space. -/
theorem cartierComplement_app_injective (W : X.Opens) :
    Function.Injective ((j).app W) := by
  intro a b hab
  apply cartierComplement_restrict_injective hI W
  rw [Scheme.Opens.ι_app] at hab
  have he : W ⊓ I.support.compl ≤ (j) ''ᵁ ((j) ⁻¹ᵁ W) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  have h := congrArg (X.presheaf.map (homOfLE he).op) hab
  have hc : X.presheaf.map (homOfLE ((j).image_preimage_le W)).op ≫
      X.presheaf.map (homOfLE he).op =
        X.presheaf.map (homOfLE (show W ⊓ I.support.compl ≤ W from inf_le_left)).op := by
    rw [← Functor.map_comp]
    rfl
  exact (ConcreteCategory.congr_hom hc a).symm.trans
    (h.trans (ConcreteCategory.congr_hom hc b))

variable [QuasiCompact (Scheme.Opens.ι (X := X) I.support.compl)]

/-- The original Cartier complement is schematically dense, with nilpotents retained. -/
theorem cartierComplement_schematicallyDense :
    IsSchemeTheoreticallyDominant (j) := by
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply, (RingHom.injective_iff_ker_eq_bot _).mp
    (cartierComplement_app_injective hI U)]
  rfl

/-- Two morphisms over a separated target base agree if their actual Cartier restrictions agree. -/
theorem cartierComplement_hom_ext {Y S : Scheme.{u}} (p : Y ⟶ S) [IsSeparated p]
    (f g : X ⟶ Y) (hb : f ≫ p = g ≫ p)
    (hc : (j) ≫ f = (j) ≫ g) : f = g := by
  let _ := cartierComplement_schematicallyDense hI
  exact Chow.schematicallyDense_ext p hb (j) hc

end FLT.Mazur.FCurve
