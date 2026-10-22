/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingLocalCubic
public import FLT.Mazur.GeneralizedCurveMarkingProjectiveIso

/-!
# Projective cubic comparisons on original affine frame neighborhoods

Every point of a locally noetherian base has a proper pointed cubic morphism
from the entire original family on an affine neighborhood. For integral
geometric fibers this is a full scheme isomorphism, including singular fibers.
Higher polygons retain their contraction map without an isomorphism claim.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle Scheme.Modules.pullback

variable {S : Scheme} [IsLocallyNoetherian S] (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) {V : S.Opens} {x : S} (hx : x ∈ V)

local notation "U" => Subtype.val (markingFrameNeighborhood E s hx)
local notation "E'" => baseChange E (Scheme.Opens.ι (U))
local notation "s'" => pullSection (Scheme.Opens.ι (U)) s
local notation "t'" => s' ≫ inclusion (E')
local notation "W" => markingNeighborhoodEquation E s hx

local instance markingProjectiveNeighborhoodAffine : IsAffine (U).toScheme :=
  (markingFrameNeighborhood E s hx).2

local instance markingProjectiveNeighborhoodNoetherian : IsNoetherianRing Γ((U).toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The full original family has its constructed projective cubic map near every base point. -/
def markingNeighborhoodToProjectiveCubic : (E').curve.left ⟶ integralCurve (W) :=
  smoothMarkingToIntegralCubic (E') (s') (markingNeighborhoodFrame E s hx)

/-- The local projective cubic morphism retains the actual base-changed structure map. -/
@[reassoc] theorem markingNeighborhoodToProjectiveCubic_over :
    markingNeighborhoodToProjectiveCubic E s hx ≫ integralCurveStructure (W) =
      (E').curve.hom ≫ (U).toScheme.toSpecΓ :=
  smoothMarkingToIntegralCubic_over (E') (s') (markingNeighborhoodFrame E s hx)

/-- The full local morphism sends the original marking to infinity over the same base. -/
@[reassoc] theorem markingNeighborhoodToProjectiveCubic_marking :
    (t').left ≫ markingNeighborhoodToProjectiveCubic E s hx =
      (U).toScheme.toSpecΓ ≫ integralCurveZero (W) :=
  smoothMarkingToIntegralCubic_marking (E') (s') (markingNeighborhoodFrame E s hx)

/-- Every local cubic contraction is proper, including for higher polygon fibers. -/
theorem markingNeighborhoodToProjectiveCubic_proper :
    IsProper (markingNeighborhoodToProjectiveCubic E s hx) :=
  smoothMarkingToIntegralCubic_proper (E') (s') (markingNeighborhoodFrame E s hx)

variable [GeometricallyIntegral E.curve.hom]

local instance markingProjectiveNeighborhoodIntegral : GeometricallyIntegral (E').curve.hom :=
  inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd E.curve.hom (U).ι))

/-- Integral geometric fibers give a full pointed cubic presentation near every base point. -/
theorem markingNeighborhoodToProjectiveCubic_isIso :
    IsIso (markingNeighborhoodToProjectiveCubic E s hx) :=
  smoothMarkingToIntegralCubic_isIso (E') (s') (markingNeighborhoodFrame E s hx)

/-- The local presentation is the actual original projective coordinate morphism. -/
def markingNeighborhoodProjectiveIso : (E').curve.left ≅ integralCurve (W) := by
  let _ := markingNeighborhoodToProjectiveCubic_isIso E s hx
  exact asIso (markingNeighborhoodToProjectiveCubic E s hx)

end FLT.Mazur.GeneralizedEllipticCurve
