/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveLocalPointFrames
public import FLT.Mazur.GeneralizedCurvePointedCubicPresentation

/-!
# Affine local pointed cubic presentations without an assumed frame

On a locally Noetherian base, every original smooth geometrically integral
family admits complete pointed cubic presentations near every base point.
The frame is constructed on the actual base restriction, so the original
varying family, coefficient map and marking are retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S)
  [SmoothOfRelativeDimension 1 E.curve.hom] (s : 𝟙_ (Over S) ⟶ E.curve)
  {V : S.Opens} {x : S} (hx : x ∈ V)

/-- An affine neighborhood carrying the actual restricted point-line frame. -/
def pointFrameNeighborhood : S.affineOpens :=
  (exists_smoothPoint_affineFrame E s hx).choose

/-- The neighborhood still contains the specified original base point. -/
theorem mem_pointFrameNeighborhood : x ∈ (pointFrameNeighborhood E s hx).1 :=
  (exists_smoothPoint_affineFrame E s hx).choose_spec.1

/-- The neighborhood stays within the originally prescribed base open. -/
theorem pointFrameNeighborhood_le : (pointFrameNeighborhood E s hx).1 ≤ V :=
  (exists_smoothPoint_affineFrame E s hx).choose_spec.2.1

local notation "U" => Subtype.val (pointFrameNeighborhood E s hx)
local notation "E'" => baseChange E (Scheme.Opens.ι (U))
local notation "s'" => pullSection (Scheme.Opens.ι (U)) s

/-- The actual framed restricted point line on the chosen neighborhood. -/
def pointNeighborhoodFrame :
    (pullback (s').left).obj
      (divisorLineBundle (s').left.ker (smoothPoint_cartier (E') (s'))) ≅
      structureModule (U).toScheme :=
  (exists_smoothPoint_affineFrame E s hx).choose_spec.2.2.some

variable [IsLocallyNoetherian S] [GeometricallyIntegral E.curve.hom]

local instance pointNeighborhoodAffine : IsAffine (U).toScheme :=
  (pointFrameNeighborhood E s hx).2

local instance pointNeighborhoodNoetherian : IsNoetherianRing Γ((U).toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

local instance pointNeighborhoodIntegral : GeometricallyIntegral (E').curve.hom :=
  inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd E.curve.hom (U).ι))

/-- The coefficients produced from the actual original family on this base neighborhood. -/
def pointNeighborhoodEquation : WeierstrassCurve Γ((U).toScheme, ⊤) :=
  smoothPointCubicEquation (E') (s') (pointNeighborhoodFrame E s hx)

/-- The original local coefficient equation is nonsingular. -/
theorem pointNeighborhoodEquation_isElliptic :
    (pointNeighborhoodEquation E s hx).IsElliptic :=
  smoothPointCubicEquation_isElliptic (E') (s') (pointNeighborhoodFrame E s hx)

/-- A complete projective presentation of the actual base-changed curve. -/
def pointNeighborhoodCubicIso :
    (E').curve.left ≅ integralCurve (pointNeighborhoodEquation E s hx) :=
  smoothPointCubicIso (E') (s') (pointNeighborhoodFrame E s hx)

/-- The full comparison retains the actual structural map on the chosen neighborhood. -/
@[reassoc] theorem pointNeighborhoodCubicIso_over :
    (pointNeighborhoodCubicIso E s hx).hom ≫
      integralCurveStructure (pointNeighborhoodEquation E s hx) =
        (E').curve.hom ≫ (U).toScheme.toSpecΓ :=
  smoothPointCubicIso_over (E') (s') (pointNeighborhoodFrame E s hx)

/-- The specified original marking becomes the infinity section on the same base. -/
@[reassoc] theorem pointNeighborhoodCubicIso_marking :
    (s').left ≫ (pointNeighborhoodCubicIso E s hx).hom =
      (U).toScheme.toSpecΓ ≫ integralCurveZero (pointNeighborhoodEquation E s hx) :=
  smoothPointCubicIso_marking (E') (s') (pointNeighborhoodFrame E s hx)

end FLT.Mazur.GeneralizedEllipticCurve
