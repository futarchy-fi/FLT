/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveLocalMarkingFrames
public import FLT.Mazur.GeneralizedCurveMarkingCoordinateRing

/-!
# Actual local cubic rings for all original singular families

Every base point has an affine neighborhood carrying the constructed equation
and complement function-ring isomorphism. The actual map retains the original
base morphism. For higher polygons the complement need not itself be affine;
no isomorphism from that complement or the whole curve is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory Scheme.Modules
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle Scheme.Modules.pullback

variable {S : Scheme} (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) {V : S.Opens} {x : S} (hx : x ∈ V)

/-- A chosen affine neighborhood with a frame of the actual marking-restricted line. -/
def markingFrameNeighborhood : S.affineOpens :=
  (exists_smoothMarking_affineFrame E s hx).choose

/-- The chosen original neighborhood contains the specified point. -/
theorem mem_markingFrameNeighborhood : x ∈ (markingFrameNeighborhood E s hx).1 :=
  (exists_smoothMarking_affineFrame E s hx).choose_spec.1

/-- The construction stays inside any prescribed original base neighborhood. -/
theorem markingFrameNeighborhood_le : (markingFrameNeighborhood E s hx).1 ≤ V :=
  (exists_smoothMarking_affineFrame E s hx).choose_spec.2.1

local notation "U" => Subtype.val (markingFrameNeighborhood E s hx)
local notation "E'" => baseChange E (Scheme.Opens.ι (U))
local notation "s'" => pullSection (Scheme.Opens.ι (U)) s
local notation "t'" => s' ≫ inclusion (E')

/-- The frame belongs to the actual marked line of the original base change. -/
def markingNeighborhoodFrame :
    (pullback (t').left).obj
      (divisorLineBundle (t').left.ker (smoothMarking_relativeCartier (E') (s')).1) ≅
        structureModule (U).toScheme :=
  (exists_smoothMarking_affineFrame E s hx).choose_spec.2.2.some

variable [IsLocallyNoetherian S]

local instance markingNeighborhoodAffine : IsAffine (U).toScheme :=
  (markingFrameNeighborhood E s hx).2

local instance markingNeighborhoodNoetherian : IsNoetherianRing Γ((U).toScheme, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The equation is constructed at every base point, including all singular fibers. -/
def markingNeighborhoodEquation : WeierstrassCurve Γ((U).toScheme, ⊤) :=
  smoothMarkingWeierstrassCurve (E') (s') (markingNeighborhoodFrame E s hx)

local notation "W" => markingNeighborhoodEquation E s hx
local notation "C" => Scheme.Opens.toScheme (X := Over.left (curve (E')))
  (TopologicalSpace.Closeds.compl
    (Scheme.IdealSheafData.support (Scheme.Hom.ker (Over.Hom.left (t')))))

/-- The cubic ring is the full ring of functions of the original local complement. -/
def markingNeighborhoodCoordinateRingEquiv : (W).toAffine.CoordinateRing ≃+* Γ(C, ⊤) :=
  smoothMarkingCoordinateRingEquiv (E') (s') (markingNeighborhoodFrame E s hx)

/-- The actual local morphism to the cubic uses the constructed original coordinates. -/
def markingNeighborhoodToAffineCubic : C ⟶ Spec (.of (W).toAffine.CoordinateRing) :=
  smoothMarkingToAffineCubic (E') (s') (markingNeighborhoodFrame E s hx)

/-- The constructed local morphism retains the original structure map. -/
theorem markingNeighborhoodToAffineCubic_over :
    markingNeighborhoodToAffineCubic E s hx ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ((U).toScheme, ⊤)
        (W).toAffine.CoordinateRing)) =
          (Scheme.Opens.ι (X := (E').curve.left) (t').left.ker.support.compl) ≫
            (E').curve.hom ≫ (U).toScheme.toSpecΓ :=
  smoothMarkingToAffineCubic_over (E') (s') (markingNeighborhoodFrame E s hx)

/-- The ring comparison respects the original coefficient map on the same neighborhood. -/
theorem markingNeighborhoodCoordinateRingEquiv_scalar (a : Γ((U).toScheme, ⊤)) :
    markingNeighborhoodCoordinateRingEquiv E s hx
      (algebraMap Γ((U).toScheme, ⊤) (W).toAffine.CoordinateRing a) =
        smoothMarkingComplementBaseMap (E') (s') a :=
  smoothMarkingCoordinateRingEquiv_scalar (E') (s') (markingNeighborhoodFrame E s hx) a

end FLT.Mazur.GeneralizedEllipticCurve
