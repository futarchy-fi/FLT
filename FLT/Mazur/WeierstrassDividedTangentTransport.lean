/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianCoefficientTransportNaturality
public import FLT.Mazur.WeierstrassDividedTangentCechIso

/-!
# Overlap transport of the original finite model

Construct the finite model comparison over every coefficient overlap and
identify its actual double-overlap instance with the previously constructed
Cech isomorphism. The original integral model projection is retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "q" => nodeTangentCover W
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "ys" => pullback.fst q base
local notation "yx" => pullback.snd q base
variable {T : Scheme.{u}} (r t : T ⟶ Spec (.of (AdjoinRoot (nodeTangentPolynomial W))))
  (h : r ≫ nodeTangentCover W = t ≫ nodeTangentCover W)

/-- The constructed transport of the whole original finite model between coefficient lifts. -/
def finiteGlobalTangentTransport : pullback r ys ≅ pullback t ys :=
  CartesianCoefficientTransport.iso (IsPullback.of_hasPullback q base).flip r t h

@[reassoc] theorem finiteGlobalTangentTransport_structure :
    (finiteGlobalTangentTransport hπ data j hj r t h).hom ≫ pullback.fst t ys =
      pullback.fst r ys := CartesianCoefficientTransport.map_coefficient _ _ _ h

/-- The comparison keeps the actual integral finite model, not merely its component labels. -/
@[reassoc] theorem finiteGlobalTangentTransport_projection :
    (finiteGlobalTangentTransport hπ data j hj r t h).hom ≫ pullback.snd t ys ≫ yx =
      pullback.snd r ys ≫ yx := CartesianCoefficientTransport.map_original _ _ _ h

/-- The model comparison satisfies the full composition law on arbitrary overlaps. -/
@[reassoc] theorem finiteGlobalTangentTransport_comp
    (w : T ⟶ Spec (.of (AdjoinRoot (nodeTangentPolynomial W))))
    (ht : t ≫ nodeTangentCover W = w ≫ nodeTangentCover W) :
    (finiteGlobalTangentTransport hπ data j hj r t h).hom ≫
        (finiteGlobalTangentTransport hπ data j hj t w ht).hom =
      (finiteGlobalTangentTransport hπ data j hj r w (h.trans ht)).hom :=
  CartesianCoefficientTransport.map_comp _ _ _ h _ ht

/-- Transport along the repeated coefficient lift is the identity on the whole model. -/
theorem finiteGlobalTangentTransport_self :
    (finiteGlobalTangentTransport hπ data j hj r r rfl).hom = 𝟙 _ :=
  CartesianCoefficientTransport.map_self _ _

omit r t h in
/-- The existing comparison on the genuine quadratic Cech scheme is this canonical transport. -/
theorem finiteGlobalTangentCechIso_eq_transport :
    finiteGlobalTangentCechIso hπ data j hj =
      finiteGlobalTangentTransport hπ data j hj (pullback.fst q q) (pullback.snd q q)
        pullback.condition := by
  apply Iso.ext
  apply CartesianCoefficientTransport.hom_ext (IsPullback.of_hasPullback q base).flip
    (pullback.snd q q)
  · rw [finiteGlobalTangentCechIso_structure, finiteGlobalTangentTransport_structure]
  · rw [finiteGlobalTangentCechIso_projection, finiteGlobalTangentTransport_projection]

end FLT.Mazur.WeierstrassDividedDepth
