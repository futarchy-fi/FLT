/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantSheaf
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

/-!
# The orbit topology of the locally ringed coequalizer

The constructed orbit space is the topological coequalizer. Since the
locally-ringed-space forgetful functor preserves coequalizers, it is canonically
homeomorphic to the carrier of the actual locally ringed quotient. Local
ringedness alone does not establish the affine neighborhoods required of a scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The actual orbit projection gives a cofork of the two topological relation maps. -/
def orbitCofork : Cofork p.left.base q.left.base :=
  Cofork.ofπ (quotientMap e) (relation_quotientMap e)

/-- The orbit topology satisfies the full topological coequalizer universal property. -/
def orbitCoforkIsColimit : IsColimit (orbitCofork e) := by
  apply Cofork.IsColimit.mk'
  intro s
  have hs (a : A.left) : s.π (p.left a) = s.π (q.left a) :=
    congrArg (fun k ↦ k a) s.condition
  let d : space e ⟶ s.pt := TopCat.ofHom
    ⟨descend e s.π hs, descend_continuous e s.π hs s.π.hom.continuous⟩
  refine ⟨d, ?_, ?_⟩
  · ext x
    rfl
  · intro m hm
    ext z
    obtain ⟨x, rfl⟩ := projection_surjective e z
    exact congrArg (fun k ↦ k x) hm

/-- The locally ringed quotient exists independently of scheme effectivity. -/
def locallyRingedQuotient : LocallyRingedSpace.{u} :=
  coequalizer p.left.toLRSHom q.left.toLRSHom

/-- The original source morphism into the locally ringed quotient. -/
def locallyRingedProjection : U.left.toLocallyRingedSpace ⟶ locallyRingedQuotient
    (p := p) (q := q) := coequalizer.π _ _

local instance forgetToTop_preservesCoequalizers :
    PreservesColimitsOfShape WalkingParallelPair LocallyRingedSpace.forgetToTop.{u} :=
  inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat.{u}))

/-- The underlying orbit space agrees with the actual locally ringed coequalizer carrier. -/
def locallyRingedOrbitIso :
    LocallyRingedSpace.forgetToTop.obj (locallyRingedQuotient (p := p) (q := q)) ≅ space e :=
  (PreservesCoequalizer.iso LocallyRingedSpace.forgetToTop
    p.left.toLRSHom q.left.toLRSHom).symm ≪≫
    (coequalizerIsCoequalizer p.left.base q.left.base).coconePointUniqueUpToIso
      (orbitCoforkIsColimit e)

/-- The comparison identifies the quotient projection with the actual orbit projection. -/
theorem locallyRingedProjection_orbitIso :
    LocallyRingedSpace.forgetToTop.map (locallyRingedProjection (p := p) (q := q)) ≫
      (locallyRingedOrbitIso e).hom = quotientMap e := by
  dsimp only [locallyRingedOrbitIso, Iso.trans_hom, Iso.symm_hom,
    locallyRingedProjection, locallyRingedQuotient]
  rw [← Category.assoc, map_π_preserves_coequalizer_inv]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coequalizerIsCoequalizer p.left.base q.left.base)
    (orbitCoforkIsColimit e) WalkingParallelPair.one

/-- The carrier comparison is a homeomorphism with the constructed actual orbit space. -/
def locallyRingedOrbitHomeomorph : locallyRingedQuotient (p := p) (q := q) ≃ₜ Orbit e :=
  TopCat.homeoOfIso (locallyRingedOrbitIso e)

/-- The carrier homeomorphism sends the original source point to its actual orbit. -/
theorem locallyRingedOrbitHomeomorph_projection (x : U.left) :
    locallyRingedOrbitHomeomorph e ((locallyRingedProjection (p := p) (q := q)).base x) =
      projection e x :=
  congrArg (fun k ↦ k x) (locallyRingedProjection_orbitIso e)

include e in
/-- Equality under the locally ringed quotient is precisely the original point relation. -/
theorem locallyRingedProjection_eq_iff (x y : U.left) :
    (locallyRingedProjection (p := p) (q := q)).base x =
      (locallyRingedProjection (p := p) (q := q)).base y ↔ Related p q x y := by
  rw [← (locallyRingedOrbitHomeomorph e).injective.eq_iff,
    locallyRingedOrbitHomeomorph_projection, locallyRingedOrbitHomeomorph_projection,
    projection_eq_iff]

include e in
/-- Every locally ringed quotient point comes from the actual source. -/
theorem locallyRingedProjection_surjective :
    Function.Surjective (locallyRingedProjection (p := p) (q := q)).base := by
  intro z
  obtain ⟨x, hx⟩ := projection_surjective e (locallyRingedOrbitHomeomorph e z)
  refine ⟨x, (locallyRingedOrbitHomeomorph e).injective ?_⟩
  exact (locallyRingedOrbitHomeomorph_projection e x).trans hx

include e in
/-- An open relation projection makes the actual locally ringed quotient map open. -/
theorem locallyRingedProjection_isOpenMap (hq : IsOpenMap q.left) :
    IsOpenMap (locallyRingedProjection (p := p) (q := q)).base := by
  apply (locallyRingedOrbitHomeomorph e).comp_isOpenMap_iff.mp
  have he : locallyRingedOrbitHomeomorph e ∘
      (locallyRingedProjection (p := p) (q := q)).base = projection e :=
    funext (locallyRingedOrbitHomeomorph_projection e)
  rw [he]
  exact projection_isOpenMap e hq

/-- The quotient is over the original base in locally ringed spaces. -/
def locallyRingedBaseMap : locallyRingedQuotient (p := p) (q := q) ⟶
    S.toLocallyRingedSpace :=
  coequalizer.desc U.hom.toLRSHom
    (congrArg Scheme.Hom.toLRSHom ((Over.w p).trans (Over.w q).symm))

/-- Its structural map factors the original source-to-base morphism. -/
theorem locallyRingedProjection_baseMap :
    locallyRingedProjection (p := p) (q := q) ≫ locallyRingedBaseMap = U.hom.toLRSHom :=
  coequalizer.π_desc _ _

end FLT.Mazur.RelativeRelationOrbit
