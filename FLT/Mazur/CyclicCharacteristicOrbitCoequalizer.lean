/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantSheaf
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
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- The actual orbit projection gives a cofork of the two topological relation maps. -/
def orbitCofork : Cofork (src).base (tgt).base :=
  Cofork.ofπ (quotientMap n) (relation_quotientMap n)

/-- The orbit topology satisfies the full topological coequalizer universal property. -/
def orbitCoforkIsColimit : IsColimit (orbitCofork n) := by
  apply Cofork.IsColimit.mk'
  intro s
  have hs (a : A) : s.π (src a) = s.π (tgt a) :=
    congrArg (fun k ↦ k a) s.condition
  let d : space n ⟶ s.pt := TopCat.ofHom
    ⟨descend n s.π hs, descend_continuous n s.π hs s.π.hom.continuous⟩
  refine ⟨d, ?_, ?_⟩
  · ext x
    rfl
  · intro m hm
    ext z
    obtain ⟨x, rfl⟩ := projection_surjective n z
    exact congrArg (fun k ↦ k x) hm

/-- The locally ringed quotient exists independently of scheme effectivity. -/
def locallyRingedQuotient : LocallyRingedSpace :=
  coequalizer (src).toLRSHom (tgt).toLRSHom

/-- The original source morphism into the locally ringed quotient. -/
def locallyRingedProjection : (U).toLocallyRingedSpace ⟶ locallyRingedQuotient n :=
  coequalizer.π _ _

local instance forgetToTop_preservesCoequalizers :
    PreservesColimitsOfShape WalkingParallelPair LocallyRingedSpace.forgetToTop :=
  inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair
    (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat))

/-- The underlying orbit space agrees with the actual locally ringed coequalizer carrier. -/
def locallyRingedOrbitIso :
    LocallyRingedSpace.forgetToTop.obj (locallyRingedQuotient n) ≅ space n :=
  (PreservesCoequalizer.iso LocallyRingedSpace.forgetToTop
    (src).toLRSHom (tgt).toLRSHom).symm ≪≫
    (coequalizerIsCoequalizer (src).base (tgt).base).coconePointUniqueUpToIso
      (orbitCoforkIsColimit n)

/-- The comparison identifies the quotient projection with the actual orbit projection. -/
theorem locallyRingedProjection_orbitIso :
    LocallyRingedSpace.forgetToTop.map (locallyRingedProjection n) ≫
      (locallyRingedOrbitIso n).hom = quotientMap n := by
  dsimp only [locallyRingedOrbitIso, Iso.trans_hom, Iso.symm_hom,
    locallyRingedProjection, locallyRingedQuotient]
  rw [← Category.assoc, map_π_preserves_coequalizer_inv]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coequalizerIsCoequalizer (src).base (tgt).base)
    (orbitCoforkIsColimit n) WalkingParallelPair.one

/-- The carrier comparison is a homeomorphism with the constructed actual orbit space. -/
def locallyRingedOrbitHomeomorph : locallyRingedQuotient n ≃ₜ Orbit n :=
  TopCat.homeoOfIso (locallyRingedOrbitIso n)

/-- The carrier homeomorphism sends the original source point to its actual orbit. -/
theorem locallyRingedOrbitHomeomorph_projection (x : U) :
    locallyRingedOrbitHomeomorph n ((locallyRingedProjection n).base x) =
      projection n x :=
  congrArg (fun k ↦ k x) (locallyRingedProjection_orbitIso n)

/-- Equality under the locally ringed quotient is precisely the original point relation. -/
theorem locallyRingedProjection_eq_iff (x y : U) :
    (locallyRingedProjection n).base x =
      (locallyRingedProjection n).base y ↔ Related n x y := by
  rw [← (locallyRingedOrbitHomeomorph n).injective.eq_iff,
    locallyRingedOrbitHomeomorph_projection, locallyRingedOrbitHomeomorph_projection,
    projection_eq_iff]

/-- Every locally ringed quotient point comes from the actual source. -/
theorem locallyRingedProjection_surjective :
    Function.Surjective (locallyRingedProjection n).base := by
  intro z
  obtain ⟨x, hx⟩ := projection_surjective n (locallyRingedOrbitHomeomorph n z)
  refine ⟨x, (locallyRingedOrbitHomeomorph n).injective ?_⟩
  exact (locallyRingedOrbitHomeomorph_projection n x).trans hx

/-- An open relation projection makes the actual locally ringed quotient map open. -/
theorem locallyRingedProjection_isOpenMap (hq : IsOpenMap tgt) :
    IsOpenMap (locallyRingedProjection n).base := by
  apply (locallyRingedOrbitHomeomorph n).comp_isOpenMap_iff.mp
  have he : locallyRingedOrbitHomeomorph n ∘
      (locallyRingedProjection n).base = projection n :=
    funext (locallyRingedOrbitHomeomorph_projection n)
  rw [he]
  exact projection_isOpenMap n hq

end FLT.Mazur.CyclicCharacteristicOrbit
