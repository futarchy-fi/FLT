/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonRootsCoefficientNaturality
public import FLT.Mazur.OneGonAdicCharacterCoefficientTower

/-!
# The coefficient comparison retains the specified initial roots

The actual boundary-root map, including its corrected torus coordinate and
parameter equality transport, is preserved by every map of coefficient pairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicCharacterTower
open OneGonSmoothing WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Named smooth coefficient maps retain equality transport at both ends. -/
theorem smoothCoefficientMapTo_transport {R S : Type} [CommRing R] [CommRing S]
    {W W' : WeierstrassCurve R} {V V' : WeierstrassCurve S}
    (f : R →+* S) (hW : W = W') (hV : V = V')
    (h : V = W.map f) (h' : V' = W'.map f) :
    eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme) hV) ≫
      smoothCoefficientMapTo W' V' f h' =
        smoothCoefficientMapTo W V f h ≫
          eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme) hW) := by
  subst W'
  subst V'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The initial group transport is the same literal smooth-scheme transport. -/
theorem initialBoundaryIso_hom_left {R : Type} [CommRing R]
    (I : Ideal R) (t : R) (ht : t ∈ I) :
    (initialBoundaryIso I t ht).hom.hom.hom.hom.left =
      eqToHom (congrArg (fun U => (integralSmoothOpen U).toScheme)
        (congrArg equation (parameter_zero I t ht).symm)) :=
  equationGroupTransport_inv_left (congrArg equation (parameter_zero I t ht))

/-- The native roots square with a specified ring map, before taking any quotients. -/
@[reassoc] theorem boundaryRootsHom_ring_projection {A B : Type}
    [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) [NeZero n]
    (h : equation (0 : B) = (equation (0 : A)).map f) :
    (boundaryRootsHom (R := B) n).hom.hom.hom.left ≫
      smoothCoefficientMapTo _ _ f h =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (ZMod n) f)) ≫
          (boundaryRootsHom (R := A) n).hom.hom.hom.left := by
  let _ := f.toAlgebra
  exact ArithmeticOneGonRootsCoefficientNaturality.nativeRoots_projection A B n

end FLT.Mazur.OneGonAdicCharacterTower
