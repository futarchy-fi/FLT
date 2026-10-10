/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineTransport
public import FLT.Mazur.AffineFreeSheafCoordinatePullback
public import FLT.Mazur.NormalizedSectionLineLinearBaseChange

/-!
# Section-line transport under genuine affine sheaf pullback

Recovered finite free section coordinates commute with every affine test map.
Consequently extending the actual transported line or first pulling back the
original free-sheaf isomorphism gives exactly the same section submodule.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeContragredient
open ProjectiveSpace
variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι κ : Type u} [Finite ι] [Finite κ]

/-- Ordinary vector coordinates inherit the genuine finite free coefficient square. -/
lemma functionCoordinates_coefficient (φ : R →+* S)
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ v, changeCoefficients φ (e v) = d (changeCoefficients φ v)) (v : ι → R) :
    (fun k ↦ φ (functionCoordinates e v k)) = functionCoordinates d (fun k ↦ φ (v k)) := by
  let w := (Finsupp.linearEquivFunOnFinite R R ι).symm v
  have hw : (fun k ↦ w k) = v :=
    (Finsupp.linearEquivFunOnFinite R R ι).apply_symm_apply _
  have hs : (Finsupp.linearEquivFunOnFinite S S ι).symm (fun k ↦ φ (v k)) =
      changeCoefficients φ w := by
    ext k
    change φ (v k) = φ (w k)
    rw [congrFun hw k]
  funext k
  change φ (e w k) = d ((Finsupp.linearEquivFunOnFinite S S ι).symm (fun k ↦ φ (v k))) k
  rw [hs]
  exact DFunLike.congr_fun (h w) k

end FiniteFreeContragredient

namespace AffineFreeSheafCoordinates
open NormalizedSectionLine FiniteFreeContragredient
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
variable {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : (SheafOfModules.free ι : Y.Modules) ≅ SheafOfModules.free κ)

/-- The original free-sheaf pullback supplies the vector coefficient square without extra data. -/
lemma vectorCoordinates_pullback (v : ι → Γ(Y, ⊤)) :
    (fun k ↦ f.appTop.hom (functionCoordinates (coordinates Y e) v k)) =
      functionCoordinates (coordinates X (pullbackFreeIso f e)) (fun k ↦ f.appTop.hom (v k)) :=
  functionCoordinates_coefficient f.appTop.hom _ _ (coordinates_pullback f e) v

/-- Pulling back the genuine sheaf coordinate change carries the selected coordinate unit. -/
lemma sectionLineTransport_pullback_unit (i : ι) (j : κ) (L : Chart Γ(Y, ⊤) ι i)
    (a : Γ(Y, ⊤)ˣ)
    (ha : functionCoordinates (coordinates Y e) (generator Γ(Y, ⊤) ι i L) j = a) :
    functionCoordinates (coordinates X (pullbackFreeIso f e))
        (generator Γ(X, ⊤) ι i (baseChange f.appTop.hom i L)) j =
      (Units.map f.appTop.hom.toMonoidHom a : Γ(X, ⊤)) :=
  linearTransport_baseChange_unit _ _ _ (vectorCoordinates_pullback f e) i j L a ha

/-- Actual transported submodules commute with arbitrary affine sheaf pullback. -/
lemma sectionLineTransport_pullback (i : ι) (j : κ) (L : Chart Γ(Y, ⊤) ι i)
    (a : Γ(Y, ⊤)ˣ)
    (ha : functionCoordinates (coordinates Y e) (generator Γ(Y, ⊤) ι i L) j = a) :
    baseChange f.appTop.hom j (linearTransport (functionCoordinates (coordinates Y e))
        i j L a ha) =
      linearTransport (functionCoordinates (coordinates X (pullbackFreeIso f e)))
        i j (baseChange f.appTop.hom i L) (Units.map f.appTop.hom.toMonoidHom a)
        (sectionLineTransport_pullback_unit f e i j L a ha) :=
  linearTransport_baseChange _ _ _ (vectorCoordinates_pullback f e) i j L a ha

end AffineFreeSheafCoordinates
end FLT.Mazur
