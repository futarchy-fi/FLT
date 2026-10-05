/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.DeSmitLenstra.TraceSpecialization
public import FLT.Deformations.DeSmitLenstra.UniversalMoritaData
public import FLT.Deformations.ProartinianImage

/-!
# A lift over the actual image of the universal trace ring

Specializing universal Morita reconstruction gives a representation over the
image object. Its scalar extension is strictly conjugate to the original
framed lift. The conjugator is constructed, not included as an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory IsLocalRing
namespace Deformation
open ProartinianCat MoritaReconstruction

universe u
variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (n : Type) [Fintype n] [DecidableEq n]
  (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))
  (A : ProartinianCat O) (tau : ContinuousFramedLifts O G n rho A)

omit [TotallyDisconnectedSpace G] in
/-- The image carries a lift of the original residual representation, with an actual strict
conjugator recovering the original framed lift after scalar extension. -/
theorem exists_traceImageLift
    [(residualLinearRepresentation O G n rho).IsAbsolutelyIrreducible.{u}] :
    ∃ sigma : ContinuousFramedLifts O G n rho
        (imageObject (traceSpecialization O G n rho A tau)),
      ∃ P : GL n A,
        Matrix.GeneralLinearGroup.map (toResidueField A).hom.toRingHom P = 1 ∧
        ∀ g, P * Matrix.GeneralLinearGroup.map
          (imageInclusion (traceSpecialization O G n rho A tau)).hom.toRingHom
          (sigma.val g) * P⁻¹ = tau.val g := by
  obtain ⟨e, _he, b, _hb, v, c, hc, hstrict⟩ := exists_universalMoritaData O G n rho
  obtain ⟨P, hPres, hP⟩ :=
    exists_strict_universalTraceDescendedGL_conjugator O G n rho e v b c hc hstrict
  let F := profiniteFramedLimitLiftToHom O G n rho A tau
  let f := traceSpecialization O G n rho A tau
  let q := imageProjection f
  let sigma0 : G →ₜ* GL n (universalTraceRingObject O G n rho) :=
    ⟨universalTraceDescendedGL O G n rho e b,
      universalTraceDescendedGL_continuous O G n rho e v b c hc⟩
  let sigma : G →ₜ* GL n (imageObject f) := (repnFunctor n G O).map q sigma0
  let Q := Matrix.GeneralLinearGroup.map F.hom.toRingHom P
  have hres : (toResidueField A).hom.toRingHom.comp F.hom.toRingHom =
      framedResidueRingHom O G n rho := by
    have h : F ≫ toResidueField A =
        toResidueField (profiniteFramedLimitObject O G n rho) := Subsingleton.elim _ _
    exact congrArg (fun h ↦ h.hom.toRingHom) h
  have hQ : Matrix.GeneralLinearGroup.map (toResidueField A).hom.toRingHom Q = 1 := by
    change Matrix.GeneralLinearGroup.map
      ((toResidueField A).hom.toRingHom.comp F.hom.toRingHom) P = 1
    rw [hres]
    exact hPres
  have hspecial (g : G) : Q * Matrix.GeneralLinearGroup.map
      (imageInclusion f).hom.toRingHom (sigma g) * Q⁻¹ = tau.val g := by
    have h := congrArg (Matrix.GeneralLinearGroup.map F.hom.toRingHom) (hP g)
    rw [map_mul, map_mul, map_inv] at h
    have hf := congrArg (fun t : ContinuousFramedLifts O G n rho A ↦ t.val g)
      (profiniteFramedLimitHomToLift_liftToHom O G n rho A tau)
    exact h.trans hf
  have hsigma : IsContinuousFramedLift O G n rho (imageObject f) sigma := by
    ext g i j
    have h := congrArg
      (Matrix.GeneralLinearGroup.map (toResidueField A).hom.toRingHom) (hspecial g)
    rw [map_mul, map_mul, map_inv, hQ, one_mul, inv_one, mul_one] at h
    change Matrix.GeneralLinearGroup.map
      ((toResidueField A).hom.toRingHom.comp (imageInclusion f).hom.toRingHom)
      (sigma g) = _ at h
    have hr := congrArg (fun h ↦ h.hom.toRingHom) (imageInclusion_residue f)
    change (toResidueField A).hom.toRingHom.comp (imageInclusion f).hom.toRingHom =
      (toResidueField (imageObject f)).hom.toRingHom at hr
    rw [hr] at h
    have ht := congrArg (fun t : G →* GL n (residueField (𝓞 := O)) ↦ t g) tau.property
    exact congrArg (fun t : GL n (residueField (𝓞 := O)) ↦ t i j) (h.trans ht)
  exact ⟨⟨sigma, hsigma⟩, Q, hQ, hspecial⟩

end Deformation
