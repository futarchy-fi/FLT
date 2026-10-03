/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtensionExists

/-!
# Generic Hopf maps and geometric point maps

The two constructions are inverse. This lets duality operate on actual generic
coordinate maps while retaining the specified Galois modules.
-/

@[expose] public noncomputable section
open scoped TensorProduct

universe u
namespace ThreeAdicPlan
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [PerfectField K]

/-- A generic Hopf map acts on the specified geometric points by precomposition. -/
def GenericGaloisHom.ofBialgHom {X Y : FF R K}
    (f : K ⊗[R] Y.CoordinateRing →ₐc[K] K ⊗[R] X.CoordinateRing) :
    GenericGaloisHom X Y :=
  Y.points.comp ((BialgHom.precompPoints f).comp X.inversePoints)

omit [PerfectField K] in
/-- On actual geometric points the constructed map is precomposition. -/
@[simp] theorem GenericGaloisHom.ofBialgHom_points {X Y : FF R K}
    (f : K ⊗[R] Y.CoordinateRing →ₐc[K] K ⊗[R] X.CoordinateRing)
    (p : Additive (K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K)) :
    ofBialgHom f (X.points p) = Y.points (BialgHom.precompPoints f p) := by
  change Y.points (BialgHom.precompPoints f (X.pointsEquiv.symm (X.pointsEquiv p))) = _
  rw [X.pointsEquiv.symm_apply_apply]

/-- Returning to generic coordinates recovers the original Hopf map. -/
@[simp] theorem GenericGaloisHom.toBialgHom_ofBialgHom {X Y : FF R K}
    (f : K ⊗[R] Y.CoordinateRing →ₐc[K] K ⊗[R] X.CoordinateRing) :
    (ofBialgHom f).toBialgHom = f := by
  ext a
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing)).injective
  ext p
  have h := (ofBialgHom f).toBialgHom_points (Additive.ofMul p)
  rw [ofBialgHom_points] at h
  exact AlgHom.congr_fun (congrArg Additive.toMul (Y.points_bijective.1 h)) a

/-- Returning to points recovers the original Galois map. -/
@[simp] theorem GenericGaloisHom.ofBialgHom_toBialgHom {X Y : FF R K}
    (f : GenericGaloisHom X Y) : ofBialgHom f.toBialgHom = f := by
  ext x
  obtain ⟨p, rfl⟩ := X.points_bijective.2 x
  rw [ofBialgHom_points, toBialgHom_points]

/-- A generic Galois map is determined by its Hopf map. -/
theorem GenericGaloisHom.toBialgHom_inj {X Y : FF R K} :
    Function.Injective (toBialgHom (X := X) (Y := Y)) := by
  intro f g h
  simpa using congrArg (ofBialgHom (X := X) (Y := Y)) h

omit [PerfectField K] in
/-- A Hopf equivalence induces a bijection of the specified generic point groups. -/
theorem GenericGaloisHom.ofBialgHom_bijective {X Y : FF R K}
    (e : K ⊗[R] Y.CoordinateRing ≃ₐc[K] K ⊗[R] X.CoordinateRing) :
    Function.Bijective (ofBialgHom e.toBialgHom) := by
  have inv (X Y : FF R K)
      (e : K ⊗[R] Y.CoordinateRing ≃ₐc[K] K ⊗[R] X.CoordinateRing) (x : X.Points) :
      ofBialgHom e.symm.toBialgHom (ofBialgHom e.toBialgHom x) = x := by
    obtain ⟨p, rfl⟩ := X.points_bijective.2 x
    rw [ofBialgHom_points, ofBialgHom_points]
    congr 1
    apply Additive.toMul.injective
    apply AlgHom.ext
    intro a
    exact congrArg p.toMul (e.apply_symm_apply a)
  exact ⟨Function.LeftInverse.injective (inv X Y e),
    Function.RightInverse.surjective (inv Y X e.symm)⟩

end ThreeAdicPlan
