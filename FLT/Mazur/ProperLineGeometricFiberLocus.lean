/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCohomologyFieldVanishing
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Intrinsic proper line cohomology loci and cartesian base change

Use the actual scheme-theoretic residue fibers, independently of affine
coordinates. Field extension preserves and detects their cohomology
vanishing, so the locus commutes with every cartesian base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve

variable {P X T S : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ T}
  {f : X ⟶ S} [IsProper f] {g : T ⟶ S}

/-- A cartesian base change preserves and detects each actual fiber cohomology vanishing. -/
theorem properLine_fiber_vanishing_iff (h : IsPullback p q f g)
    (L : X.Modules) (hL : LocallyFreeRankOne L) (t : T) (n : ℕ) :
    Subsingleton (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) n) ↔
      Subsingleton (ModuleH ((pullback (f.fiberι (g t))).obj L) n) := by
  let k : q.fiber t ⟶ f.fiber (g t) :=
    Limits.pullback.map _ _ _ _ p (Spec.map (g.residueFieldMap t)) g h.w.symm (by simp)
  have hk : IsPullback k (q.fiberToSpecResidueField t)
      (f.fiberToSpecResidueField (g t)) (Spec.map (g.residueFieldMap t)) :=
    isPullback_fiberToSpecResidueField_of_isPullback h t
  have he : k ≫ f.fiberι (g t) = q.fiberι t ≫ p := by
    simp [k, Scheme.Hom.fiberι]
  let e := (pullbackComp (q.fiberι t) p).app L ≪≫
    (pullbackCongr he.symm).app L ≪≫ ((pullbackComp k (f.fiberι (g t))).app L).symm
  let _ : IsProper (f.fiberToSpecResidueField (g t)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd f _))
  have hv := proper_line_cohomology_field_vanishing_iff hk (hL.pullback (f.fiberι (g t))) n
  change Subsingleton (ModuleH _ n) ↔ Subsingleton (ModuleH _ n) at hv
  exact (Equiv.subsingleton_congr (moduleHIsoOfIso e n).toEquiv).trans hv

/-- The intrinsic positive-cohomology vanishing locus of a line family. -/
def properLineGeometricAcyclicLocus (f : X ⟶ S) (L : X.Modules) : Set S :=
  {s | ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1))}

/-- Cartesian base change pulls back the entire positive-cohomology locus exactly. -/
theorem properLineGeometricAcyclicLocus_baseChange (h : IsPullback p q f g)
    (L : X.Modules) (hL : LocallyFreeRankOne L) :
    properLineGeometricAcyclicLocus q ((pullback p).obj L) =
      g ⁻¹' properLineGeometricAcyclicLocus f L := by
  ext t
  exact forall_congr' fun n ↦ properLine_fiber_vanishing_iff h L hL t (n + 1)

/-- Changing the coefficient line by an isomorphism leaves the intrinsic locus unchanged. -/
theorem properLineGeometricAcyclicLocus_iso (f : X ⟶ S) {L N : X.Modules}
    (e : L ≅ N) : properLineGeometricAcyclicLocus f L =
      properLineGeometricAcyclicLocus f N := by
  ext s
  exact forall_congr' fun n ↦ Equiv.subsingleton_congr
    (moduleHIsoOfIso ((pullback (f.fiberι s)).mapIso e) (n + 1)).toEquiv

/-- Open restriction has exactly the inverse-image locus, including detection on overlaps. -/
theorem properLineGeometricAcyclicLocus_restrict (f : X ⟶ S) [IsProper f]
    (L : X.Modules) (hL : LocallyFreeRankOne L) (U : S.Opens) :
    properLineGeometricAcyclicLocus (f ∣_ U) ((pullback (f ⁻¹ᵁ U).ι).obj L) =
      U.ι ⁻¹' properLineGeometricAcyclicLocus f L :=
  properLineGeometricAcyclicLocus_baseChange (isPullback_morphismRestrict f U).flip L hL

end FLT.Mazur.FCurve
