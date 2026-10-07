/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberProductPairTransport
public import FLT.Mazur.SchemeOverlapNormalizationNaturality

/-!
# Compatible maps on categorical and tensor-spectrum overlaps

Tensor-spectrum normalization preserves the actual compatibility square. This
statement is independent of quasi-coherence and effective descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricOverlap
open AffineOverlapTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable {M N : (Spec (.of S)).Modules}

/-- Compatible categorical overlaps induce compatible affine tensor-chart overlaps. -/
theorem fromFiberProduct_compatible (e : FiberProductOverlap R S M)
    (e' : FiberProductOverlap R S N) (f : M ⟶ N)
    (hf : e.hom ≫ (pullback (Limits.pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))).map f =
      (pullback (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))))).map f ≫ e'.hom) :
    (fromFiberProduct R S M e).hom ≫
        (pullback (Spec.map (CommRingCat.ofHom (right R S)))).map f =
      (pullback (Spec.map (CommRingCat.ofHom (left R S)))).map f ≫
        (fromFiberProduct R S N e').hom := by
  rw [fromFiberProduct_eq_normalize, fromFiberProduct_eq_normalize]
  exact SchemeOverlapDiagonalChart.normalize_compatible
    (Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) (pullbackSpecIso R S S).inv
    (Spec.map (CommRingCat.ofHom (left R S)))
    (Spec.map (CommRingCat.ofHom (right R S)))
    (pullbackSpecIso_inv_fst R S S) (pullbackSpecIso_inv_snd R S S)
    (M := M) (N := N) e e' f hf

end FLT.Mazur.AffineGeometricOverlap
