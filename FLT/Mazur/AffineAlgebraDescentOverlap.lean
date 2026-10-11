/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentReconstruction

/-!
# Algebra descent from the original tensor overlap

A tensor overlap with its geometric scalar, diagonal and cocycle equations
and with multiplicative transport constructs algebra descent data. The
reconstruction recovers the supplied overlap on every tensor, including
its second covering scalar coordinate.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.AffineAlgebraDescent
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : AffineTensorCocycle.Datum R S B)
  (h1 : D.overlap 1 = 1)
  (hm : ∀ x y, D.overlap (x * y) = D.overlap x * D.overlap y)

/-- Multiplicative overlap transport constructs the original algebra coaction. -/
def ofOverlap : Data R S B where
  coaction := AlgHom.ofLinearMap D.coaction h1 (fun b c ↦ by
    change D.overlap ((b * c) ⊗ₜ[R] (1 : S)) =
      D.overlap (b ⊗ₜ[R] (1 : S)) * D.overlap (c ⊗ₜ[R] (1 : S))
    simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one] using
      hm (b ⊗ₜ[R] (1 : S)) (c ⊗ₜ[R] (1 : S)))
  counit := D.coaction_counit
  coassoc := D.coaction_coassoc

/-- The algebra coaction is the actual original overlap evaluated on the unit factor. -/
theorem ofOverlap_coaction (b : B) :
    (ofOverlap D h1 hm).coaction b = D.overlap (b ⊗ₜ[R] (1 : S)) := rfl

/-- Reconstruction recovers the specified overlap, including arbitrary second scalar factors. -/
theorem reconstruct_overlap (t : S ⊗[R] invariants (ofOverlap D h1 hm)) (s : S) :
    D.overlap (reconstruct (ofOverlap D h1 hm) t ⊗ₜ[R] s) =
      (Algebra.lsmul R R B s).lTensor S
        ((inclusion (ofOverlap D h1 hm)).hom.lTensor S t) := by
  rw [D.overlap_tmul]
  change (Algebra.lsmul R R B s).lTensor S
    ((ofOverlap D h1 hm).coaction (reconstruct (ofOverlap D h1 hm) t)) = _
  rw [reconstruct_coaction]

/-- Flat descent reconstructs the entire original multiplicative overlap algebra. -/
def overlapReconstruction [Module.Flat R S] :
    S ⊗[R] invariants (ofOverlap D h1 hm) ≃ₐ[S] B :=
  reconstruction (ofOverlap D h1 hm)

end FLT.Mazur.AffineAlgebraDescent
