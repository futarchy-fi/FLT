/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCharacterAdicElements

/-!
# Effective coordinate homomorphisms into a finite character algebra

Compatible finite-stage ring maps reconstruct a unique ring map into the
original character algebra over the complete base. All ring equations follow
from the prescribed reductions and coefficientwise separatedness.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteCharacterAdicHom

open FiniteCharacterAdicElements

variable {R G C : Type} [CommRing R] [AddCommMonoid G] [Finite G] [CommRing C]
  (I : Ideal R) [IsAdicComplete I R]
  (f : ∀ m : ℕ, C →+* AddMonoidAlgebra (R ⧸ I ^ (m + 1)) G)
  (hf : ∀ m, (restriction I m).comp (f (m + 1)) = f m)

/-- The reconstructed coordinate map with values in the original full character algebra. -/
def liftHom : C →+* AddMonoidAlgebra R G where
  toFun c := lift I (fun m => f m c) (fun m => RingHom.congr_fun (hf m) c)
  map_one' := by
    apply reduction_ext I
    intro m
    rw [reduction_lift, map_one, map_one]
  map_mul' c d := by
    apply reduction_ext I
    intro m
    rw [map_mul, reduction_lift, reduction_lift, reduction_lift, map_mul]
  map_zero' := by
    apply reduction_ext I
    intro m
    rw [reduction_lift, map_zero, map_zero]
  map_add' c d := by
    apply reduction_ext I
    intro m
    rw [map_add, reduction_lift, reduction_lift, reduction_lift, map_add]

/-- Every full finite-stage coordinate homomorphism is retained exactly. -/
theorem reduction_liftHom (m : ℕ) : (reduction I m).comp (liftHom I f hf) = f m := by
  apply RingHom.ext
  intro c
  exact reduction_lift I _ _ m

/-- The actual complete coordinate homomorphism is uniquely specified by its reductions. -/
theorem liftHom_unique (q : C →+* AddMonoidAlgebra R G)
    (hq : ∀ m, (reduction I m).comp q = f m) : q = liftHom I f hf := by
  apply RingHom.ext
  intro c
  apply reduction_ext I
  intro m
  exact (RingHom.congr_fun (hq m) c).trans
    (RingHom.congr_fun (reduction_liftHom I f hf m) c).symm

end FLT.Mazur.FiniteCharacterAdicHom
