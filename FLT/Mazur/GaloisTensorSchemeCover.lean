/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.GaloisTensorReduced
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Galois evaluations cover the actual coefficient-overlap scheme

Every scheme point of Spec(L tensor_K L) is covered by an original evaluation.
Reducedness upgrades this coverage to detection of maps to separated targets.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.GaloisTensorPrime

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The actual scheme point obtained by evaluating the original coefficient overlap. -/
def evaluationSpec (g : L ≃ₐ[K] L) : Spec (.of L) ⟶ Spec (.of (L ⊗[K] L)) :=
  Spec.map (CommRingCat.ofHom (evaluation g).toRingHom)

/-- The scheme evaluation has exactly the original classified prime as its image. -/
theorem evaluationSpec_point (g : L ≃ₐ[K] L) (x : Spec (.of L)) :
    evaluationSpec g x = prime g := by
  have hx : x = (⟨⊥, inferInstance⟩ : PrimeSpectrum L) := Subsingleton.elim _ _
  subst x
  rfl

/-- All original Galois evaluations, assembled into a single scheme morphism. -/
def schemeCover : (∐ fun _ : L ≃ₐ[K] L ↦ Spec (.of L)) ⟶ Spec (.of (L ⊗[K] L)) :=
  Sigma.desc evaluationSpec

variable [Algebra.IsAlgebraic K L] [IsAlgClosed L]

/-- The original evaluations cover every scheme point of the coefficient overlap. -/
instance schemeCover_surjective : Surjective (schemeCover (K := K) (L := L)) := by
  constructor
  intro x
  obtain ⟨g, hg⟩ := prime_surjective x
  refine ⟨Sigma.ι (fun _ : L ≃ₐ[K] L ↦ Spec (.of L)) g (IsLocalRing.closedPoint L), ?_⟩
  rw [← Scheme.Hom.comp_apply, schemeCover, Sigma.ι_comp_desc, evaluationSpec_point]
  exact hg

variable [CharZero K]

/-- The original evaluations detect whole morphisms to any relatively separated target. -/
theorem scheme_hom_ext {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsSeparated i]
    (f g : Spec (.of (L ⊗[K] L)) ⟶ Y) (hb : f ≫ i = g ≫ i)
    (h : ∀ a : L ≃ₐ[K] L, evaluationSpec a ≫ f = evaluationSpec a ≫ g) : f = g := by
  apply ext_of_isDominant_of_isSeparated i hb (schemeCover (K := K) (L := L))
  apply Sigma.hom_ext
  intro a
  simpa only [schemeCover, Sigma.ι_comp_desc_assoc] using h a

end FLT.Mazur.GaloisTensorPrime
