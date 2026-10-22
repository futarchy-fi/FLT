/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFrameScalarNorm
public import FLT.Mazur.FiniteFreeSplitComparisonEquation

/-!
# Full original boundary arrows from a finite free original scalar source

A basis over the unchanged original invariant ring constructs the scalar
norm. A whole-source decomposition matching the actual frame constructs
its splitting. No norm equation, mixed-product vanishing, or Noetherian
condition on the affine test is supplied as an additional hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators
open Module TensorProduct
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "P" => pullback.snd p J.subschemeι
local notation "Q" => InvariantIdealRelation.snd J p q hJ
local notation "E" => Over.mk P
local notation "c" => originalBoundaryComparison p q J hJ
local instance finiteFreeScalarBoundaryOver_separated : IsSeparated (E).hom :=
  inferInstanceAs (IsSeparated P)
local instance finiteFreeScalarBoundaryOver_etale : Etale (E).hom := inferInstanceAs (Etale P)
local instance finiteFreeScalarBoundaryOver_compact : QuasiCompact (E).hom :=
  inferInstanceAs (QuasiCompact P)
local instance finiteFreeScalarOriginalOver_separated : IsSeparated (Over.mk p).hom :=
  ‹IsSeparated p›
local instance finiteFreeScalarOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteFreeScalarOriginalOver_compact : QuasiCompact (Over.mk p).hom :=
  ‹QuasiCompact p›
variable (t : B ⟶ pullback
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤)))
    (scalarMorphism (algebraMap (invariants p.appTop.hom q.appTop.hom) Γ(J.subscheme, ⊤))))
  (n : ℕ)
local notation "x" => t ≫ pullback.fst f f
local notation "y" => t ≫ pullback.snd f f
variable (a : Over.mk (t ≫ pullback.fst _ _) ⟶
    distinctScheme (Over.mk (pullback.snd p J.subschemeι)) (Fin n))
  (ht : Set.range (t ≫ pullback.fst _ _ ≫ J.subschemeι) ⊆ exactRank (Over.mk p) n)

variable [IsAffine A] [IsAffine B] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteFreeScalarBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
local instance finiteFreeScalarOriginal_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
attribute [local irreducible] scalarMorphism
local notation "s" k:max => testSection E (Fin n) a k

local notation "l" k:max => (s k ≫ pullback.fst P x ≫ Q).appTop.hom
local notation "r" => (y).appTop.hom

local notation "σ" => algebraMap R Γ(J.subscheme, ⊤)

include ht e

/-- A complete original scalar algebra frame constructs the unique full boundary arrow. -/
theorem originalBoundary_frame_lift_of_finiteFree_source {d : ℕ}
    (basis : Basis (Fin d) R Γ(J.subscheme, ⊤)) :
    let _ : Algebra R Γ(B, ⊤) := ((x).appTop.hom.comp σ).toAlgebra
    ∀ (frame : (Γ(B, ⊤) ⊗[R] Γ(J.subscheme, ⊤)) ≃ₐ[Γ(B, ⊤)] (Fin n → Γ(B, ⊤)))
    (_hframe : ∀ k z, frame (1 ⊗ₜ[R] z) k = (l k) z),
    ∃! u : B ⟶ pullback p J.subschemeι, u ≫ c = t := by
  let _ : Algebra R Γ(B, ⊤) := ((x).appTop.hom.comp σ).toAlgebra
  dsimp only
  intro frame hframe
  let yAlg : Γ(J.subscheme, ⊤) →ₐ[R] Γ(B, ⊤) :=
    { r with
      commutes' z := by
        exact (DFunLike.congr_fun (originalBoundary_frame_scalar_maps_eq J t) z).symm }
  apply (originalBoundary_frame_lift_iff_products J hJ t n a ht e).mpr
  intro z
  have hz := FiniteFreeSplitComparisonEquation.mixed_products_eq_zero basis frame yAlg z
  change (∏ k, (frame (1 ⊗ₜ[R] z k) k - r (z k))) = 0 at hz
  simp_rw [hframe] at hz
  exact hz

/-- A complete scalar frame modulo a correction ideal controls the entire comparison kernel. -/
theorem originalBoundary_frame_kernel_le_of_finiteFree_source {d : ℕ}
    (basis : Basis (Fin d) R Γ(J.subscheme, ⊤)) (K : Ideal Γ(B, ⊤)) :
    let _ : Algebra R Γ(B, ⊤) := ((x).appTop.hom.comp σ).toAlgebra
    ∀ (frame : ((Γ(B, ⊤) ⧸ K) ⊗[R] Γ(J.subscheme, ⊤)) ≃ₐ[Γ(B, ⊤) ⧸ K]
      (Fin n → Γ(B, ⊤) ⧸ K))
    (_hframe : ∀ k z, frame (1 ⊗ₜ[R] z) k = Ideal.Quotient.mk K ((l k) z)),
    RingHom.ker (pullback.snd c t).appTop.hom ≤ K := by
  let _ : Algebra R Γ(B, ⊤) := ((x).appTop.hom.comp σ).toAlgebra
  dsimp only
  intro frame hframe
  let yAlg : Γ(J.subscheme, ⊤) →ₐ[R] Γ(B, ⊤) ⧸ K :=
    { (Ideal.Quotient.mk K).comp r with
      commutes' z := by
        exact congrArg (Ideal.Quotient.mk K)
          (DFunLike.congr_fun (originalBoundary_frame_scalar_maps_eq J t) z).symm }
  apply (originalBoundary_frame_kernel_le_iff_products J hJ t n a ht e K).mpr
  intro z
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have hz := FiniteFreeSplitComparisonEquation.mixed_products_eq_zero basis frame yAlg z
  change (∏ k, (frame (1 ⊗ₜ[R] z k) k - Ideal.Quotient.mk K (r (z k)))) = 0 at hz
  simp_rw [hframe] at hz
  change Ideal.Quotient.mk K (∏ k, ((l k) (z k) - r (z k))) = 0
  simpa only [map_prod, map_sub] using hz

end FLT.Mazur.EquivalenceRelationOrderedFrames
