/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.KnownIn1980s.EllipticCurves.Flat

/-!
# Finite-flat models for the torsion representation

The geometric flatness theorem uses convolution points with a `WithConv` wrapper.
The finite-flat Galois-module interface uses convolution directly on algebra maps.
We compare these presentations and transport flatness to the actual torsion action.
The geometric input is the existing `torsion_flat_of_good_reduction` admission.
-/

@[expose] public section

open scoped TensorProduct WeierstrassCurve.Affine
universe u
variable {K L H : Type u} [Field K] [Field L] [Algebra K L] [CommRing H] [Bialgebra K H]
namespace GaloisModule

/-- The two convolution presentations of geometric points have the same additive law. -/
noncomputable def convolutionPointsEquiv :
    Additive (H →ₐ[K] L) ≃+ Additive (WithConv (H →ₐ[K] L)) where
  toFun f := Additive.ofMul (WithConv.toConv f.toMul)
  invFun f := Additive.ofMul f.toMul.ofConv
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' f g := by
    apply congrArg Additive.ofMul
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    change Algebra.TensorProduct.lift f.toMul g.toMul (fun _ _ ↦ .all _ _) (Coalgebra.comul x) =
      (Algebra.TensorProduct.lmul' K).comp
        (Algebra.TensorProduct.map f.toMul g.toMul) (Coalgebra.comul x)
    induction Coalgebra.comul (R := K) x with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rfl

end GaloisModule

namespace WeierstrassCurve

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
  [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
  (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]
  (n : ℕ) (hn : 0 < n)

set_option backward.isDefEq.respectTransparency false in
/-- Good reduction supplies a finite-flat model for the continuous torsion representation.
This uses the existing geometric admission `torsion_flat_of_good_reduction`. -/
theorem isFiniteFlat_torsion_of_goodReduction :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (E.galoisRep n hn).Space := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨H, _, _, _, _, _, f, hf⟩ := E.torsion_flat_of_good_reduction R K n (AlgebraicClosure K)
  let e := (GaloisModule.convolutionPointsEquiv
    (K := K) (L := AlgebraicClosure K) (H := K ⊗[R] H)).trans f
  let g : Additive (K ⊗[R] H →ₐ[K] AlgebraicClosure K) →+[Field.absoluteGaloisGroup K]
      (E.galoisRep n hn).Space :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro σ φ
        apply Subtype.ext
        exact hf σ φ.toMul }
  exact (GaloisModule.isFiniteFlat_iff R K (AlgebraicClosure K) _).mpr
    ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, g, e.bijective⟩

end WeierstrassCurve

namespace GaloisRep

universe v

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CharZero K]
  {k : Type v} [CommRing k] [TopologicalSpace k]
  {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- A surjective equivariant linear map carries a finite-flat representation to
a finite-flat quotient, using schematic closure in the Hopf-algebra model. -/
theorem isFiniteFlat_of_surjective (ρ : GaloisRep K k V) (χ : GaloisRep K k W)
    (hρ : GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) ρ.Space)
    (q : V →ₗ[k] W) (hq : Function.Surjective q)
    (heq : ∀ g x, q (ρ g x) = χ g (q x)) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) χ.Space := by
  let f : ρ.Space →+[Field.absoluteGaloisGroup K] χ.Space :=
    { q.toAddMonoidHom with map_smul' := heq }
  exact hρ.quotient R K (AlgebraicClosure K) ρ.Space f hq

end GaloisRep
