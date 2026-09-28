/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudExtensionExists

/-!
# Flat closures of generic torsion subgroups

The generic subgroup killed by an integer has a finite flat schematic closure in
any chosen model. Its inclusion is an integral closed immersion. Multiplication
by `p` on the generic fibre has kernel killed by `p` and image killed by `p^n`
when the ambient group is killed by `p^(n+1)`.

These statements concern the flat closure of the generic kernel. They do not assert
that the entire scheme-theoretic kernel of multiplication is flat, nor establish
the exactness on integral models needed to deduce general Raynaud rigidity by induction.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- Choose a model from the finite-flat predicate while retaining the prescribed point type. -/
@[implicit_reducible]
def FF.ofIsFiniteFlat (M : Type u) [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) M]
    (h : GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) M) : FF R K := by
  choose A hA hH hF hE f hf using h
  exact { CoordinateRing := A
          commRing := hA
          hopfAlgebra := hH
          finiteFlat := hF
          genericEtale := hE
          Points := M
          points := f
          points_bijective := hf }

/-- The generic points annihilated by `n`, as an additive subgroup. -/
abbrev FF.torsionPoints (X : FF R K) (n : ℕ) :=
  ↥(nsmulAddMonoidHom (α := X.Points) n).ker

/-- Galois acts on the subgroup killed by an integer. -/
instance FF.torsionPointsAction (X : FF R K) (n : ℕ) :
    DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (X.torsionPoints n) where
  smul σ x := ⟨σ • x.val, by
    change n • (σ • x.val) = 0
    rw [← smul_comm, show n • x.val = 0 from x.property, smul_zero]⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ x.val)
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ x y := Subtype.ext (smul_add σ x.val y.val)

/-- The equivariant inclusion of generic torsion into the ambient point group. -/
def FF.torsionInclusion (X : FF R K) (n : ℕ) :
    X.torsionPoints n →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] X.Points where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The image of multiplication by `n` on the generic point group. -/
abbrev FF.multiplePoints (X : FF R K) (n : ℕ) :=
  ↥(nsmulAddMonoidHom (α := X.Points) n).range

/-- Galois acts on the image of multiplication by an integer. -/
instance FF.multiplePointsAction (X : FF R K) (n : ℕ) :
    DistribMulAction (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (X.multiplePoints n) where
  smul σ x := ⟨σ • x.val, by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨σ • y, ?_⟩
    change n • (σ • y) = σ • x.val
    rw [← smul_comm]
    exact congrArg (σ • ·) hy⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ x.val)
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ x y := Subtype.ext (smul_add σ x.val y.val)

/-- Multiplication by `n`, with codomain restricted to its image. -/
def FF.multiplyGeneric (X : FF R K) (n : ℕ) :
    X.Points →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] X.multiplePoints n where
  toFun x := ⟨n • x, ⟨x, rfl⟩⟩
  map_zero' := Subtype.ext (nsmul_zero n)
  map_add' x y := Subtype.ext (nsmul_add x y n)
  map_smul' σ x := Subtype.ext (smul_comm n σ x)

/-- Multiplication onto its image is surjective. -/
theorem FF.multiplyGeneric_surjective (X : FF R K) (n : ℕ) :
    Function.Surjective (X.multiplyGeneric n) := by
  intro x
  obtain ⟨y, hy⟩ := x.property
  exact ⟨y, Subtype.ext hy⟩

variable [IsDedekindDomain R] [IsFractionRing R K] [PerfectField K]

/-- The generic torsion subgroup has a finite-flat model over a Dedekind base. -/
theorem FF.torsionPoints_isFiniteFlat (X : FF R K) (n : ℕ) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (X.torsionPoints n) :=
  X.isFiniteFlat.subobject R K (AlgebraicClosure K) X.Points
    (X.torsionInclusion n) Subtype.val_injective

/-- An auxiliary finite-flat model of the generic torsion point group. -/
@[implicit_reducible]
def FF.torsionAuxModel (X : FF R K) (n : ℕ) : FF R K :=
  FF.ofIsFiniteFlat (X.torsionPoints n) (X.torsionPoints_isFiniteFlat n)

/-- The flat closure of generic `n`-torsion in the given model. -/
@[implicit_reducible]
def FF.torsionClosure (X : FF R K) (n : ℕ) : FF R K :=
  (show GenericGaloisHom (X.torsionAuxModel n) X from X.torsionInclusion n).closure
    Subtype.val_injective

/-- The closed immersion of the flat torsion closure into the original model. -/
def FF.torsionClosureInclusion (X : FF R K) (n : ℕ) : ModelHom (X.torsionClosure n) X :=
  (show GenericGaloisHom (X.torsionAuxModel n) X from X.torsionInclusion n).closureInclusion
    Subtype.val_injective

/-- The torsion closure inclusion induces the usual inclusion on generic points. -/
@[simp] theorem FF.genericHom_torsionClosureInclusion (X : FF R K) (n : ℕ)
    (x : (X.torsionClosure n).Points) : genericHom (X.torsionClosureInclusion n) x = x.val :=
  GenericGaloisHom.genericHom_closureInclusion
    (X := X.torsionAuxModel n) (Y := X) (X.torsionInclusion n) Subtype.val_injective x

/-- On coordinate rings, the flat torsion closure inclusion is surjective. -/
theorem FF.torsionClosureInclusion_surjective (X : FF R K) (n : ℕ) :
    Function.Surjective (X.torsionClosureInclusion n) :=
  Ideal.Quotient.mk_surjective

/-- The flat closure of generic `n`-torsion is killed by `n` on generic points. -/
theorem FF.torsionClosure_killed (X : FF R K) (n : ℕ)
    (x : (X.torsionClosure n).Points) : n • x = 0 := by
  apply Subtype.ext
  exact x.property

/-- In particular, the `p`-torsion closure is killed by a power of `p`. -/
theorem FF.torsionClosure_killedByPowerOf (X : FF R K) (p : ℕ) :
    KilledByPowerOf p (X.torsionClosure p) :=
  ⟨1, by simpa using X.torsionClosure_killed p⟩

/-- The image of generic multiplication has a finite-flat model by the quotient theorem. -/
theorem FF.multiplePoints_isFiniteFlat (X : FF R K) (n : ℕ) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (X.multiplePoints n) :=
  X.isFiniteFlat.quotient R K (AlgebraicClosure K) X.Points
    (X.multiplyGeneric n) (X.multiplyGeneric_surjective n)

/-- A finite-flat model of the image of generic multiplication. -/
@[implicit_reducible]
def FF.multipleModel (X : FF R K) (n : ℕ) : FF R K :=
  FF.ofIsFiniteFlat (X.multiplePoints n) (X.multiplePoints_isFiniteFlat n)

/-- On generic points, the flat torsion closure is exactly the kernel of multiplication. -/
theorem FF.multiplyGeneric_eq_zero_iff (X : FF R K) (n : ℕ) (x : X.Points) :
    X.multiplyGeneric n x = 0 ↔
      ∃ t : (X.torsionClosure n).Points, genericHom (X.torsionClosureInclusion n) t = x := by
  constructor
  · intro hx
    have hx' : n • x = 0 := congrArg Subtype.val hx
    exact ⟨⟨x, hx'⟩, X.genericHom_torsionClosureInclusion n _⟩
  · rintro ⟨t, rfl⟩
    apply Subtype.ext
    change n • genericHom (X.torsionClosureInclusion n) t = 0
    rw [X.genericHom_torsionClosureInclusion]
    exact t.property

/-- Passing to the generic image of multiplication by `p` lowers an annihilating exponent. -/
theorem FF.multipleModel_killed (X : FF R K) (p n : ℕ)
    (hX : ∀ x : X.Points, p ^ (n + 1) • x = 0) (y : (X.multipleModel p).Points) :
    p ^ n • y = 0 := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := y.property
  change p ^ n • y.val = 0
  rw [← hx]
  change p ^ n • (p • x) = 0
  rw [← mul_nsmul, ← pow_succ']
  exact hX x

/-- The finite-flat image model is killed by a power of `p`, with the smaller exponent. -/
theorem FF.multipleModel_killedByPowerOf (X : FF R K) (p n : ℕ)
    (hX : ∀ x : X.Points, p ^ (n + 1) • x = 0) :
    KilledByPowerOf p (X.multipleModel p) :=
  ⟨n, X.multipleModel_killed p n hX⟩

end ThreeAdicPlan
