/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.CompatibleIdempotent
public import FLT.Deformations.DeSmitLenstra.UniversalLift

/-!
# Morita reconstruction for trace descent

An idempotent in the descended image algebra cuts out the principal module `Ae`.  Left
multiplication gives the Morita map from the image algebra to the endomorphisms of `Ae`; after a
choice of rank-`n` basis, the group action on `Ae` is a `GLₙ`-valued representation over the
smaller coefficient ring.
-/

@[expose] public section

universe u

namespace Representation

namespace MoritaReconstruction

noncomputable section

variable {S R G : Type u} {n : Type} [CommRing S] [CommRing R] [Algebra S R]
variable [Group G] [Fintype n] [DecidableEq n]

/-- Regard a `GLₙ`-valued homomorphism as a linear representation. -/
def linearRepresentationOfGL (rho : G →* GL n R) : Representation R G (n → R) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp ((Units.coeHom _).comp rho)

@[simp]
lemma representationMatrix_linearRepresentationOfGL (rho : G →* GL n R) (g : G) :
    representationMatrix (linearRepresentationOfGL rho) g = (rho g : Matrix n n R) := by
  simp [representationMatrix, linearRepresentationOfGL]

/-- The element of the image algebra represented by a group element. -/
def imageElement (rho : Representation R G (n → R)) (g : G) :
    imageAlgebra (S := S) rho :=
  ⟨representationMatrix rho g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

/-- The representation, regarded as a monoid homomorphism into its image algebra. -/
def imageMonoidHom (rho : Representation R G (n → R)) :
    G →* imageAlgebra (S := S) rho where
  toFun := imageElement rho
  map_one' := by
    apply Subtype.ext
    exact map_one (representationMatrixHom rho)
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (representationMatrixHom rho) g h

/-- The principal left module `Ae`, realized as the range of right multiplication by `e`. -/
abbrev principalModule (A : Type u) [Ring A] [Algebra S A] (e : A) :=
  LinearMap.range (LinearMap.mulRight S e)

/-- Left multiplication by `a` on the principal module `Ae`. -/
def principalLeftMul {A : Type u} [Ring A] [Algebra S A]
    (e a : A) : Module.End S (principalModule (S := S) A e) where
  toFun x := ⟨a * x.1, by
    obtain ⟨y, hy⟩ := x.2
    refine ⟨a * y, ?_⟩
    change (a * y) * e = a * x.1
    change y * e = x.1 at hy
    rw [← hy, mul_assoc]⟩
  map_add' x y := by ext; exact mul_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    change a * (r • x.1) = r • (a * x.1)
    exact Algebra.mul_smul_comm r a x.1

@[simp]
lemma principalLeftMul_apply {A : Type u} [Ring A] [Algebra S A]
    (e a : A) (x : principalModule (S := S) A e) :
    (principalLeftMul e a x : A) = a * x.1 := rfl

/-- The Morita left-action map `A → End_S(Ae)`. -/
def principalLeftAction {A : Type u} [Ring A] [Algebra S A] (e : A) :
    A →ₐ[S] Module.End S (principalModule (S := S) A e) where
  toFun := principalLeftMul e
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [Module.End.mul_apply, mul_assoc]
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp [add_mul]
  commutes' r := by ext x; simp [Algebra.smul_def]

@[simp]
lemma principalLeftAction_apply {A : Type u} [Ring A] [Algebra S A]
    (e a : A) (x : principalModule (S := S) A e) :
    (principalLeftAction e a x : A) = a * x.1 := rfl

/-- A bijective left action identifies the algebra with the endomorphism algebra of `Ae`. -/
def moritaEquiv {A : Type u} [Ring A] [Algebra S A] (e : A)
    (h : Function.Bijective (principalLeftAction (S := S) e)) :
    A ≃ₐ[S] Module.End S (principalModule (S := S) A e) :=
  AlgEquiv.ofBijective (principalLeftAction e) h

/-- The matrix form of the Morita equivalence after choosing a basis of `Ae`. -/
def moritaMatrixEquiv {A : Type u} [Ring A] [Algebra S A] (e : A)
    (b : Module.Basis n S (principalModule (S := S) A e))
    (h : Function.Bijective (principalLeftAction (S := S) e)) :
    A ≃ₐ[S] Matrix n n S :=
  (moritaEquiv e h).trans (LinearMap.toMatrixAlgEquiv b)

/-- The representation of `G` on the principal module cut out by `e`. -/
def principalRepresentation (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho) :
    Representation S G (principalModule (S := S) (imageAlgebra (S := S) rho) e) :=
  (principalLeftAction e).toMonoidHom.comp (imageMonoidHom rho)

/-- Transport the principal-module action to coordinates supplied by a basis. -/
def descendedRepresentation (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho)
    (b : Module.Basis n S (principalModule (S := S) (imageAlgebra (S := S) rho) e)) :
    Representation S G (n → S) where
  toFun g := b.equivFun.toLinearMap.comp
    ((principalRepresentation rho e g).comp b.equivFun.symm.toLinearMap)
  map_one' := by
    classical
    ext x
    simp [principalRepresentation, Pi.single_apply, eq_comm]
  map_mul' g h := by
    ext x
    simp [principalRepresentation, Module.End.mul_apply]

@[simp]
lemma descendedRepresentation_matrix_apply
    (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho)
    (b : Module.Basis n S (principalModule (S := S) (imageAlgebra (S := S) rho) e))
    (g : G) (i j : n) :
    representationMatrix (descendedRepresentation rho e b) g i j =
      b.repr (principalRepresentation rho e g (b j)) i := by
  classical
  simp [representationMatrix, descendedRepresentation, LinearMap.toMatrixAlgEquiv'_apply,
    Pi.single_apply, eq_comm]

/-- The descended action, bundled as a `GLₙ(S)`-valued representation. -/
def descendedGL (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho)
    (b : Module.Basis n S (principalModule (S := S) (imageAlgebra (S := S) rho) e)) :
    G →* GL n S :=
  (representationMatrixHom (descendedRepresentation rho e b)).toHomUnits

@[simp]
lemma descendedGL_coe (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho)
    (b : Module.Basis n S (principalModule (S := S) (imageAlgebra (S := S) rho) e))
    (g : G) :
    ((descendedGL rho e b g : GL n S) : Matrix n n S) =
      representationMatrix (descendedRepresentation rho e b) g := rfl

/-- Evaluate a matrix in `Ae` on a vector.  This is the comparison map used to identify scalar
extension of the principal module with the original representation space. -/
def principalEvaluation (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho) (v : n → R) :
    principalModule (S := S) (imageAlgebra (S := S) rho) e →ₗ[S] n → R where
  toFun x := (x.1.1 : Matrix n n R).mulVec v
  map_add' x y := by simp [Matrix.add_mulVec]
  map_smul' r x := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Algebra.smul_def,
      Matrix.algebraMap_matrix_apply, Finset.mul_sum, mul_assoc]

/-- Evaluation intertwines the principal-module action and the original representation. -/
lemma principalEvaluation_equivariant (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho) (v : n → R) (g : G)
    (x : principalModule (S := S) (imageAlgebra (S := S) rho) e) :
    principalEvaluation rho e v (principalRepresentation rho e g x) =
      rho g (principalEvaluation rho e v x) := by
  change (representationMatrix rho g * (x.1.1 : Matrix n n R)).mulVec v =
    rho g ((x.1.1 : Matrix n n R).mulVec v)
  rw [← Matrix.mulVec_mulVec]
  change Matrix.toLinAlgEquiv' (representationMatrix rho g)
    ((x.1.1 : Matrix n n R).mulVec v) = _
  rw [show Matrix.toLinAlgEquiv' (representationMatrix rho g) = rho g by
    simp [representationMatrix]]

/-- Coordinates of evaluation are obtained by extending the principal-module coordinates. -/
lemma principalEvaluation_repr (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho) (v : n → R)
    (b : Module.Basis n S (principalModule (S := S) (imageAlgebra (S := S) rho) e))
    (c : Module.Basis n R (n → R))
    (hc : ∀ i, c i = principalEvaluation rho e v (b i))
    (x : principalModule (S := S) (imageAlgebra (S := S) rho) e) (i : n) :
    c.repr (principalEvaluation rho e v x) i = algebraMap S R (b.repr x i) := by
  have heval : principalEvaluation rho e v x =
      ∑ j, algebraMap S R (b.repr x j) • c j := by
    calc
      principalEvaluation rho e v x =
          principalEvaluation rho e v (∑ j, b.repr x j • b j) := by
            rw [b.sum_repr]
      _ = ∑ j, principalEvaluation rho e v (b.repr x j • b j) := by
            exact map_sum (principalEvaluation rho e v)
              (fun j ↦ b.repr x j • b j) Finset.univ
      _ = ∑ j, algebraMap S R (b.repr x j) • c j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [map_smul, ← hc]
            ext k
            simp [Algebra.smul_def]
  rw [heval, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply]
  simp [Finsupp.single_apply, eq_comm]

/-- After scalar extension, the descended matrices are the matrices of the original
representation in the evaluation basis; equivalently, the two representations are conjugate. -/
theorem map_descendedRepresentation_eq_toMatrix
    (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho) (v : n → R)
    (b : Module.Basis n S (principalModule (S := S) (imageAlgebra (S := S) rho) e))
    (c : Module.Basis n R (n → R))
    (hc : ∀ i, c i = principalEvaluation rho e v (b i)) (g : G) :
    (representationMatrix (descendedRepresentation rho e b) g).map (algebraMap S R) =
      LinearMap.toMatrix c c (rho g) := by
  ext i j
  rw [Matrix.map_apply, descendedRepresentation_matrix_apply,
    LinearMap.toMatrix_apply]
  rw [← principalEvaluation_repr rho e v b c hc
    (principalRepresentation rho e g (b j)) i]
  rw [principalEvaluation_equivariant, ← hc]

/-- Morita reconstruction: a full idempotent whose principal module has rank `n` produces both
the matrix-algebra identification and the descended `GLₙ`-valued representation. -/
theorem exists_moritaEquiv_and_descendedGL
    (rho : Representation R G (n → R))
    (e : imageAlgebra (S := S) rho)
    (b : Module.Basis n S (principalModule (S := S) (imageAlgebra (S := S) rho) e))
    (hMorita : Function.Bijective (principalLeftAction (S := S) e)) :
    (Nonempty (imageAlgebra (S := S) rho ≃ₐ[S] Matrix n n S)) ∧
      Nonempty (G →* GL n S) := by
  constructor
  · exact ⟨moritaMatrixEquiv e b hMorita⟩
  · exact ⟨descendedGL rho e b⟩

end

end MoritaReconstruction

end Representation

namespace Deformation

namespace MoritaReconstruction

noncomputable section

open Representation

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable (n : Type) [Fintype n] [DecidableEq n]
variable [Finite (IsLocalRing.ResidueField O)]
variable (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

/-- The universal framed lift as an ordinary linear representation. -/
def universalLinearRepresentation :
    Representation (ProfiniteFramedLimit O G n rho) G
      (n → ProfiniteFramedLimit O G n rho) :=
  Representation.MoritaReconstruction.linearRepresentationOfGL
    (profiniteUniversalLift O G n rho)

omit [TotallyDisconnectedSpace G] in
@[simp]
lemma universalLinearRepresentation_matrix (g : G) :
    representationMatrix (universalLinearRepresentation O G n rho) g =
      profiniteUniversalMatrix O G n rho g := by
  exact Representation.MoritaReconstruction.representationMatrix_linearRepresentationOfGL
    (profiniteUniversalLift O G n rho) g

/-- The image algebra of the universal framed lift over its closed trace ring. -/
abbrev UniversalImageAlgebra :=
  imageAlgebra (S := UniversalTraceRing O G n rho)
    (universalLinearRepresentation O G n rho)

set_option synthInstance.maxHeartbeats 100000 in
-- Lean v4.35 needs extra time to synthesize the module structure through the trace-ring aliases.
/-- The `GLₙ`-valued representation over the closed trace ring reconstructed from universal
Morita data. -/
def universalTraceDescendedGL
    (e : UniversalImageAlgebra O G n rho)
    (b : Module.Basis n (UniversalTraceRing O G n rho)
      (Representation.MoritaReconstruction.principalModule
        (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e)) :
    G →* GL n (UniversalTraceRing O G n rho) :=
  Representation.MoritaReconstruction.descendedGL
    (universalLinearRepresentation O G n rho) e b

set_option synthInstance.maxHeartbeats 100000 in
-- Lean v4.35 needs extra time to synthesize the module structure through the trace-ring aliases.
/-- The corresponding identification of the universal image algebra with a matrix algebra over
the closed trace ring. -/
def universalMoritaMatrixEquiv
    (e : UniversalImageAlgebra O G n rho)
    (b : Module.Basis n (UniversalTraceRing O G n rho)
      (Representation.MoritaReconstruction.principalModule
        (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e))
    (hMorita : Function.Bijective
      (Representation.MoritaReconstruction.principalLeftAction
        (S := UniversalTraceRing O G n rho) e)) :
    UniversalImageAlgebra O G n rho ≃ₐ[UniversalTraceRing O G n rho]
      Matrix n n (UniversalTraceRing O G n rho) :=
  Representation.MoritaReconstruction.moritaMatrixEquiv
    e b hMorita

set_option synthInstance.maxHeartbeats 100000 in
-- Lean v4.35 needs extra time to synthesize the module structure through the trace-ring aliases.
omit [TotallyDisconnectedSpace G] in
/-- Scalar extension of the reconstructed universal representation is the original universal
framed lift written in the evaluation basis, hence is conjugate to it. -/
theorem universalTraceDescendedGL_conjugate
    (e : UniversalImageAlgebra O G n rho) (v : n → ProfiniteFramedLimit O G n rho)
    (b : Module.Basis n (UniversalTraceRing O G n rho)
      (Representation.MoritaReconstruction.principalModule
        (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e))
    (c : Module.Basis n (ProfiniteFramedLimit O G n rho)
      (n → ProfiniteFramedLimit O G n rho))
    (hc : ∀ i, c i = Representation.MoritaReconstruction.principalEvaluation
      (universalLinearRepresentation O G n rho) e v (b i)) (g : G) :
    ((universalTraceDescendedGL O G n rho e b g :
        GL n (UniversalTraceRing O G n rho)) :
      Matrix n n (UniversalTraceRing O G n rho)).map
        (algebraMap (UniversalTraceRing O G n rho)
          (ProfiniteFramedLimit O G n rho)) =
      LinearMap.toMatrix c c (universalLinearRepresentation O G n rho g) := by
  exact Representation.MoritaReconstruction.map_descendedRepresentation_eq_toMatrix
    (universalLinearRepresentation O G n rho) e v b c hc g

set_option synthInstance.maxHeartbeats 100000 in
-- Lean v4.35 needs extra time to synthesize the module structure through the trace-ring aliases.
omit [TotallyDisconnectedSpace G] in
/-- The universal specialization of Morita reconstruction. -/
theorem exists_universalMoritaEquiv_and_descendedGL
    (e : UniversalImageAlgebra O G n rho) (_he : IsIdempotentElem e)
    (b : Module.Basis n (UniversalTraceRing O G n rho)
      (Representation.MoritaReconstruction.principalModule
        (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e))
    (hMorita : Function.Bijective
      (Representation.MoritaReconstruction.principalLeftAction
        (S := UniversalTraceRing O G n rho) e)) :
    (Nonempty (UniversalImageAlgebra O G n rho ≃ₐ[UniversalTraceRing O G n rho]
      Matrix n n (UniversalTraceRing O G n rho))) ∧
      Nonempty (G →* GL n (UniversalTraceRing O G n rho)) := by
  constructor
  · exact ⟨universalMoritaMatrixEquiv O G n rho e b hMorita⟩
  · exact ⟨universalTraceDescendedGL O G n rho e b⟩

end

end MoritaReconstruction

end Deformation
