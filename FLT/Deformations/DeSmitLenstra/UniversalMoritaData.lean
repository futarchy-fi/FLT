/-
Copyright (c) 2026 FLT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT contributors
-/
module

public import FLT.Deformations.DeSmitLenstra.MoritaReconstruction
public import FLT.Deformations.LiftFunctor
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Morita data for the universal trace ring

We lift a Burnside basis of the residual representation to the universal framed ring.  The
lifted matrices remain a basis because their trace Gram matrix is invertible.  Trace-pairing
descent then gives a finite-free basis of the universal image algebra over the closed trace ring.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Representation

namespace MoritaReconstruction

noncomputable section

variable {R : Type u} {n : Type} {ι : Type u}
variable [CommRing R] [Fintype n] [Fintype ι] [DecidableEq ι]

/-- A family of square matrices whose trace Gram matrix is invertible is a basis, provided it has
the cardinality of the standard matrix basis. -/
theorem exists_basis_of_isUnit_traceGram
    (v : ι → Matrix n n R) (hcard : Fintype.card ι = Fintype.card (n × n))
    (hgram : IsUnit (Matrix.det ((fun i j ↦ (v i * v j).trace) : Matrix ι ι R))) :
    ∃ b : Module.Basis ι R (Matrix n n R), ∀ i, b i = v i := by
  classical
  let e : ι ≃ n × n := Fintype.equivOfCardEq hcard
  let b₀ : Module.Basis ι R (Matrix n n R) :=
    (Matrix.stdBasis R n n).reindex e.symm
  let c : Module.Basis ι R (ι → R) := Pi.basisFun R ι
  let f : (ι → R) →ₗ[R] Matrix n n R := c.constr R v
  let B : LinearMap.BilinForm R (Matrix n n R) := matrixTracePairing
  have hf (i : ι) : f (c i) = v i := by simp [f]
  have hmatrix :
      (B.comp f f).toMatrix c = ((fun i j ↦ (v i * v j).trace) : Matrix ι ι R) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, B, matrixTracePairing_apply, hf]
  have hmatrix' :
      (LinearMap.toMatrix c b₀ f).transpose * B.toMatrix b₀ * LinearMap.toMatrix c b₀ f =
        (B.comp f f).toMatrix c :=
    (LinearMap.BilinForm.toMatrix_comp (b := b₀) c B f f).symm
  have hproduct : IsUnit
      ((LinearMap.toMatrix c b₀ f).det *
        (B.toMatrix b₀).det * (LinearMap.toMatrix c b₀ f).det) := by
    have hdetprod :
        ((LinearMap.toMatrix c b₀ f).transpose * B.toMatrix b₀ *
          LinearMap.toMatrix c b₀ f).det =
            (LinearMap.toMatrix c b₀ f).det *
              (B.toMatrix b₀).det * (LinearMap.toMatrix c b₀ f).det := by
      simp only [Matrix.det_mul, Matrix.det_transpose]
    rw [← hdetprod, hmatrix', hmatrix]
    exact hgram
  have hdet : IsUnit (LinearMap.toMatrix c b₀ f).det :=
    (IsUnit.mul_iff.mp hproduct).2
  have hdet' : IsUnit (b₀.det v) := by
    have htoMatrix : b₀.toMatrix v = LinearMap.toMatrix c b₀ f := by
      ext i j
      rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, hf]
    rw [Module.Basis.det_apply, htoMatrix]
    exact hdet
  obtain ⟨hli, hspan⟩ := (b₀.is_basis_iff_det).mpr hdet'
  let b := Module.Basis.mk hli hspan.ge
  exact ⟨b, fun i ↦ by simp [b]⟩

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
variable [Finite (ResidueField O)]
variable (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

/-- The residual continuous representation regarded as a linear representation.  The explicit
type ascription bridges the definitional presentation used by `repnFunctor`. -/
abbrev residualLinearRepresentation :
    Representation (ProartinianCat.residueField (𝓞 := O)) G
      (n → ProartinianCat.residueField (𝓞 := O)) :=
  toRepresentation
    (show (repnFunctor n G O).obj .residueField from rho)

omit [IsNoetherianRing O] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Finite (ResidueField O)] in
@[simp]
lemma residualLinearRepresentation_matrix (g : G) :
    representationMatrix (residualLinearRepresentation O G n rho) g =
      (rho g : Matrix n n (ProartinianCat.residueField (𝓞 := O))) := by
  change LinearMap.toMatrixAlgEquiv'
      ((rho g : Matrix n n (ProartinianCat.residueField (𝓞 := O))).mulVecLin) = _
  ext i j
  change (rho g : Matrix n n (ProartinianCat.residueField (𝓞 := O))).mulVec
      (Pi.single j 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl

/-- The residue homomorphism of the universal framed ring, with its domain presented by the
abbreviation used throughout the de Smit--Lenstra construction. -/
def framedResidueRingHom : ProfiniteFramedLimit O G n rho →+*
    ProartinianCat.residueField (𝓞 := O) :=
  (ProartinianCat.toResidueField
    (profiniteFramedLimitObject O G n rho)).hom.toRingHom

/-- Reduction of the universal image algebra to the residual matrix algebra. -/
def universalImageResidue :
    UniversalImageAlgebra O G n rho →+*
      Matrix n n (ProartinianCat.residueField (𝓞 := O)) where
  toFun x := x.1.map (framedResidueRingHom O G n rho)
  map_one' := Matrix.map_one _ (map_zero _) (map_one _)
  map_mul' _ _ := Matrix.map_mul
  map_zero' := Matrix.map_zero _ (map_zero _)
  map_add' x y := Matrix.map_add _ (map_add _) x.1 y.1

/-- Explicit scalar multiplication in the universal image algebra.  Spelling this through the
ambient matrix algebra keeps typeclass search independent of the nested subalgebra coercions. -/
def universalImageScalarMul (s : UniversalTraceRing O G n rho)
    (x : UniversalImageAlgebra O G n rho) : UniversalImageAlgebra O G n rho :=
  ⟨algebraMap (UniversalTraceRing O G n rho)
      (Matrix n n (ProfiniteFramedLimit O G n rho)) s * x.1,
    (UniversalImageAlgebra O G n rho).mul_mem
      ((UniversalImageAlgebra O G n rho).algebraMap_mem s) x.2⟩

omit [TotallyDisconnectedSpace G] in
lemma universalImageResidue_smul (s : UniversalTraceRing O G n rho)
    (x : UniversalImageAlgebra O G n rho) :
    universalImageResidue O G n rho
        (universalImageScalarMul O G n rho s x) =
      ((ProartinianCat.toResidueField
        (universalTraceRingObject O G n rho)).hom s •
        universalImageResidue O G n rho x :
          Matrix n n (ProartinianCat.residueField (𝓞 := O))) := by
  have hres : universalTraceRingInclusion O G n rho ≫
      ProartinianCat.toResidueField (profiniteFramedLimitObject O G n rho) =
        ProartinianCat.toResidueField (universalTraceRingObject O G n rho) :=
    Subsingleton.elim _ _
  unfold universalImageResidue universalImageScalarMul
  change ((algebraMap (UniversalTraceRing O G n rho)
      (Matrix n n (ProfiniteFramedLimit O G n rho)) s) * x.1).map
        (framedResidueRingHom O G n rho) =
      (ProartinianCat.toResidueField
        (universalTraceRingObject O G n rho)).hom s •
        x.1.map (framedResidueRingHom O G n rho)
  have hsmap : (algebraMap (UniversalTraceRing O G n rho)
      (Matrix n n (ProfiniteFramedLimit O G n rho)) s).map
        (framedResidueRingHom O G n rho) =
      algebraMap (ProartinianCat.residueField (𝓞 := O))
        (Matrix n n (ProartinianCat.residueField (𝓞 := O)))
          ((ProartinianCat.toResidueField
            (universalTraceRingObject O G n rho)).hom s) := by
    let qR : ProfiniteFramedLimit O G n rho →+*
        ProartinianCat.residueField (𝓞 := O) :=
      framedResidueRingHom O G n rho
    let _ : Algebra (ProfiniteFramedLimit O G n rho)
        (ProartinianCat.residueField (𝓞 := O)) := qR.toAlgebra
    have hs : qR s.1 = (ProartinianCat.toResidueField
        (universalTraceRingObject O G n rho)).hom s := by
      exact congrArg (fun f ↦ f.hom s) hres
    rw [show algebraMap (UniversalTraceRing O G n rho)
      (Matrix n n (ProfiniteFramedLimit O G n rho)) s =
        algebraMap (ProfiniteFramedLimit O G n rho)
          (Matrix n n (ProfiniteFramedLimit O G n rho)) s.1 from rfl]
    rw [Matrix.map_algebraMap (R := ProfiniteFramedLimit O G n rho)
      s.1 qR (map_zero qR) rfl]
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.algebraMap_matrix_apply, Algebra.algebraMap_self_apply]
      change qR s.1 = _
      exact hs
    · simp [Matrix.algebraMap_matrix_apply, hij]
  rw [Algebra.smul_def, ← hsmap]
  exact Matrix.map_mul

omit [TotallyDisconnectedSpace G] in
@[simp]
lemma universalImageResidue_imageElement (g : G) :
    universalImageResidue O G n rho
      (Representation.MoritaReconstruction.imageElement
        (S := UniversalTraceRing O G n rho)
        (universalLinearRepresentation O G n rho) g) =
      (rho g : Matrix n n (ProartinianCat.residueField (𝓞 := O))) := by
  have hu := congrArg
    (fun r : G →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦ r g)
    (profiniteUniversalContinuousLift_isFramedLift O G n rho)
  unfold universalImageResidue Representation.MoritaReconstruction.imageElement
  change (representationMatrix (universalLinearRepresentation O G n rho) g).map
      (framedResidueRingHom O G n rho) = _
  rw [universalLinearRepresentation_matrix]
  exact congrArg Units.val hu

omit [TotallyDisconnectedSpace G] in
/-- Burnside spanning makes reduction of the universal image algebra onto the full residual
matrix algebra surjective. -/
theorem universalImageResidue_surjective
    [(residualLinearRepresentation O G n rho).IsAbsolutelyIrreducible.{u}] :
    Function.Surjective (universalImageResidue O G n rho) := by
  intro M
  have hspan : M ∈ Submodule.span
      (ProartinianCat.residueField (𝓞 := O))
      (Set.range (representationMatrix (residualLinearRepresentation O G n rho))) := by
    rw [Representation.span_range_representationMatrix_eq_top]
    exact Submodule.mem_top
  induction hspan using Submodule.span_induction with
  | mem M hM =>
      obtain ⟨g, rfl⟩ := hM
      refine ⟨Representation.MoritaReconstruction.imageElement
        (S := UniversalTraceRing O G n rho)
        (universalLinearRepresentation O G n rho) g, ?_⟩
      rw [residualLinearRepresentation_matrix,
        universalImageResidue_imageElement]
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩
  | smul c x _ hx =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨s, hs⟩ := ProartinianCat.toResidueField_surjective
        (universalTraceRingObject O G n rho) c
      let s' : UniversalTraceRing O G n rho := s
      refine ⟨universalImageScalarMul O G n rho s' x, ?_⟩
      rw [universalImageResidue_smul]
      rw [show (ProartinianCat.toResidueField
        (universalTraceRingObject O G n rho)).hom s' = c from hs]

/-- The trace-pairing matrix of a family in the universal framed lift, with entries bundled in
the closed trace ring. -/
def universalTraceGram {ι : Type u} (g : ι → G) :
    Matrix ι ι (UniversalTraceRing O G n rho) :=
  fun i j ↦ ⟨(profiniteUniversalMatrix O G n rho (g i * g j)).trace,
    universalTrace_mem O G n rho (g i * g j)⟩

omit [TotallyDisconnectedSpace G] in
lemma universalTraceGram_map {ι : Type u} (g : ι → G) :
    (universalTraceGram O G n rho g).map
        (algebraMap (UniversalTraceRing O G n rho)
          (ProfiniteFramedLimit O G n rho)) =
      (fun i j ↦
        (representationMatrix (universalLinearRepresentation O G n rho) (g i * g j)).trace) := by
  apply Matrix.ext
  intro i j
  change (profiniteUniversalMatrix O G n rho (g i * g j)).trace = _
  rw [universalLinearRepresentation_matrix]

omit [TotallyDisconnectedSpace G] in
lemma universalTraceGram_residue {ι : Type u} (g : ι → G) :
    (universalTraceGram O G n rho g).map
        (ProartinianCat.toResidueField
          (universalTraceRingObject O G n rho)).hom.toRingHom =
      (fun i j ↦
        (representationMatrix (residualLinearRepresentation O G n rho)
          (g i * g j)).trace) := by
  apply Matrix.ext
  intro i j
  have hres : universalTraceRingInclusion O G n rho ≫
      ProartinianCat.toResidueField (profiniteFramedLimitObject O G n rho) =
        ProartinianCat.toResidueField (universalTraceRingObject O G n rho) :=
    Subsingleton.elim _ _
  have hu := congrArg
    (fun r : G →* GL n (ProartinianCat.residueField (𝓞 := O)) ↦ r (g i * g j))
    (profiniteUniversalContinuousLift_isFramedLift O G n rho)
  change (ProartinianCat.toResidueField
      (universalTraceRingObject O G n rho)).hom
        ⟨(profiniteUniversalMatrix O G n rho (g i * g j)).trace,
          universalTrace_mem O G n rho (g i * g j)⟩ = _
  rw [← hres]
  change (ProartinianCat.toResidueField
      (profiniteFramedLimitObject O G n rho)).hom
        ((profiniteUniversalMatrix O G n rho (g i * g j)).trace) = _
  calc
    _ = ((profiniteUniversalMatrix O G n rho (g i * g j)).map
        (ProartinianCat.toResidueField
          (profiniteFramedLimitObject O G n rho)).hom).trace := by
      change (ProartinianCat.toResidueField
          (profiniteFramedLimitObject O G n rho)).hom
            (∑ k, profiniteUniversalMatrix O G n rho (g i * g j) k k) =
        ∑ k, (ProartinianCat.toResidueField
          (profiniteFramedLimitObject O G n rho)).hom
            (profiniteUniversalMatrix O G n rho (g i * g j) k k)
      exact map_sum (ProartinianCat.toResidueField
        (profiniteFramedLimitObject O G n rho)).hom
        (fun k ↦ profiniteUniversalMatrix O G n rho (g i * g j) k k) Finset.univ
    _ = ((rho.toMonoidHom (g i * g j) : GL n
        (ProartinianCat.residueField (𝓞 := O))) :
          Matrix n n (ProartinianCat.residueField (𝓞 := O))).trace := by
      exact congrArg Matrix.trace (congrArg Units.val hu)
    _ = _ := by
      rw [residualLinearRepresentation_matrix]
      change ((rho (g i * g j) : GL n
        (ProartinianCat.residueField (𝓞 := O))) :
          Matrix n n (ProartinianCat.residueField (𝓞 := O))).trace = _
      rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The nested trace-ring/image-algebra module instance is expensive to synthesize in a clean build.
omit [TotallyDisconnectedSpace G] in
/-- Burnside's residual basis lifts to a basis of the full matrix algebra over the universal
framed ring, and the same family gives a finite-free basis of the image algebra over the closed
trace ring. -/
theorem exists_universalTraceImageAlgebra_basis
    [(residualLinearRepresentation O G n rho).IsAbsolutelyIrreducible.{u}] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (g : ι → G)
      (b : Module.Basis ι (ProfiniteFramedLimit O G n rho)
        (Matrix n n (ProfiniteFramedLimit O G n rho)))
      (_bA : Module.Basis ι (UniversalTraceRing O G n rho)
        (UniversalImageAlgebra O G n rho)),
      ∀ i, b i = profiniteUniversalMatrix O G n rho (g i) := by
  classical
  obtain ⟨ι, hι, hdec, g, bbar, hbbar, hdetbar⟩ :=
    Representation.exists_tracePairing_basis
      (residualLinearRepresentation O G n rho)
  let _ : Fintype ι := hι
  let _ : DecidableEq ι := hdec
  let C := universalTraceGram O G n rho g
  have hCdet : IsUnit C.det := by
    let q := (ProartinianCat.toResidueField
      (universalTraceRingObject O G n rho)).hom.toRingHom
    change UniversalTraceRing O G n rho →+*
      ProartinianCat.residueField (𝓞 := O) at q
    have hmapC : C.map q =
        (fun i j ↦ (representationMatrix
          (residualLinearRepresentation O G n rho) (g i * g j)).trace) := by
      apply Matrix.ext
      intro i j
      change q (universalTraceGram O G n rho g i j) = _
      have h := congrFun (congrFun
        (universalTraceGram_residue O G n rho g) i) j
      exact h
    have hne : q C.det ≠ 0 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmapC]
      exact hdetbar
    by_contra hunit
    have hm : C.det ∈ maximalIdeal (UniversalTraceRing O G n rho) :=
      (mem_maximalIdeal C.det).mpr (mem_nonunits_iff.mpr hunit)
    have hker : C.det ∈ RingHom.ker q := by
      have hkerEq := ProartinianCat.ker_toResidueField
        (universalTraceRingObject O G n rho)
      change RingHom.ker q = maximalIdeal (UniversalTraceRing O G n rho) at hkerEq
      rw [hkerEq]
      exact hm
    exact hne (RingHom.mem_ker.mp hker)
  have hcard : Fintype.card ι = Fintype.card (n × n) := by
    calc
      Fintype.card ι = Module.finrank
          (ProartinianCat.residueField (𝓞 := O))
          (Matrix n n (ProartinianCat.residueField (𝓞 := O))) :=
        (Module.finrank_eq_card_basis bbar).symm
      _ = Fintype.card (n × n) := by simp [Module.finrank_matrix]
  have hgram : IsUnit (Matrix.det ((fun i j ↦
      (profiniteUniversalMatrix O G n rho (g i) *
        profiniteUniversalMatrix O G n rho (g j)).trace) :
          Matrix ι ι (ProfiniteFramedLimit O G n rho))) := by
    have hmul : ((fun i j ↦
        (profiniteUniversalMatrix O G n rho (g i) *
          profiniteUniversalMatrix O G n rho (g j)).trace) :
            Matrix ι ι (ProfiniteFramedLimit O G n rho)) =
        (fun i j ↦
          (representationMatrix (universalLinearRepresentation O G n rho)
            (g i * g j)).trace) := by
      apply Matrix.ext
      intro i j
      rw [universalLinearRepresentation_matrix]
      exact congrArg Matrix.trace (congrArg Units.val
        (map_mul (profiniteUniversalLift O G n rho) (g i) (g j))).symm
    rw [hmul, ← universalTraceGram_map O G n rho g,
      show ((universalTraceGram O G n rho g).map
        (algebraMap (UniversalTraceRing O G n rho)
          (ProfiniteFramedLimit O G n rho))).det =
          algebraMap (UniversalTraceRing O G n rho)
            (ProfiniteFramedLimit O G n rho)
              (universalTraceGram O G n rho g).det by
        exact (RingHom.map_det _ _).symm]
    exact hCdet.map _
  obtain ⟨b, hb⟩ :=
    Representation.MoritaReconstruction.exists_basis_of_isUnit_traceGram
      (fun i ↦ profiniteUniversalMatrix O G n rho (g i)) hcard hgram
  have htrace : ∀ h,
      (representationMatrix (universalLinearRepresentation O G n rho) h).trace ∈
        Set.range (algebraMap (UniversalTraceRing O G n rho)
          (ProfiniteFramedLimit O G n rho)) := by
    intro h
    refine ⟨⟨(profiniteUniversalMatrix O G n rho h).trace,
      universalTrace_mem O G n rho h⟩, ?_⟩
    rw [universalLinearRepresentation_matrix]
    rfl
  have hb' : ∀ i,
      b i = representationMatrix (universalLinearRepresentation O G n rho) (g i) := by
    intro i
    rw [hb, universalLinearRepresentation_matrix]
  let bA : Module.Basis ι (UniversalTraceRing O G n rho)
      (UniversalImageAlgebra O G n rho) :=
    Representation.traceImageAlgebraBasis
      (universalLinearRepresentation O G n rho) g b hb'
      C (universalTraceGram_map O G n rho g) hCdet htrace
  exact ⟨ι, inferInstance, inferInstance, g, b, bA, hb⟩

end

end MoritaReconstruction

end Deformation
