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
Residual matrix units lift to an idempotent whose principal module is free of rank `n`; its left
action is the required Morita equivalence, and evaluation gives a strict basis after scalar
extension to the universal framed ring.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w x

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
      exact ⟨x + y, (universalImageResidue O G n rho).map_add x y⟩
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

namespace Representation.MoritaReconstruction

/-- Lifts of a residual basis form a basis when reduction has the expected extended kernel. -/
theorem lift_residue_basis
    {S A : Type u} {k : Type w} {B : Type x} {ι : Type v}
    [CommRing S] [IsLocalRing S] [Ring A] [Algebra S A]
    [Field k] [Ring B] [Algebra k B] [Finite ι]
    (b : Module.Basis ι S A) (qS : S →+* k) (hqS : Function.Surjective qS)
    (hkerS : RingHom.ker qS = maximalIdeal S) (qA : A →+* B)
    (hqA : Function.Surjective qA)
    (hscalar : ∀ s x, qA (s • x) = qS s • qA x)
    (hkerA : RingHom.ker qA = Deformation.CompatibleIdempotent.extendedIdeal
      (A := A) (maximalIdeal S))
    (v : ι → A) (vbar : Module.Basis ι k B)
    (hv : ∀ i, qA (v i) = vbar i) :
    ∃ bv : Module.Basis ι S A, ∀ i, bv i = v i := by
  classical
  let _ := Fintype.ofFinite ι
  have hli : LinearIndependent k (fun i ↦ qA (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    choose s hs using fun j ↦ hqS (c j)
    have hsum : qA (∑ j, s j • b j) = 0 := by
      rw [map_sum]
      simp_rw [hscalar, hs]
      exact hc
    have hm : ∑ j, s j • b j ∈
        Deformation.CompatibleIdempotent.extendedIdeal (A := A) (maximalIdeal S) := by
      rw [← hkerA, RingHom.mem_ker]
      exact hsum
    have hcoord := (Deformation.CompatibleIdempotent.mem_extendedIdeal_iff
      b (maximalIdeal S) _).mp hm i
    have hcoordEq : b.repr (∑ j, s j • b j) i = s i := by
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
        Finset.sum_apply, Pi.smul_apply, Module.Basis.repr_self]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp
    have hsi : s i ∈ maximalIdeal S := by simpa only [hcoordEq] using hcoord
    rw [← hs i]
    apply RingHom.mem_ker.mp
    rw [hkerS]
    exact hsi
  have hspan : Submodule.span k (Set.range fun i ↦ qA (b i)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hqA y
    rw [← b.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ ↦ by
      rw [hscalar]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  let qb : Module.Basis ι k B := Module.Basis.mk hli hspan.ge
  have hqb (i : ι) : qb i = qA (b i) := by simp [qb]
  have hrepr (x : A) (i : ι) : qb.repr (qA x) i = qS (b.repr x i) := by
    have hx : qA x = ∑ j, qS (b.repr x j) • qb j := by
      calc
        qA x = qA (∑ j, b.repr x j • b j) := congrArg qA (b.sum_repr x).symm
        _ = _ := by
          rw [map_sum]
          simp_rw [hscalar, hqb]
    rw [hx, map_sum]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
      Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  have hmatrix : (b.toMatrix v).map qS = qb.toMatrix vbar := by
    ext i j
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply,
      Module.Basis.toMatrix_apply, ← hv, hrepr]
  have hdetne : qS (b.det v) ≠ 0 := by
    rw [Module.Basis.det_apply, RingHom.map_det, RingHom.mapMatrix_apply, hmatrix]
    exact (qb.isUnit_det vbar).ne_zero
  have hdet : IsUnit (b.det v) := by
    by_contra hunit
    have hm : b.det v ∈ maximalIdeal S :=
      (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
    have hz : qS (b.det v) = 0 := RingHom.mem_ker.mp (hkerS.symm ▸ hm)
    exact hdetne hz
  obtain ⟨hli', hspan'⟩ := (b.is_basis_iff_det).mpr hdet
  let bv := Module.Basis.mk hli' hspan'.ge
  exact ⟨bv, fun i ↦ by simp [bv]⟩


end Representation.MoritaReconstruction

open CategoryTheory

namespace Deformation.MoritaReconstruction

variable (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable (n : Type) [Fintype n] [DecidableEq n]
variable [Finite (ResidueField O)]
variable (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))

set_option synthInstance.maxHeartbeats 100000 in
-- The quotient-algebra instance follows through several bundled algebra structures.
set_option maxHeartbeats 800000 in
-- Quotient finiteness and the residue-cardinality comparison are expensive to synthesize.
omit [TotallyDisconnectedSpace G] in
/-- The kernel of residual reduction is the maximal ideal extended to the universal image. -/
theorem universalImageResidue_ker {ι : Type u} [Fintype ι]
    (bA : Module.Basis ι (UniversalTraceRing O G n rho)
      (UniversalImageAlgebra O G n rho))
    (hcard : Fintype.card ι = Fintype.card (n × n))
    (hsurj : Function.Surjective (universalImageResidue O G n rho)) :
    RingHom.ker (universalImageResidue O G n rho) =
      CompatibleIdempotent.extendedIdeal
        (A := UniversalImageAlgebra O G n rho)
        (maximalIdeal (UniversalTraceRing O G n rho)) := by
  let S := UniversalTraceRing O G n rho
  let A := UniversalImageAlgebra O G n rho
  let k : Type u := ProartinianCat.residueField (𝓞 := O)
  let qS : S →+* k :=
    (ProartinianCat.toResidueField
      (universalTraceRingObject O G n rho)).hom.toRingHom
  let qA : A →+* Matrix n n k := universalImageResidue O G n rho
  have hkerS : RingHom.ker qS = maximalIdeal S := by
    exact ProartinianCat.ker_toResidueField
      (universalTraceRingObject O G n rho)
  have hle : CompatibleIdempotent.extendedIdeal (A := A) (maximalIdeal S) ≤
      RingHom.ker qA := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hqs : qS s = 0 := RingHom.mem_ker.mp (hkerS.symm ▸ hs)
    have h := universalImageResidue_smul O G n rho s (1 : A)
    have hmul : universalImageScalarMul O G n rho s (1 : A) =
        algebraMap S A s := by
      apply Subtype.ext
      dsimp [S, A]
      simp [universalImageScalarMul]
    rw [hmul] at h
    change qA (algebraMap S A s) = qS s • qA 1 at h
    rw [hqs] at h
    simpa using h
  let qbar : (A ⧸ CompatibleIdempotent.extendedIdeal (A := A) (maximalIdeal S)) →+*
      Matrix n n k := Ideal.Quotient.lift _ qA fun a ha ↦ RingHom.mem_ker.mp (hle ha)
  have hqbar : Function.Surjective qbar := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    change qA x = qA x
    rfl
  let _ : Algebra (universalTraceRingObject O G n rho)
      (UniversalImageAlgebra O G n rho) := by
    change Algebra (UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho)
    infer_instance
  let _ : Finite ((UniversalImageAlgebra O G n rho) ⧸
      CompatibleIdempotent.extendedIdeal
        (A := UniversalImageAlgebra O G n rho)
        (maximalIdeal (UniversalTraceRing O G n rho))) :=
    CompatibleIdempotent.quotientAlgebraFinite
      (universalTraceRingObject O G n rho) bA
      (CompatibleIdempotent.maximalOpenIdeal (universalTraceRingObject O G n rho))
  let eι : ι ≃ n × n := Fintype.equivOfCardEq hcard
  let ek : (S ⧸ maximalIdeal S) ≃+* k :=
    (Ideal.quotEquivOfEq hkerS.symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (ProartinianCat.toResidueField_surjective
          (universalTraceRingObject O G n rho)))
  let E : (A ⧸ CompatibleIdempotent.extendedIdeal (A := A) (maximalIdeal S)) ≃
      Matrix n n k :=
    (CompatibleIdempotent.quotientEquivPi bA (maximalIdeal S)).trans
      ((Equiv.arrowCongr eι ek.toEquiv).trans (Equiv.curry n n k))
  have hqbar_bij : Function.Bijective qbar :=
    (Nat.bijective_iff_surjective_and_card qbar).mpr
      ⟨hqbar, Nat.card_congr E⟩
  apply le_antisymm
  · intro x hx
    have hz : qbar (Ideal.Quotient.mk _ x) = 0 := by
      exact RingHom.mem_ker.mp hx
    have hmk : Ideal.Quotient.mk
        (CompatibleIdempotent.extendedIdeal (A := A) (maximalIdeal S)) x = 0 :=
      hqbar_bij.injective (by simpa using hz)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · exact hle

end Deformation.MoritaReconstruction

namespace Representation.MoritaReconstruction

set_option maxHeartbeats 800000 in
-- The two determinant arguments build bases for both the principal module and its endomorphisms.
/-- A lifted primitive matrix idempotent yields a rank-n principal module and a full left action. -/
theorem exists_matrix_idempotent_data
    {S A : Type u} {k : Type w} {n : Type v}
    [CommRing S] [IsLocalRing S] [Ring A] [Algebra S A]
    [Field k] [Fintype n] [DecidableEq n]
    (b0 : Module.Basis (n × n) S A) (qS : S →+* k)
    (hqS : Function.Surjective qS) (hkerS : RingHom.ker qS = maximalIdeal S)
    (qA : A →+* Matrix n n k) (hqA : Function.Surjective qA)
    (hscalar : ∀ s x, qA (s • x) = qS s • qA x)
    (hkerA : RingHom.ker qA = Deformation.CompatibleIdempotent.extendedIdeal
      (A := A) (maximalIdeal S)) (i0 : n) (e : A) (he : IsIdempotentElem e)
    (hqe : qA e = Matrix.single i0 i0 1) :
    ∃ (e : A), IsIdempotentElem e ∧
      ∃ B : Module.Basis (n × n) S A,
        ∃ b : Module.Basis n S (principalModule (S := S) A e),
          Function.Bijective (principalLeftAction (S := S) e) ∧
            (∀ i, (b i : A) = B (i, i0)) ∧
            (∀ ij, qA (B ij) = Matrix.stdBasis k n n ij) := by
  classical
  let ebar : Matrix n n k := Matrix.single i0 i0 1
  choose a ha using fun ij : n × n ↦ hqA (Matrix.stdBasis k n n ij)
  let w : n × n → A := fun ij ↦
    if ij.2 = i0 then a ij * e else a ij * (1 - e)
  have hw (ij : n × n) : qA (w ij) = Matrix.stdBasis k n n ij := by
    rcases ij with ⟨i, j⟩
    by_cases hj : j = i0
    · subst j
      simp only [w, ↓reduceIte, map_mul, hqe, ha,
        Matrix.stdBasis_eq_single]
      simp
    · simp only [w, hj, ↓reduceIte, map_mul, map_sub, map_one, hqe, ha,
        Matrix.stdBasis_eq_single]
      have hz : Matrix.single i j (1 : k) * Matrix.single i0 i0 1 = 0 := by
        exact Matrix.single_mul_single_of_ne (1 : k) i j i0 hj 1
      rw [mul_sub, mul_one, hz, sub_zero]
  obtain ⟨B, hB⟩ := lift_residue_basis b0 qS hqS hkerS qA hqA hscalar hkerA
    w (Matrix.stdBasis k n n) hw
  have hBe (ij : n × n) : B ij * e = if ij.2 = i0 then B ij else 0 := by
    rw [hB]
    by_cases hj : ij.2 = i0
    · simp only [w, hj, ↓reduceIte, mul_assoc, he.eq]
    · simp only [w, hj, ↓reduceIte, mul_assoc]
      rw [sub_mul, one_mul, he.eq, sub_self, mul_zero]
  let x : n → principalModule (S := S) A e := fun i ↦
    ⟨B (i, i0), ⟨a (i, i0), by simp [hB, w]⟩⟩
  have hxcoe (i : n) : (x i : A) = B (i, i0) := rfl
  have hli : LinearIndependent S x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hc' : ∑ j, c j • B (j, i0) = 0 := by
      have hc' := congrArg
        (Submodule.subtype (principalModule (S := S) A e)) hc
      rw [map_sum] at hc'
      simp only [map_smul, map_zero] at hc'
      change (∑ j, c j • (x j : A)) = 0 at hc'
      simpa only [hxcoe] using hc'
    have hcoord := congrArg (fun z : A ↦ B.repr z (i, i0)) hc'
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
      Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply] at hcoord
    rw [Finset.sum_eq_single i] at hcoord
    · simpa using hcoord
    · intro j _ hji
      simp [hji]
    · simp
  have hfixed (y : principalModule (S := S) A e) : y.1 * e = y.1 := by
    obtain ⟨z, hz⟩ := y.2
    change z * e = y.1 at hz
    rw [← hz, mul_assoc, he.eq]
  have hspan : Submodule.span S (Set.range x) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y = ∑ i, B.repr y.1 (i, i0) • x i := by
      apply Submodule.injective_subtype
      rw [map_sum]
      simp only [map_smul]
      calc
        y.1 = y.1 * e := (hfixed y).symm
        _ = (∑ ij, B.repr y.1 ij • B ij) * e := by rw [B.sum_repr]
        _ = ∑ ij, B.repr y.1 ij • (B ij * e) := by
          simp only [Finset.sum_mul, Algebra.smul_mul_assoc]
        _ = ∑ ij, if ij.2 = i0 then B.repr y.1 ij • B ij else 0 := by
          apply Finset.sum_congr rfl
          intro ij _
          rw [hBe]
          split <;> simp_all
        _ = ∑ i, B.repr y.1 (i, i0) • B (i, i0) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_eq_single i0]
          · simp
          · intro j _ hj
            simp [hj]
          · simp
    rw [hy]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  let b : Module.Basis n S (principalModule (S := S) A e) := Module.Basis.mk hli hspan.ge
  have hb (i : n) : (b i : A) = B (i, i0) := by simp [b, x]
  have hqB (ij : n × n) : qA (B ij) = Matrix.stdBasis k n n ij := by
    rw [hB, hw]
  have hreprColumn (z : principalModule (S := S) A e) (i : n) :
      qS (b.repr z i) = qA z.1 i i0 := by
    have hzA : z.1 = ∑ j, b.repr z j • (b j : A) := by
      have hzA := congrArg (Submodule.subtype (principalModule (S := S) A e))
        (b.sum_repr z)
      rw [map_sum] at hzA
      simp only [map_smul] at hzA
      exact hzA.symm
    have hz : qA z.1 = ∑ j, qS (b.repr z j) • Matrix.single j i0 1 := by
      calc
        qA z.1 = qA (∑ j, b.repr z j • (b j : A)) := congrArg qA hzA
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [hscalar, hb, hqB, Matrix.stdBasis_eq_single]
    let ev : Matrix n n k →ₗ[k] k := {
      toFun M := M i i0
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    have hzentry := congrArg ev hz
    rw [map_sum] at hzentry
    simp only [map_smul] at hzentry
    change qA z.1 i i0 =
      ∑ j, qS (b.repr z j) * Matrix.single j i0 (1 : k) i i0 at hzentry
    rw [Finset.sum_eq_single i] at hzentry
    · simpa [Matrix.single] using hzentry.symm
    · intro j _ hji
      simp [Matrix.single, hji]
    · simp
  let f : n × n → Module.End S (principalModule (S := S) A e) := fun ij ↦
    principalLeftAction e (B ij)
  have hstd (M : Matrix n n S) (r l : n) :
      (Matrix.stdBasis S n n).repr M (r, l) = M r l := by
    have hsingle (i j : n) : Matrix.single i j (M i j) =
        M i j • Matrix.stdBasis S n n (i, j) := by
      ext a c
      simp [Matrix.stdBasis_eq_single, Matrix.single]
    have hM : M = ∑ i, ∑ j, M i j • Matrix.stdBasis S n n (i, j) := by
      calc
        M = ∑ i, ∑ j, Matrix.single i j (M i j) := Matrix.matrix_eq_sum_single M
        _ = _ := by simp_rw [hsingle]
    conv_lhs => rw [hM]
    rw [map_sum]
    simp only [map_sum, map_smul, Module.Basis.repr_self,
      Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single l]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · intro i _ hir
      simp [hir]
    · simp
  have hend (T : Module.End S (principalModule (S := S) A e)) (r l : n) :
      (b.end).repr T (r, l) = b.repr (T (b l)) r := by
    rw [Module.Basis.end_repr_apply, hstd, LinearMap.toMatrix_apply]
  have hfres (ij kl : n × n) :
      qS ((b.end).repr (f ij) kl) = Matrix.stdBasis k n n ij kl.1 kl.2 := by
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨r, l⟩
    change qS ((b.end).repr (f (i, j)) (r, l)) = Matrix.stdBasis k n n (i, j) r l
    rw [hend]
    rw [hreprColumn]
    change qA (B (i, j) * (b l : A)) r i0 = _
    rw [hb, map_mul, hqB, hqB]
    simp [Matrix.stdBasis_eq_single, Matrix.single, Matrix.mul_apply]
  have hmatrix : ((b.end).toMatrix f).map qS = 1 := by
    ext ij kl
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply, hfres]
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨r, l⟩
    simp [Matrix.stdBasis_eq_single, Matrix.single, Matrix.one_apply, eq_comm]
  have hdetres : qS ((b.end).det f) = 1 := by
    rw [Module.Basis.det_apply, RingHom.map_det, RingHom.mapMatrix_apply, hmatrix,
      Matrix.det_one]
  have hdet : IsUnit ((b.end).det f) := by
    by_contra hunit
    have hm : (b.end).det f ∈ maximalIdeal S :=
      (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
    have hz : qS ((b.end).det f) = 0 := RingHom.mem_ker.mp (hkerS.symm ▸ hm)
    rw [hdetres] at hz
    exact one_ne_zero hz
  obtain ⟨hliF, hspanF⟩ := ((b.end).is_basis_iff_det (v := f)).mpr hdet
  let F : Module.Basis (n × n) S (Module.End S (principalModule (S := S) A e)) :=
    Module.Basis.mk hliF hspanF.ge
  have hF (ij : n × n) : F ij = f ij := by simp [F]
  let L := (principalLeftAction (S := S) e).toLinearMap
  have hreprAction (z : A) : F.repr (L z) = B.repr z := by
    have hz : L z = ∑ kl, B.repr z kl • F kl := by
      calc
        L z = L (∑ kl, B.repr z kl • B kl) :=
          congrArg L (B.sum_repr z).symm
        _ = ∑ kl, B.repr z kl • L (B kl) := by rw [map_sum]; simp
        _ = ∑ kl, B.repr z kl • F kl := by
          apply Finset.sum_congr rfl
          intro kl _
          rw [hF]
          rfl
    rw [hz, map_sum]
    apply Finsupp.ext
    intro ij
    simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
      Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single ij]
    · simp
    · intro kl _ hne
      simp [hne]
    · simp
  have hL : Function.Bijective L := by
    constructor
    · intro z z' hzz'
      apply B.repr.injective
      rw [← hreprAction, ← hreprAction, hzz']
    · intro y
      let z : A := B.equivFun.symm (F.repr y)
      refine ⟨z, F.repr.injective ?_⟩
      rw [hreprAction]
      simp [z]
  exact ⟨e, he, B, b, hL, hb, hqB⟩

end Representation.MoritaReconstruction

namespace Deformation.MoritaReconstruction

set_option maxHeartbeats 4000000 in
-- The combined existence proof elaborates every determinant argument in this file.
set_option synthInstance.maxHeartbeats 500000 in
-- Assembling all universal data requires several large nested instance and determinant proofs.
/-- Universal Morita data, including a strict evaluation basis for the universal framed lift. -/
theorem exists_universalMoritaData
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (n : Type) [Fintype n] [DecidableEq n]
    [Finite (ResidueField O)]
    (rho : G →ₜ* GL n (ProartinianCat.residueField (𝓞 := O)))
    [(residualLinearRepresentation O G n rho).IsAbsolutelyIrreducible.{u}] :
    ∃ (e : UniversalImageAlgebra O G n rho), IsIdempotentElem e ∧
      ∃ b : Module.Basis n (UniversalTraceRing O G n rho)
          (Representation.MoritaReconstruction.principalModule
            (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e),
        Function.Bijective (Representation.MoritaReconstruction.principalLeftAction
          (S := UniversalTraceRing O G n rho) e) ∧
          ∃ (v : n → ProfiniteFramedLimit O G n rho)
            (c : Module.Basis n (ProfiniteFramedLimit O G n rho)
              (n → ProfiniteFramedLimit O G n rho)),
            (∀ i, c i = Representation.MoritaReconstruction.principalEvaluation
              (universalLinearRepresentation O G n rho) e v (b i)) ∧
              ∀ i j, framedResidueRingHom O G n rho (c i j) =
                (Pi.single i (1 : ResidueField O) : n → ResidueField O) j := by
  classical
  let k := ProartinianCat.residueField (𝓞 := O)
  have hntriv : Nontrivial (n → k) := by
    have hirrBase : (Representation.baseChange k
        (residualLinearRepresentation O G n rho)).IsIrreducible :=
      Representation.IsAbsolutelyIrreducible.absolutelyIrreducible
        (ρ := residualLinearRepresentation O G n rho) k inferInstance inferInstance
    have hirr : (residualLinearRepresentation O G n rho).IsIrreducible :=
      Slop.OddRep.isIrreducible_of_baseChange
        (residualLinearRepresentation O G n rho) k hirrBase
    let _ : IsSimpleModule (MonoidAlgebra k G)
        (residualLinearRepresentation O G n rho).asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule
        (residualLinearRepresentation O G n rho)).mp hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra k G)
      (residualLinearRepresentation O G n rho).asModule
  have hn : Nonempty n := by
    rcases isEmpty_or_nonempty n with hn | hn
    · let _ := hn
      let _ : Nontrivial (n → k) := hntriv
      exact (not_subsingleton (n → k) inferInstance).elim
    · exact hn
  let _ : Nonempty n := hn
  let i0 : n := hn.some
  obtain ⟨ι, hι, hdec, _g, bR, bA, _hbR⟩ :=
    exists_universalTraceImageAlgebra_basis O G n rho
  let _ : Fintype ι := hι
  let _ : DecidableEq ι := hdec
  let _ : IsLocalProartinianAlgebra O (ProfiniteFramedLimit O G n rho) :=
    (profiniteFramedLimitObject O G n rho).isLocalProartinianAlgebra
  let eι : ι ≃ n × n := bR.indexEquiv
    (Matrix.stdBasis (ProfiniteFramedLimit O G n rho) n n)
  have hcard : Fintype.card ι = Fintype.card (n × n) := Fintype.card_congr eι
  let b0 : Module.Basis (n × n) (UniversalTraceRing O G n rho)
      (UniversalImageAlgebra O G n rho) := bA.reindex eι
  have hsurj := universalImageResidue_surjective O G n rho
  have hker := universalImageResidue_ker O G n rho bA hcard hsurj
  let qA := universalImageResidue O G n rho
  have hle : CompatibleIdempotent.extendedIdeal
      (A := UniversalImageAlgebra O G n rho)
      (maximalIdeal (UniversalTraceRing O G n rho)) ≤ RingHom.ker qA := by
    rw [← hker]
  let qbar : ((UniversalImageAlgebra O G n rho) ⧸
      CompatibleIdempotent.extendedIdeal
        (A := UniversalImageAlgebra O G n rho)
        (maximalIdeal (UniversalTraceRing O G n rho))) →+*
      Matrix n n k := Ideal.Quotient.lift _ qA
        fun a ha ↦ RingHom.mem_ker.mp (hle ha)
  have hqbar_surj : Function.Surjective qbar := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    change qA x = qA x
    rfl
  have hqbar_inj : Function.Injective qbar := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.2
    rw [show qbar (Ideal.Quotient.mk _ x) = qA x from rfl,
      show qbar (Ideal.Quotient.mk _ y) = qA y from rfl] at hxy
    have hmem : x - y ∈ RingHom.ker qA := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    rw [hker] at hmem
    exact hmem
  let qbarEquiv := RingEquiv.ofBijective qbar ⟨hqbar_inj, hqbar_surj⟩
  let ebar : Matrix n n k := Matrix.single i0 i0 1
  have hebar : IsIdempotentElem ebar := by
    rw [IsIdempotentElem]
    simp [ebar]
  let equot := qbarEquiv.symm ebar
  have hequot : IsIdempotentElem equot := hebar.map qbarEquiv.symm
  let _ : Algebra (universalTraceRingObject O G n rho)
      (UniversalImageAlgebra O G n rho) := by
    change Algebra (UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho)
    infer_instance
  obtain ⟨e, he, heq⟩ := CompatibleIdempotent.exists_isIdempotentElem_lift_residue
    (universalTraceRingObject O G n rho) bA equot hequot
  have hqe : qA e = ebar := by
    have h := congrArg qbar heq
    change qA e = qbar equot at h
    have hebar' := qbarEquiv.apply_symm_apply ebar
    change qbar equot = ebar at hebar'
    exact h.trans hebar'
  let qS : UniversalTraceRing O G n rho →+* k :=
    (ProartinianCat.toResidueField
      (universalTraceRingObject O G n rho)).hom.toRingHom
  have hkerS : RingHom.ker qS = maximalIdeal (UniversalTraceRing O G n rho) :=
    ProartinianCat.ker_toResidueField (universalTraceRingObject O G n rho)
  have hscalar : ∀ s x, qA (s • x) = qS s • qA x := by
    intro s x
    have h := universalImageResidue_smul O G n rho s x
    have hmul : universalImageScalarMul O G n rho s x = s • x := by
      apply Subtype.ext
      unfold universalImageScalarMul
      rw [Algebra.smul_def]
      rfl
    rw [hmul] at h
    exact h
  obtain ⟨e', he', B, b, hMorita, hb, hqB⟩ :=
    Representation.MoritaReconstruction.exists_matrix_idempotent_data
      (S := UniversalTraceRing O G n rho)
      (A := UniversalImageAlgebra O G n rho) (k := k) (n := n)
      b0 qS (ProartinianCat.toResidueField_surjective
        (universalTraceRingObject O G n rho)) hkerS qA hsurj hscalar hker i0 e he hqe
  let R := ProfiniteFramedLimit O G n rho
  let qR : R →+* k := framedResidueRingHom O G n rho
  let v : n → R := Pi.single i0 1
  let eval : n → (n → R) := fun i ↦
    Representation.MoritaReconstruction.principalEvaluation
      (universalLinearRepresentation O G n rho) e' v (b i)
  have hmatrix (i : n) : ((b i).1.1 : Matrix n n R).map qR =
      Matrix.stdBasis k n n (i, i0) := by
    calc
      _ = qA ((b i : Representation.MoritaReconstruction.principalModule
          (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e').1) := rfl
      _ = qA (B (i, i0)) := congrArg qA (hb i)
      _ = _ := hqB (i, i0)
  have heval (i j : n) : qR (eval i j) = (Pi.single i (1 : k) : n → k) j := by
    have h := congrArg (fun M : Matrix n n k ↦ M.mulVec (Pi.single i0 1) j) (hmatrix i)
    simpa [eval, v, Representation.MoritaReconstruction.principalEvaluation,
      RingHom.map_mulVec, Matrix.stdBasis_eq_single, Matrix.single_mulVec,
      Matrix.single, Pi.single_apply, eq_comm] using h
  let bstd : Module.Basis n R (n → R) := Pi.basisFun R n
  have hcoordMatrix : (Matrix.of eval).map qR = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.of_apply, heval]
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  have hdetres : qR (bstd.det eval) = 1 := by
    rw [Pi.basisFun_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, hcoordMatrix,
      Matrix.det_one]
  have hkerR : RingHom.ker qR = maximalIdeal R := by
    exact ProartinianCat.ker_toResidueField (profiniteFramedLimitObject O G n rho)
  have hdeteval : IsUnit (bstd.det eval) := by
    by_contra hunit
    have hm : bstd.det eval ∈ maximalIdeal R :=
      (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
    have hz : qR (bstd.det eval) = 0 := RingHom.mem_ker.mp (hkerR.symm ▸ hm)
    rw [hdetres] at hz
    exact one_ne_zero hz
  obtain ⟨hlieval, hspaneval⟩ := (bstd.is_basis_iff_det (v := eval)).mpr hdeteval
  let c : Module.Basis n R (n → R) := Module.Basis.mk hlieval hspaneval.ge
  have hc (i : n) : c i = eval i := by simp [c]
  exact ⟨e', he', b, hMorita, v, c, fun i ↦ hc i,
    fun i j ↦ by rw [hc]; exact heval i j⟩

set_option maxHeartbeats 4000000 in
-- Continuity through an arbitrary evaluation basis expands two finite matrix products.
set_option synthInstance.maxHeartbeats 100000 in
/-- The representation reconstructed over the universal trace ring is continuous. -/
theorem universalTraceDescendedGL_continuous
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (n : Type) [Fintype n] [DecidableEq n]
    [Finite (ResidueField O)]
    (rho : G →ₜ* GL n (@ProartinianCat.residueField O _ _))
    (e : UniversalImageAlgebra O G n rho)
    (v : n → ProfiniteFramedLimit O G n rho)
    (b : Module.Basis n (UniversalTraceRing O G n rho)
      (Representation.MoritaReconstruction.principalModule
        (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e))
    (c : Module.Basis n (ProfiniteFramedLimit O G n rho)
      (n → ProfiniteFramedLimit O G n rho))
    (hc : ∀ i, c i = Representation.MoritaReconstruction.principalEvaluation
      (universalLinearRepresentation O G n rho) e v (b i)) :
    Continuous (universalTraceDescendedGL O G n rho e b) := by
  let _ : IsLocalProartinianAlgebra O (ProfiniteFramedLimit O G n rho) :=
    (profiniteFramedLimitObject O G n rho).isLocalProartinianAlgebra
  let htop : IsTopologicalRing (ProfiniteFramedLimit O G n rho) :=
    IsLocalProartinianAlgebra.toIsTopologicalRing O
  let _ : IsTopologicalRing (ProfiniteFramedLimit O G n rho) := htop
  let _ : ContinuousAdd (ProfiniteFramedLimit O G n rho) := htop.toContinuousAdd
  let _ : ContinuousMul (ProfiniteFramedLimit O G n rho) := htop.toContinuousMul
  let R := ProfiniteFramedLimit O G n rho
  let bstd : Module.Basis n R (n → R) := Pi.basisFun R n
  have hchange (g : G) :
      LinearMap.toMatrix c c (universalLinearRepresentation O G n rho g) =
        c.toMatrix bstd * profiniteUniversalMatrix O G n rho g * bstd.toMatrix c := by
    calc
      _ = c.toMatrix bstd *
          LinearMap.toMatrix bstd bstd (universalLinearRepresentation O G n rho g) *
          bstd.toMatrix c :=
        (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
          (b := c) (b' := bstd) (c := c) (c' := bstd)
          (f := universalLinearRepresentation O G n rho g)).symm
      _ = _ := by
        rw [show LinearMap.toMatrix bstd bstd
            (universalLinearRepresentation O G n rho g) =
            profiniteUniversalMatrix O G n rho g by
          change Representation.representationMatrix
            (universalLinearRepresentation O G n rho) g = _
          exact universalLinearRepresentation_matrix O G n rho g]
  have hambient : Continuous (fun g : G ↦
      ((↑(universalTraceDescendedGL O G n rho e b g) :
        Matrix n n (UniversalTraceRing O G n rho)).map
          (algebraMap (UniversalTraceRing O G n rho)
            (ProfiniteFramedLimit O G n rho)))) := by
    have hcont : Continuous (fun g : G ↦
        c.toMatrix bstd * profiniteUniversalMatrix O G n rho g * bstd.toMatrix c) := by
      apply continuous_matrix
      intro i j
      simp only [Matrix.mul_apply]
      apply continuous_finsetSum _
      intro k _
      apply Continuous.mul
      · apply continuous_finsetSum _
        intro l _
        exact continuous_const.mul ((continuous_apply k).comp
          ((continuous_apply l).comp
            (profiniteUniversalMatrix_continuous O G n rho)))
      · exact continuous_const
    convert hcont using 1
    funext g
    rw [← hchange]
    exact universalTraceDescendedGL_conjugate O G n rho e v b c hc g
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    apply continuous_induced_rng.mpr
    exact (continuous_apply j).comp ((continuous_apply i).comp hambient)
  · apply continuous_matrix
    intro i j
    apply continuous_induced_rng.mpr
    have hinv := hambient.comp continuous_inv
    exact (continuous_apply j).comp ((continuous_apply i).comp hinv)

set_option synthInstance.maxHeartbeats 100000 in
-- Lean v4.35 needs extra time to synthesize the module structure through the trace-ring aliases.
/-- The reconstructed representation has the universal trace. -/
theorem universalTraceDescendedGL_trace
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (n : Type) [Fintype n] [DecidableEq n]
    [Finite (ResidueField O)]
    (rho : G →ₜ* GL n (@ProartinianCat.residueField O _ _))
    (e : UniversalImageAlgebra O G n rho)
    (v : n → ProfiniteFramedLimit O G n rho)
    (b : Module.Basis n (UniversalTraceRing O G n rho)
      (Representation.MoritaReconstruction.principalModule
        (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e))
    (c : Module.Basis n (ProfiniteFramedLimit O G n rho)
      (n → ProfiniteFramedLimit O G n rho))
    (hc : ∀ i, c i = Representation.MoritaReconstruction.principalEvaluation
      (universalLinearRepresentation O G n rho) e v (b i)) (g : G) :
    Matrix.trace (↑(universalTraceDescendedGL O G n rho e b g) :
      Matrix n n (UniversalTraceRing O G n rho)) =
        ⟨(profiniteUniversalMatrix O G n rho g).trace,
          universalTrace_mem O G n rho g⟩ := by
  let _ : IsLocalProartinianAlgebra O (ProfiniteFramedLimit O G n rho) :=
    (profiniteFramedLimitObject O G n rho).isLocalProartinianAlgebra
  let R := ProfiniteFramedLimit O G n rho
  let bstd : Module.Basis n R (n → R) := Pi.basisFun R n
  apply Subtype.ext
  change algebraMap (UniversalTraceRing O G n rho) R
      (Matrix.trace (↑(universalTraceDescendedGL O G n rho e b g) :
        Matrix n n (UniversalTraceRing O G n rho))) =
      (profiniteUniversalMatrix O G n rho g).trace
  rw [AddMonoidHom.map_trace]
  rw [universalTraceDescendedGL_conjugate O G n rho e v b c hc g]
  calc
    Matrix.trace (LinearMap.toMatrix c c
        (universalLinearRepresentation O G n rho g)) =
        LinearMap.traceAux R c (universalLinearRepresentation O G n rho g) := rfl
    _ = LinearMap.traceAux R bstd (universalLinearRepresentation O G n rho g) := by
      exact DFunLike.congr_fun (LinearMap.traceAux_eq (R := R) c bstd)
        (universalLinearRepresentation O G n rho g)
    _ = Matrix.trace (LinearMap.toMatrix bstd bstd
        (universalLinearRepresentation O G n rho g)) := rfl
    _ = _ := by
      rw [show LinearMap.toMatrix bstd bstd
          (universalLinearRepresentation O G n rho g) =
          profiniteUniversalMatrix O G n rho g by
        change Representation.representationMatrix
          (universalLinearRepresentation O G n rho) g = _
        exact universalLinearRepresentation_matrix O G n rho g]

set_option synthInstance.maxHeartbeats 100000 in
-- Lean v4.35 needs extra time to synthesize the module structure through the trace-ring aliases.
/-- The evaluation basis gives a change-of-basis matrix reducing to the identity and conjugating
the scalar extension of the reconstructed representation to the universal framed lift. -/
theorem exists_strict_universalTraceDescendedGL_conjugator
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G]
    (n : Type) [Fintype n] [DecidableEq n]
    [Finite (ResidueField O)]
    (rho : G →ₜ* GL n (@ProartinianCat.residueField O _ _))
    (e : UniversalImageAlgebra O G n rho)
    (v : n → ProfiniteFramedLimit O G n rho)
    (b : Module.Basis n (UniversalTraceRing O G n rho)
      (Representation.MoritaReconstruction.principalModule
        (S := UniversalTraceRing O G n rho) (UniversalImageAlgebra O G n rho) e))
    (c : Module.Basis n (ProfiniteFramedLimit O G n rho)
      (n → ProfiniteFramedLimit O G n rho))
    (hc : ∀ i, c i = Representation.MoritaReconstruction.principalEvaluation
      (universalLinearRepresentation O G n rho) e v (b i))
    (hstrict : ∀ i j, framedResidueRingHom O G n rho (c i j) =
      (Pi.single i (1 : ResidueField O) : n → ResidueField O) j) :
    ∃ P : GL n (ProfiniteFramedLimit O G n rho),
      Matrix.GeneralLinearGroup.map (framedResidueRingHom O G n rho) P = 1 ∧
        ∀ g, P * Matrix.GeneralLinearGroup.map
          (algebraMap (UniversalTraceRing O G n rho)
            (ProfiniteFramedLimit O G n rho))
          (universalTraceDescendedGL O G n rho e b g) * P⁻¹ =
            profiniteUniversalLift O G n rho g := by
  let _ : IsLocalProartinianAlgebra O (ProfiniteFramedLimit O G n rho) :=
    (profiniteFramedLimitObject O G n rho).isLocalProartinianAlgebra
  let R := ProfiniteFramedLimit O G n rho
  let bstd : Module.Basis n R (n → R) := Pi.basisFun R n
  let P : GL n R :=
    { val := bstd.toMatrix c
      inv := c.toMatrix bstd
      val_inv := Module.Basis.toMatrix_mul_toMatrix_flip bstd c
      inv_val := Module.Basis.toMatrix_mul_toMatrix_flip c bstd }
  have hP_res : Matrix.GeneralLinearGroup.map (framedResidueRingHom O G n rho) P = 1 := by
    apply Units.ext
    ext i j
    change framedResidueRingHom O G n rho (c j i) =
      (1 : Matrix n n (ResidueField O)) i j
    rw [hstrict]
    simp only [Pi.single_apply, Matrix.one_apply]
    rfl
  refine ⟨P, hP_res, fun g ↦ ?_⟩
  apply Units.ext
  change bstd.toMatrix c *
      ((↑(universalTraceDescendedGL O G n rho e b g) :
        Matrix n n (UniversalTraceRing O G n rho)).map
          (algebraMap (UniversalTraceRing O G n rho) R)) *
      c.toMatrix bstd = profiniteUniversalMatrix O G n rho g
  rw [universalTraceDescendedGL_conjugate O G n rho e v b c hc g]
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  change Representation.representationMatrix
    (universalLinearRepresentation O G n rho) g = _
  exact universalLinearRepresentation_matrix O G n rho g

end Deformation.MoritaReconstruction
