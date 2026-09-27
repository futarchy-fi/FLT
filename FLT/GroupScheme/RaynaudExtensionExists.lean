/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatSubobject
public import FLT.GroupScheme.RaynaudExtension

/-!
# The graph construction for Raynaud extension

For a map of geometric Galois modules, `GenericGaloisHom.toBialgHom` constructs
its generic Hopf morphism. `GenericGaloisHom.graphClosure` takes the schematic
closure of its graph in the product of the chosen models. Its two integral
projections recover the identity and the given morphism on generic points.

`exists_generic_graph_span` packages this construction over a Dedekind domain.
The first projection is injective on coordinate rings and bijective after base
change. Proving its integral surjectivity over `ℤ_[3]` requires Raynaud's
small-ramification rigidity theorem; see `BLOCKED.md`. The full extension
existence theorem is not established here.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [PerfectField K]

/-- Evaluation identifies the canonical function algebra on the chosen points
with the generic coordinate Hopf algebra. -/
def FF.genericCoordinates (X : FF R K) :
    (X.Points →[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] AlgebraicClosure K)
      ≃ₐc[K] K ⊗[R] X.CoordinateRing := by
  letI := GaloisModule.GenericFiber.hopfAlgebra K (AlgebraicClosure K) X.Points
  exact BialgEquiv.ofBijective
    (GaloisModule.GenericFiber.canonicalEmbeddingBialgHom K (AlgebraicClosure K)
      (K ⊗[R] X.CoordinateRing) X.Points X.points)
    (GaloisModule.GenericFiber.canonicalEmbeddingAlgHom_bijective K (AlgebraicClosure K)
      (K ⊗[R] X.CoordinateRing) X.Points X.points X.points_bijective)

/-- Evaluation of the coordinate comparison is evaluation at the chosen point. -/
theorem FF.eval_genericCoordinates (X : FF R K)
    (a : X.Points →[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] AlgebraicClosure K)
    (p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) :
    p (X.genericCoordinates a) = a (X.points (Additive.ofMul p)) :=
  GaloisModule.GenericFiber.eval_canonicalEmbeddingAlgHom K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing) X.Points X.points a p

/-- A generic Galois morphism determines a contravariant morphism of generic Hopf algebras. -/
def GenericGaloisHom.toBialgHom {X Y : FF R K} (f : GenericGaloisHom X Y) :
    K ⊗[R] Y.CoordinateRing →ₐc[K] K ⊗[R] X.CoordinateRing := by
  letI := GaloisModule.GenericFiber.hopfAlgebra K (AlgebraicClosure K) Y.Points
  exact (GaloisModule.GenericFiber.canonicalEmbeddingBialgHom K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing) Y.Points (f.comp X.points)).comp
      Y.genericCoordinates.symm.toBialgHom

/-- The constructed generic Hopf map induces exactly the prescribed map of points. -/
theorem GenericGaloisHom.toBialgHom_points {X Y : FF R K} (f : GenericGaloisHom X Y)
    (p : Additive (K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K)) :
    Y.points (BialgHom.precompPoints f.toBialgHom p) = f (X.points p) := by
  let q := Y.inversePoints (f (X.points p))
  have hq : Y.points q = f (X.points p) := Y.pointsEquiv.apply_symm_apply _
  suffices h : BialgHom.precompPoints f.toBialgHom p = q by rw [h, hq]
  apply Additive.toMul.injective
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Y.genericCoordinates.surjective a
  change p.toMul (f.toBialgHom (Y.genericCoordinates b)) = q.toMul (Y.genericCoordinates b)
  rw [Y.eval_genericCoordinates]
  change _ = b (Y.points q)
  rw [hq]
  change p.toMul (GaloisModule.GenericFiber.canonicalEmbeddingAlgHom K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing) Y.Points (f.comp X.points)
      (Y.genericCoordinates.symm (Y.genericCoordinates b))) = _
  rw [BialgEquiv.symm_apply_apply]
  exact GaloisModule.GenericFiber.eval_canonicalEmbeddingAlgHom K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing) Y.Points (f.comp X.points) b p.toMul

/-- Taking the generic Hopf map of an integral morphism recovers its base change. -/
theorem ModelHom.toBialgHom_genericHom {X Y : FF R K} (f : ModelHom X Y) :
    (genericHom f).toBialgHom = f.baseChange := by
  ext a
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing)).injective
  ext p
  have h := (genericHom f).toBialgHom_points (Additive.ofMul p)
  rw [genericHom_points] at h
  exact AlgHom.congr_fun (congrArg Additive.toMul (Y.points_bijective.1 h)) a

/-- The tensor coordinate algebra models the product of the chosen groups. -/
@[implicit_reducible]
def FF.prod (X Y : FF R K) : FF R K := by
  let H := X.CoordinateRing ⊗[R] Y.CoordinateRing
  letI : HopfAlgebra.IsFiniteFlat R H := ⟨⟩
  letI : Algebra (K ⊗[R] X.CoordinateRing)
      ((K ⊗[R] X.CoordinateRing) ⊗[K] (K ⊗[R] Y.CoordinateRing)) :=
    Algebra.TensorProduct.leftAlgebra
  letI : Algebra.Etale K
      ((K ⊗[R] X.CoordinateRing) ⊗[K] (K ⊗[R] Y.CoordinateRing)) :=
    Algebra.Etale.comp K (K ⊗[R] X.CoordinateRing) _
  letI : Algebra.Etale K (K ⊗[R] H) := Algebra.Etale.of_equiv
    (GaloisModule.genericTensorEquiv R K X.CoordinateRing Y.CoordinateRing)
  let p : Additive (K ⊗[R] H →ₐ[K] AlgebraicClosure K) →+[
      AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] (X.Points × Y.Points) :=
    { toFun := fun a ↦
        (X.points (BialgHom.precompPoints
          (GaloisModule.genericTensorIncludeLeft R K X.CoordinateRing Y.CoordinateRing) a),
        Y.points (BialgHom.precompPoints
          (GaloisModule.genericTensorIncludeRight R K X.CoordinateRing Y.CoordinateRing) a))
      map_zero' := by simp
      map_add' := by intro a b; simp
      map_smul' := by intro σ a; simp }
  refine { CoordinateRing := H, Points := X.Points × Y.Points
           points := p, points_bijective := ?_ }
  let e := GaloisModule.genericTensorPointsEquiv R K X.CoordinateRing Y.CoordinateRing
    (AlgebraicClosure K)
  have he (a : K ⊗[R] H →ₐ[K] AlgebraicClosure K) :
      p (Additive.ofMul a) =
        (X.points (Additive.ofMul (e a).1), Y.points (Additive.ofMul (e a).2)) := by
    apply Prod.ext
    · change X.points _ = X.points _
      apply congrArg X.points
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      change a (GaloisModule.genericTensorIncludeLeft R K
        X.CoordinateRing Y.CoordinateRing x) = (e a).1 x
      induction x using TensorProduct.inductionOn with
      | tmul k x =>
        simp [e, GaloisModule.genericTensorPointsEquiv, GaloisModule.genericTensorEquiv,
          GaloisModule.commutingPairEquiv, GaloisModule.genericTensorIncludeLeft,
          GaloisModule.tensorIncludeLeft, Algebra.TensorProduct.one_def]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    · change Y.points _ = Y.points _
      apply congrArg Y.points
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      change a (GaloisModule.genericTensorIncludeRight R K
        X.CoordinateRing Y.CoordinateRing x) = (e a).2 x
      induction x using TensorProduct.inductionOn with
      | tmul k x =>
        simp [e, GaloisModule.genericTensorPointsEquiv, GaloisModule.genericTensorEquiv,
          GaloisModule.commutingPairEquiv, GaloisModule.genericTensorIncludeRight,
          GaloisModule.tensorIncludeRight, Algebra.TensorProduct.one_def]
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  constructor
  · intro a b hab
    apply Additive.toMul.injective
    apply e.injective
    change p (Additive.ofMul a.toMul) = p (Additive.ofMul b.toMul) at hab
    rw [he a.toMul, he b.toMul] at hab
    exact Prod.ext (X.points_bijective.1 (congrArg Prod.fst hab))
      (Y.points_bijective.1 (congrArg Prod.snd hab))
  · rintro ⟨x, y⟩
    refine ⟨Additive.ofMul (e.symm ((X.inversePoints x).toMul, (Y.inversePoints y).toMul)), ?_⟩
    rw [he, e.apply_symm_apply]
    exact Prod.ext (X.pointsEquiv.apply_symm_apply x) (Y.pointsEquiv.apply_symm_apply y)

/-- Projection to the first chosen model. -/
def FF.fst (X Y : FF R K) : ModelHom (X.prod Y) X :=
  GaloisModule.tensorIncludeLeft R X.CoordinateRing Y.CoordinateRing

/-- Projection to the second chosen model. -/
def FF.snd (X Y : FF R K) : ModelHom (X.prod Y) Y :=
  GaloisModule.tensorIncludeRight R X.CoordinateRing Y.CoordinateRing

omit [PerfectField K] in
/-- The first integral projection induces the first projection on chosen points. -/
@[simp] theorem FF.genericHom_fst (X Y : FF R K) (p : (X.prod Y).Points) :
    genericHom (X.fst Y) p = p.1 := by
  obtain ⟨a, rfl⟩ := (X.prod Y).points_bijective.2 p
  rw [genericHom_points]
  rfl

omit [PerfectField K] in
/-- The second integral projection induces the second projection on chosen points. -/
@[simp] theorem FF.genericHom_snd (X Y : FF R K) (p : (X.prod Y).Points) :
    genericHom (X.snd Y) p = p.2 := by
  obtain ⟨a, rfl⟩ := (X.prod Y).points_bijective.2 p
  rw [genericHom_points]
  rfl

/-- An embedding of geometric point groups gives a surjection on generic coordinate rings. -/
theorem GenericGaloisHom.toBialgHom_surjective {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Injective f) : Function.Surjective f.toBialgHom := by
  change Function.Surjective (fun a ↦
    GaloisModule.GenericFiber.canonicalEmbeddingAlgHom K (AlgebraicClosure K)
      (K ⊗[R] X.CoordinateRing) Y.Points (f.comp X.points) (Y.genericCoordinates.symm a))
  apply Function.Surjective.comp _ Y.genericCoordinates.symm.surjective
  apply (GaloisModule.GenericFiber.genericEvalAlgEquiv K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing)).symm.surjective.comp
  apply MulActionHom.compLeftAlgHom_surjective_of_injective (S := K)
  intro p q hpq
  exact X.points_bijective.1 (hf hpq)

/-- A surjection on geometric points gives an injection on generic coordinate rings. -/
theorem GenericGaloisHom.toBialgHom_injective {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Surjective f) : Function.Injective f.toBialgHom := by
  change Function.Injective (fun a ↦
    GaloisModule.GenericFiber.canonicalEmbeddingAlgHom K (AlgebraicClosure K)
      (K ⊗[R] X.CoordinateRing) Y.Points (f.comp X.points) (Y.genericCoordinates.symm a))
  exact (GaloisModule.GenericFiber.canonicalEmbeddingAlgHom_injective K (AlgebraicClosure K)
    (K ⊗[R] X.CoordinateRing) Y.Points (f.comp X.points)
      (hf.comp X.points_bijective.2)).comp Y.genericCoordinates.symm.injective

omit [PerfectField K] in
/-- Base change respects composition of integral morphisms. -/
theorem ModelHom.baseChange_comp {X Y Z : FF R K} (f : ModelHom X Y) (g : ModelHom Y Z) :
    ModelHom.baseChange (X := X) (Y := Z) (f.comp g) =
      f.baseChange.comp g.baseChange := by
  ext a
  induction a using TensorProduct.inductionOn with
  | tmul k a => rfl
  | add a b ha hb => simpa using congrArg₂ (· + ·) ha hb

omit [PerfectField K] in
/-- Restriction to geometric points respects composition of integral morphisms. -/
theorem genericHom_comp {X Y Z : FF R K} (f : ModelHom X Y) (g : ModelHom Y Z)
    (x : X.Points) : genericHom (f.comp g) x = genericHom g (genericHom f x) := by
  obtain ⟨p, rfl⟩ := X.points_bijective.2 x
  rw [genericHom_points, genericHom_points, genericHom_points, ModelHom.baseChange_comp]
  rfl

/-- A generic isomorphism on points is a generic isomorphism of coordinate Hopf algebras. -/
theorem ModelHom.baseChange_bijective {X Y : FF R K} (f : ModelHom X Y)
    (hf : Function.Bijective (genericHom f)) : Function.Bijective f.baseChange := by
  rw [← f.toBialgHom_genericHom]
  exact ⟨(genericHom f).toBialgHom_injective hf.2, (genericHom f).toBialgHom_surjective hf.1⟩

variable [IsDedekindDomain R] [IsFractionRing R K]

omit [PerfectField K] [IsDedekindDomain R] in
/-- Flatness detects injectivity of an integral coordinate map on its generic fibre. -/
theorem ModelHom.injective_of_baseChange_injective {X Y : FF R K} (f : ModelHom X Y)
    (hf : Function.Injective f.baseChange) : Function.Injective f := by
  intro x y hxy
  apply Algebra.TensorProduct.includeRight_injective (A := K)
    (IsFractionRing.injective R K)
  apply hf
  change (1 ⊗ₜ[R] f x : K ⊗[R] X.CoordinateRing) = 1 ⊗ₜ[R] f y
  rw [hxy]

/-- The integral equations of the schematic image of a generic morphism. -/
def GenericGaloisHom.closureIdeal {X Y : FF R K} (f : GenericGaloisHom X Y) :
    Ideal Y.CoordinateRing :=
  HopfAlgebra.SchematicClosure.ideal R K Y.CoordinateRing (K ⊗[R] X.CoordinateRing)
    f.toBialgHom

/-- The equations of the schematic image form a Hopf ideal. -/
instance GenericGaloisHom.closureIdealIsHopfIdeal {X Y : FF R K} (f : GenericGaloisHom X Y) :
    f.closureIdeal.IsHopfIdeal R :=
  HopfAlgebra.SchematicClosure.isHopfIdeal R K Y.CoordinateRing
    (K ⊗[R] X.CoordinateRing) f.toBialgHom

/-- The schematic image is finite flat. -/
instance GenericGaloisHom.closureFiniteFlat {X Y : FF R K} (f : GenericGaloisHom X Y) :
    HopfAlgebra.IsFiniteFlat R (Y.CoordinateRing ⧸ f.closureIdeal) :=
  HopfAlgebra.SchematicClosure.isFiniteFlat R K Y.CoordinateRing
    (K ⊗[R] X.CoordinateRing) f.toBialgHom inferInstance

/-- For an embedded generic subgroup, closure recovers its prescribed generic Hopf algebra. -/
def GenericGaloisHom.closureGenericEquiv {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Injective f) :
    K ⊗[R] (Y.CoordinateRing ⧸ f.closureIdeal) ≃ₐc[K] K ⊗[R] X.CoordinateRing :=
  BialgEquiv.ofBijective
    (HopfAlgebra.SchematicClosure.genericBialgHom R K Y.CoordinateRing
      (K ⊗[R] X.CoordinateRing) f.toBialgHom)
    ⟨HopfAlgebra.SchematicClosure.genericMap_injective R K Y.CoordinateRing
      (K ⊗[R] X.CoordinateRing) f.toBialgHom,
      HopfAlgebra.SchematicClosure.genericMap_surjective R K Y.CoordinateRing
        (K ⊗[R] X.CoordinateRing) f.toBialgHom (f.toBialgHom_surjective hf)⟩

/-- The schematic closure, retaining its original generic point group. -/
@[implicit_reducible]
def GenericGaloisHom.closure {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Injective f) : FF R K := by
  let e := f.closureGenericEquiv hf
  letI : Algebra.Etale K (K ⊗[R] (Y.CoordinateRing ⧸ f.closureIdeal)) :=
    Algebra.Etale.of_equiv e.symm.toAlgEquiv
  let a := BialgHom.precompPoints (L := AlgebraicClosure K) e.symm.toBialgHom
  have ha : Function.Bijective a := by
    constructor
    · intro b c hbc
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      obtain ⟨y, rfl⟩ := e.symm.surjective x
      exact AlgHom.congr_fun (congrArg Additive.toMul hbc) y
    · intro b
      refine ⟨Additive.ofMul (b.toMul.comp e.toAlgEquiv.toAlgHom), ?_⟩
      apply Additive.toMul.injective
      apply AlgHom.ext
      intro x
      exact congrArg b.toMul (e.apply_symm_apply x)
  exact { CoordinateRing := Y.CoordinateRing ⧸ f.closureIdeal, Points := X.Points
          points := X.points.comp a, points_bijective := X.points_bijective.comp ha }

/-- The closed immersion from the schematic closure into the ambient model. -/
def GenericGaloisHom.closureInclusion {X Y : FF R K} (f : GenericGaloisHom X Y)
    (hf : Function.Injective f) : ModelHom (f.closure hf) Y :=
  Bialgebra.Quotient.mkBialgHom f.closureIdeal

/-- The closure inclusion recovers the specified generic embedding. -/
theorem GenericGaloisHom.genericHom_closureInclusion {X Y : FF R K}
    (f : GenericGaloisHom X Y) (hf : Function.Injective f) (x : X.Points) :
    genericHom (f.closureInclusion hf) x = f x := by
  obtain ⟨p, rfl⟩ := (f.closure hf).points_bijective.2 x
  rw [genericHom_points]
  change Y.points (BialgHom.precompPoints (f.closureInclusion hf).baseChange p) =
    f (X.points (BialgHom.precompPoints (f.closureGenericEquiv hf).symm.toBialgHom p))
  rw [← f.toBialgHom_points]
  congr 1
  apply Additive.toMul.injective
  apply AlgHom.ext
  intro a
  change p.toMul ((f.closureInclusion hf).baseChange a) =
    p.toMul ((f.closureGenericEquiv hf).symm (f.toBialgHom a))
  congr 1
  apply (f.closureGenericEquiv hf).injective
  exact (AlgHom.congr_fun (HopfAlgebra.SchematicClosure.genericMap_comp_projection R K
    Y.CoordinateRing (K ⊗[R] X.CoordinateRing) f.toBialgHom) a).trans
      ((f.closureGenericEquiv hf).apply_symm_apply _).symm

/-- The generic graph embedding into the product of the chosen point groups. -/
def GenericGaloisHom.graph {X Y : FF R K} (f : GenericGaloisHom X Y) :
    GenericGaloisHom X (X.prod Y) where
  toFun x := (x, f x)
  map_zero' := by change (0, f 0) = (0, 0); rw [map_zero]
  map_add' x y := by change (x + y, f (x + y)) = (x + y, f x + f y); rw [map_add]
  map_smul' σ x := by change (σ • x, f (σ • x)) = (σ • x, σ • f x); rw [map_smul]

omit [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K] in
/-- A graph is embedded because its first projection is the identity. -/
theorem GenericGaloisHom.graph_injective {X Y : FF R K} (f : GenericGaloisHom X Y) :
    Function.Injective f.graph := fun _ _ h ↦ congrArg Prod.fst h

/-- The finite flat schematic closure of the generic graph. -/
@[implicit_reducible]
def GenericGaloisHom.graphClosure {X Y : FF R K} (f : GenericGaloisHom X Y) : FF R K :=
  f.graph.closure f.graph_injective

/-- The integral first projection from the graph closure to the source model. -/
def GenericGaloisHom.graphFst {X Y : FF R K} (f : GenericGaloisHom X Y) :
    ModelHom f.graphClosure X :=
  (f.graph.closureInclusion f.graph_injective).comp (X.fst Y)

/-- The integral second projection from the graph closure to the target model. -/
def GenericGaloisHom.graphSnd {X Y : FF R K} (f : GenericGaloisHom X Y) :
    ModelHom f.graphClosure Y :=
  (f.graph.closureInclusion f.graph_injective).comp (X.snd Y)

/-- The first graph projection is the identity on the chosen generic points. -/
@[simp] theorem GenericGaloisHom.genericHom_graphFst {X Y : FF R K}
    (f : GenericGaloisHom X Y) (x : X.Points) : genericHom f.graphFst x = x := by
  change genericHom ((f.graph.closureInclusion f.graph_injective).comp (X.fst Y)) x = x
  rw [genericHom_comp, FF.genericHom_fst, GenericGaloisHom.genericHom_closureInclusion]
  rfl

/-- The second graph projection is the given morphism on the chosen generic points. -/
@[simp] theorem GenericGaloisHom.genericHom_graphSnd {X Y : FF R K}
    (f : GenericGaloisHom X Y) (x : X.Points) : genericHom f.graphSnd x = f x := by
  change genericHom ((f.graph.closureInclusion f.graph_injective).comp (X.snd Y)) x = f x
  rw [genericHom_comp, FF.genericHom_snd, GenericGaloisHom.genericHom_closureInclusion]
  rfl

/-- The first graph projection becomes an isomorphism over the fraction field. -/
theorem GenericGaloisHom.graphFst_baseChange_bijective {X Y : FF R K}
    (f : GenericGaloisHom X Y) : Function.Bijective f.graphFst.baseChange := by
  apply ModelHom.baseChange_bijective
  constructor
  · intro x y h
    simpa using h
  · intro x
    exact ⟨x, f.genericHom_graphFst x⟩

/-- The first graph projection is injective on integral coordinate rings.
Surjectivity is the remaining small-ramification rigidity step. -/
theorem GenericGaloisHom.graphFst_injective {X Y : FF R K}
    (f : GenericGaloisHom X Y) : Function.Injective f.graphFst :=
  f.graphFst.injective_of_baseChange_injective f.graphFst_baseChange_bijective.1

/-- The graph closure is killed by the same power as its chosen source. -/
theorem GenericGaloisHom.graphClosure_killedByPowerOf {X Y : FF R K}
    (f : GenericGaloisHom X Y) (p : ℕ) (hX : KilledByPowerOf p X) :
    KilledByPowerOf p f.graphClosure := hX

/-- Every generic morphism has an integral graph span with generically invertible first leg.
No ramification assumption is needed to construct this span. -/
theorem exists_generic_graph_span (X Y : FF R K) (f : GenericGaloisHom X Y) :
    ∃ (Z : FF R K) (a : ModelHom Z X) (b : ModelHom Z Y),
      Function.Bijective a.baseChange ∧
      ∀ z : Z.Points, genericHom b z = f (genericHom a z) := by
  exact ⟨f.graphClosure, f.graphFst, f.graphSnd, f.graphFst_baseChange_bijective,
    fun z ↦ by rw [f.genericHom_graphFst, f.genericHom_graphSnd]⟩

end ThreeAdicPlan
