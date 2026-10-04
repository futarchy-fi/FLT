/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralSubquotientExtension
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltration

/-!
# Integral models of an ordinary generic filtration

The submodel is the schematic closure in the given middle model; the quotient
is obtained by contraction. Their point groups keep the original coefficient
module and character actions. Multiplicative/étale integral identifications
are separate arithmetic statements and are not assumed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open GaloisRepresentation.Extensions
namespace ThreeAdicPlan

variable {R K k : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  [IsPrincipalIdealRing R] [Field k]
  (X : FF R K) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k X.Points]

variable {α β : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kˣ}
  (E : OrdinaryFiltration
    (Representation.ofDistribMulAction k
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points) α β)

/-- The actual ordinary injection, with its character action. -/
def ordinaryInjection :
    CharacterModule α k →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] X.Points where
  toFun := E.injection
  map_zero' := E.injection.map_zero
  map_add' := E.injection.map_add
  map_smul' g a := (E.injection_equivariant g a).symm

/-- The actual ordinary projection, with its character action. -/
def ordinaryProjection :
    X.Points →+[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] CharacterModule β k where
  toFun := E.projection
  map_zero' := E.projection.map_zero
  map_add' := E.projection.map_add
  map_smul' := E.projection_equivariant

/-- A preliminary sub-line model is derived by schematic closure. -/
@[implicit_reducible]
def ordinarySubLine : FF R K :=
  FF.ofIsFiniteFlat (CharacterModule α k)
    (X.isFiniteFlat.subobject R K (AlgebraicClosure K) X.Points
      (ordinaryInjection (k := k) X E) E.injective)

/-- A preliminary quotient-line model is derived from the actual surjection. -/
@[implicit_reducible]
def ordinaryQuotientLine : FF R K :=
  FF.ofIsFiniteFlat (CharacterModule β k)
    (X.isFiniteFlat.quotient R K (AlgebraicClosure K) X.Points
      (ordinaryProjection (k := k) X E) E.surjective)

/-- The injection regarded as a map between the constructed generic models. -/
abbrev ordinaryGenericInjection : GenericGaloisHom (ordinarySubLine X E) X :=
  ordinaryInjection (k := k) X E

/-- The projection regarded as a map between the constructed generic models. -/
abbrev ordinaryGenericProjection : GenericGaloisHom X (ordinaryQuotientLine X E) :=
  ordinaryProjection (k := k) X E

omit [IsPrincipalIdealRing R] in
/-- The ordinary sequence has exactly the kernel required by integral contraction. -/
theorem ordinaryGenericExact (x : X.Points) :
    ordinaryGenericProjection X E x = 0 ↔ ∃ a, ordinaryGenericInjection X E a = x := by
  change E.projection x = 0 ↔ ∃ a, E.injection a = x
  change x ∈ LinearMap.ker E.projection ↔ x ∈ LinearMap.range E.injection
  rw [E.exact]

/-- The submodel inside the specified middle model. -/
abbrev ordinaryKernelModel : FF R K :=
  (ordinaryGenericInjection X E).closure E.injective

/-- The integral quotient of the specified middle model. -/
abbrev ordinaryQuotientModel : FF R K :=
  (ordinaryGenericProjection X E).flatQuotient E.surjective

/-- Construct the integral ordinary extension, including faithful flatness and
its canonical torsor comparison, from the actual generic exact sequence. -/
def ordinaryModelExtension :
    ModelExtension (ordinaryKernelModel X E) X (ordinaryQuotientModel X E) :=
  (ordinaryGenericInjection X E).integralModelExtension (ordinaryGenericProjection X E)
    E.injective E.surjective (ordinaryGenericExact X E)

/-- The constructed integral inclusion induces the originally specified injection. -/
@[simp] theorem ordinaryModelExtension_inclusion (a : k) :
    genericHom (ordinaryModelExtension X E).inclusion a = E.injection a :=
  (ordinaryGenericInjection X E).genericHom_closureInclusion E.injective a

/-- The constructed integral quotient induces the originally specified projection. -/
@[simp] theorem ordinaryModelExtension_quotient (x : X.Points) :
    genericHom (ordinaryModelExtension X E).quotient x = E.projection x :=
  (ordinaryGenericProjection X E).genericHom_toFlatQuotient E.surjective x

/-- The actual submodel points keep the scalar action, rather than a chosen
basis over the prime field. -/
theorem ordinaryKernel_smul (a x : k) :
    genericHom (ordinaryModelExtension X E).inclusion (a • x) = a • E.injection x := by
  rw [ordinaryModelExtension_inclusion, E.injection.map_smul]

/-- The actual quotient map keeps the scalar action. -/
theorem ordinaryQuotient_smul (a : k) (x : X.Points) :
    genericHom (ordinaryModelExtension X E).quotient (a • x) = a * E.projection x := by
  rw [ordinaryModelExtension_quotient, E.projection.map_smul]
  rfl

end ThreeAdicPlan
