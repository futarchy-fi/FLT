/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateSequences
public import FLT.GroupScheme.PDivisibleSystemCategory

/-! # Galois action and functoriality of coherent Tate sequences

The action and induced maps use the actual geometric-point maps at each level.
No finite-freeness, continuity, or period comparison is assumed.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Galois acts coordinatewise on compatible sequences. -/
instance instDistribMulActionTateSequences :
    DistribMulAction (Field.absoluteGaloisGroup K) X.tateSequences where
  smul g x := ⟨fun n ↦ g • x.val n, by
    intro m n h
    rw [map_smul, x.property h]⟩
  one_smul x := by apply Subtype.ext; funext n; exact one_smul _ _
  mul_smul g h x := by apply Subtype.ext; funext n; exact mul_smul _ _ _
  smul_zero g := by apply Subtype.ext; funext n; exact smul_zero _
  smul_add g x y := by apply Subtype.ext; funext n; exact smul_add _ _ _

/-- Evaluation is equivariant for the Galois action. -/
@[simp] theorem tateEval_smul (n : ℕ) (g : Field.absoluteGaloisGroup K)
    (x : X.tateSequences) : X.tateEval n (g • x) = g • X.tateEval n x := rfl

variable {X} {Y Z : PDivisibleSystem R K p height}

/-- A system morphism induces an equivariant additive map on Tate sequences. -/
def Hom.tateMap (f : Hom X Y) :
    X.tateSequences →+[Field.absoluteGaloisGroup K] Y.tateSequences where
  toFun x := ⟨fun n ↦ genericHom (f.app n) (x.val n), by
    intro m n h
    have he := congrArg (fun q ↦ genericHom q (x.val n)) (f.reduction_naturality h)
    simpa only [genericHom_comp, x.property h] using he.symm⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_add' x y := by apply Subtype.ext; funext n; exact map_add _ _ _
  map_smul' g x := by apply Subtype.ext; funext n; exact map_smul _ _ _

/-- The identity system morphism acts identically on the limit. -/
@[simp] theorem Hom.tateMap_id (x : X.tateSequences) : (Hom.id X).tateMap x = x := by
  apply Subtype.ext
  funext n
  exact genericHom_id (X.level n) (x.val n)

/-- Composition of system morphisms is preserved on the limit. -/
@[simp] theorem Hom.tateMap_comp (f : Hom X Y) (g : Hom Y Z) (x : X.tateSequences) :
    (f.comp g).tateMap x = g.tateMap (f.tateMap x) := by
  apply Subtype.ext
  funext n
  exact genericHom_comp (f.app n) (g.app n) (x.val n)

end ThreeAdicPlan.PDivisibleSystem
