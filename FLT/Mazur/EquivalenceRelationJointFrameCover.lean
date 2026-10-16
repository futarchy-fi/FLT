/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointGeometricComparison
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Cover.Sigma

/-!
# A finite etale common-frame cover of the entire mixed relation

The finite indexing set consists of jointly exhaustive pairs of embeddings into
a bounded label set. Their actual common-frame graphs cover every original
relation point. This does not assert that complete frames form an open subset.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Bounded, jointly exhaustive pairs of finite label embeddings. -/
def JointIndex (I J : Type) [Fintype I] [Fintype J] :=
  Σ n : Fin (Fintype.card I + Fintype.card J + 1),
    {a : (I ↪ Fin n.val) × (J ↪ Fin n.val) //
      ∀ k, (∃ i, a.1 i = k) ∨ ∃ j, a.2 j = k}

instance {I J : Type} [Fintype I] [Fintype J] : Fintype (JointIndex I J) := by
  classical
  unfold JointIndex
  infer_instance

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

/-- The actual common normalized source associated to a pair of finite embeddings. -/
def jointSource (c : JointIndex I J) : Scheme := source p q (Fin c.1.val) (c.2.val.1 o)

/-- The actual source comparison into the full original mixed relation. -/
def jointMap (c : JointIndex I J) : jointSource (p := p) (q := q) o c ⟶
    relation p q I J o o' := jointGraph e o o' c.2.val.1 c.2.val.2

instance jointMap_mono (c : JointIndex I J) : Mono (jointMap e o o' c) :=
  jointGraph_mono e o o' c.2.val.1 c.2.val.2 c.2.property

variable [Etale p]

instance jointMap_etale (c : JointIndex I J) : Etale (jointMap e o o' c) :=
  jointGraph_etale e o o' c.2.val.1 c.2.val.2

/-- Every original field-valued test lifts without extending its residue field. -/
theorem jointMap_geometric_lift {K : Type} [Field K]
    (z : Spec (.of K) ⟶ relation p q I J o o') :
    ∃ (c : JointIndex I J) (w : Spec (.of K) ⟶ jointSource (p := p) (q := q) o c),
      w ≫ jointMap e o o' c = z := by
  obtain ⟨n, hn, α, β, h, w, hw⟩ := exists_joint_original_frame e o o' z
  exact ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, ⟨⟨α, β⟩, h⟩⟩, w, hw⟩

/-- These source neighborhoods cover every point of the entire original mixed relation. -/
theorem jointMap_covers (x : relation p q I J o o') :
    ∃ (c : JointIndex I J) (y : jointSource (p := p) (q := q) o c),
      jointMap e o o' c y = x := by
  obtain ⟨c, w, hw⟩ := jointMap_geometric_lift e o o'
    ((relation p q I J o o').fromSpecResidueField x)
  refine ⟨c, w default, ?_⟩
  exact (congrArg (fun f ↦ f default) hw).trans (Scheme.fromSpecResidueField_apply _ _)

/-- A finite family of actual etale source neighborhoods of the full mixed relation. -/
def jointCover : (relation p q I J o o').Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers _ (jointSource (p := p) (q := q) o) (jointMap e o o')
    (jointMap_covers e o o') (fun _ ↦ inferInstance)

/-- The total comparison retains all the original source schemes as disjoint components. -/
def jointComparison : (∐ jointSource (p := p) (q := q) (J := J) o) ⟶
    relation p q I J o o' := Sigma.desc (jointMap e o o')

omit [Etale p] in
/-- Each component map is its actual common-frame graph. -/
@[reassoc] theorem component_jointComparison (c : JointIndex I J) :
    Sigma.ι (jointSource (p := p) (q := q) o) c ≫ jointComparison e o o' =
      jointMap e o o' c := Sigma.ι_comp_desc _ _

instance jointComparison_etale : Etale (jointComparison e o o') :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ ↦ inferInstance)

instance jointComparison_surjective : Surjective (jointComparison e o o') where
  surj x := by
    obtain ⟨c, y, rfl⟩ := jointMap_covers e o o' x
    refine ⟨Sigma.ι (jointSource (p := p) (q := q) o) c y, ?_⟩
    rw [← Scheme.Hom.comp_apply, component_jointComparison]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
