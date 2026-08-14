# Jacquet–Langlands correspondence + multiplicity one

This is a first-pass map for hub-lsb1u.4. “JL” below means the global Jacquet–Langlands transfer from GL₂ to an inner form; “multiplicity one” is kept separate because the blueprint explicitly says that the cyclic-base-change image test may need it as an additional input.

## What FLT needs

### Where the blueprint and assumptions invoke the inputs

The grep hits are short and fairly precise:

* `blueprint/src/chapter/ch04overview.tex:30` lists “the Jacquet--Langlands correspondence” among the inputs to potential modularity.
* `blueprint/src/chapter/ch04overview.tex:86-88` says the minimal-case argument uses cyclic base change and “a characterisation of the image of the base change construction”; the author expects this to need multiplicity one and, because “modular” is defined with a totally definite quaternion algebra, Jacquet–Langlands as well.
* `blueprint/src/chapter/ch04overview.tex:93-98` is the actual direction of use: a converse theorem gives an automorphic representation of `GL₂/F`, Jacquet–Langlands makes it modular in the project’s quaternionic sense, and modularity lifting is then applied.
* `blueprint/src/chapter/chtopbestiary.tex:212-214` names the required theorem package: “Jacquet-Langlands for inner forms of `GL₂` over totally real fields” and “multiplicity 1 for these inner forms,” alongside cyclic base change, image classification, and automorphic induction.
* `blueprint/src/chapter/QuaternionAlgebraProject.tex:155-157` mentions Jacquet–Langlands only as the much harder result which, over `ℂ`, implies classical finite-dimensionality; it is motivation, not a formal assumption.
* `FLT/Assumptions/README.md:48-49` lists the still-forthcoming existence of a p-adic Galois representation attached to a weight-2 form on a totally definite quaternion algebra.
* `FLT/Assumptions/README.md:51-53` says the next assumptions need automorphic representations and warns that cyclic-base-change image classification may need “multiplicity 1 for `GL_2`.”
* `FLT/Assumptions/README.md:59-60` lists “The Jacquet-Langlands correspondence between `GL_2` and automorphic forms on totally definite quaternion algebras.” There is no `FLT/Assumptions/JacquetLanglands.lean` or multiplicity-one axiom yet; this README entry is the current assumption inventory.

The other grep hits are bibliographic background rather than FLT dependencies: `blueprint/src/chapter/ch07exampleGLn.tex:16` and `blueprint/src/chapter/chtopbestiary.tex:157` refer to Borel–Jacquet’s exposition, not to the Jacquet–Langlands transfer.

The repository has since made the intended specialization explicit. `FLT/GaloisRepresentation/Automorphic.lean:20-35` restricts automorphy to a totally real field of even degree, a totally definite quaternion algebra unramified at all finite places, weight 2, and a square-free `U₁(S)`-type level. Its definition at `:67-95` asks for an eigenform of the corresponding quaternionic Hecke algebra whose good-prime traces and determinants match the Galois representation.

### Weakest sufficient statement

Let `F` be totally real with even degree over `ℚ`. Let `D/F` be the quaternion algebra ramified at every real place and at no finite place (equivalently, the discriminant-1 totally definite algebra used by the repository), together with the finite-adelic rigidification already used in `FLT/QuaternionAlgebra/NumberField.lean:59-72`. Let `S` be the finite set of bad finite places and let `U₁(S)` be the square-free level in `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:27-43`.

The smallest theorem that closes the blueprint edge is:

> For every cuspidal automorphic representation `π` of `GL₂(𝔸_F)` with trivial central character, discrete-series weight 2 at every real place, and the local type/level needed for `U₁(S)`, there is a quaternionic automorphic representation `Π` of `Dˣ(𝔸_F)` with a `U₁(S)`-fixed vector. At a finite place (all of which are split for this `D`) the local component and unramified Hecke polynomial agree with `π`; at a real place the weight-2 discrete series is the local Jacquet–Langlands transfer to `D_vˣ`. The transfer is injective on this class (equivalently, equality of almost-all finite Hecke data implies equality), and each relevant `Dˣ` representation occurs with multiplicity one.

This is a global theorem packaged with the local assertions needed to identify the level, archimedean type, and Hecke eigenvalues. A separate formal development of every local Langlands correspondence, Plancherel measure, or arbitrary inner form is not needed for the FLT edge. The proof still has local ingredients, but the Lean-facing assumption can be global and specialized.

Thus we do **not** need arbitrary quaternion algebras, arbitrary weights, nontrivial central characters, or a theorem for every coefficient field. We need only the `D` above, weight 2/trivial infinity type, the `U₁(S)` levels used by the Galois-representation definition, and enough local-global compatibility to carry good-prime Hecke traces into `FLT/GaloisRepresentation/Automorphic.lean:87-95`. The converse direction (recovering the `GL₂` representation from a quaternionic eigenpacket) is useful for the image-classification argument, but can be stated only for the same packet and almost-all Hecke data.

## Statement inventory

The citations below are deliberately conservative. Where I remember the book/chapter but not the exact numbering, the number is marked “(number unverified)” rather than guessed as fact.

1. **Quaternion algebra local invariants and the FLT algebra (M).**  Classify a quaternion algebra by its local split/ramified invariants, with an even number of ramified places; for even-degree totally real `F` there is a unique algebra ramified at every real place and no finite place. This supplies the discriminant-1 `D` and the finite-place rigidification.  *Citation:* Jacquet–Langlands (1970), *Automorphic Forms on GL(2)*, LNM 114, §§1–2 (section number unverified); Gelbart (1975), *Automorphic Forms on Adele Groups*, Annals of Mathematics Studies 83, discussion of quaternion algebras (section number unverified).

2. **Local JL at a division place (L).**  For a local quaternion division algebra `D_v`, irreducible essentially square-integrable representations of `GL₂(F_v)` correspond to irreducible smooth representations of `D_vˣ`, characterized by the equality of characters on matching regular elliptic elements; at a split place the transfer is the identity.  *Citation:* Jacquet–Langlands (1970), LNM 114, local correspondence chapter/§16 (theorem number unverified); Gelbart (1975), local Jacquet–Langlands discussion (section/theorem number unverified).

3. **Archimedean weight-2 transfer (M).**  At a real place, the weight-2 discrete series occurring in a parallel-weight-2 Hilbert form transfers to the finite-dimensional representation of `D_vˣ ≅ ℍˣ` used by the totally definite algebra (trivial infinity type in the project’s convention).  *Citation:* Jacquet–Langlands (1970), LNM 114, archimedean/local correspondence sections (number unverified); Gelbart (1975), archimedean JL discussion (section/theorem number unverified).

4. **Local matching of orbital integrals (M/L).**  Construct matching test functions on `GL₂(F_v)` and `D_vˣ` whose regular-elliptic orbital integrals agree, with the transfer factor normalized compatibly with the character identity. This is the local analytic input to the trace-formula proof.  *Citation:* Jacquet–Langlands (1970), LNM 114, §§14–16 (section numbers unverified); Gelbart (1975), trace-formula/JL treatment (section number unverified).

5. **The anisotropic trace formula for `Dˣ` (XL).**  Because `Dˣ(F)\backslash Dˣ(𝔸_F)` is compact modulo centre for the totally definite `D`, its trace formula has a discrete spectral side; express it in terms of conjugacy classes and orbital integrals.  *Citation:* Jacquet–Langlands (1970), LNM 114, trace-formula chapters (§§14–16, numbers unverified); Gelbart (1975), *Automorphic Forms on Adele Groups*, trace-formula chapter (chapter/section number unverified). A modern trace-formula route is Arthur–Clozel (1989), *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*, Annals of Mathematics Studies 120, Chs. 3–4 (theorem numbers unverified).

6. **Global Jacquet–Langlands transfer (XL).**  Compare the `GL₂` and `Dˣ` trace formulas using node 4 to obtain a cuspidal transfer `π ↦ π^D` whenever `π_v` is discrete series at every place where `D` is division; the transfer is unique, preserves the standard `L`-function, and agrees with local JL. Its image is exactly the cuspidal packets with those local conditions.  *Citation:* Jacquet–Langlands (1970), LNM 114, global theorem in §16 (Theorem 16.1, number unverified); Gelbart (1975), global JL theorem (section/theorem number unverified); Vignéras (1980), *Arithmétique des algèbres de quaternions*, LNM 800, JL chapter (section/theorem number unverified).

7. **Level and Hecke compatibility in the discriminant-1 case (L).**  For finite places (where `D` is split), `U₁(S)`-invariants on `π^D` are the expected congruence invariants on `π`; outside `S`, the operators `T_v` and the Satake polynomial/eigenvalue agree. This is the exact bridge to the trace and determinant clauses in `GaloisRep.IsAutomorphicOfLevel`.  *Citation:* Jacquet–Langlands (1970), LNM 114, local-global/newvector sections (number unverified); Gelbart (1975), Hecke/JL discussion (section/theorem number unverified). The concrete target level is documented in `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:27-43`.

8. **Strong multiplicity one for `GL₂` (L).**  Two cuspidal `GL₂(𝔸_F)` representations with the same central character and equal local components (equivalently, matching Hecke eigenvalues) outside a finite set are equal. This turns “same almost-all Hecke packet” into a unique global source for the transfer.  *Citation:* Jacquet–Langlands (1970), LNM 114, multiplicity-one theorem (section/theorem number unverified); Gelbart (1975), strong multiplicity-one discussion (section/theorem number unverified). The later Rankin–Selberg proof is Jacquet–Shalika, “A non-vanishing theorem for Rankin–Selberg L-functions of `GL(n)`,” *American Journal of Mathematics* 105 (1983), theorem number unverified.

9. **Multiplicity one for the quaternionic inner form (M/L).**  Each cuspidal automorphic representation of `Dˣ(𝔸_F)` occurs with multiplicity one in the discrete automorphic spectrum; at a fixed level, the corresponding simultaneous Hecke eigensystem is not duplicated. The shortest route is as a corollary of nodes 6 and 8 (or directly from the anisotropic trace formula in node 5), rather than a second independent trace-formula proof.  *Citation:* Jacquet–Langlands (1970), LNM 114, global multiplicity-one corollary (section/theorem number unverified); Gelbart (1975), quaternionic multiplicity discussion (section/theorem number unverified).

10. **JL-compatible cyclic base-change image criterion (XL, boundary node).**  For a solvable/cyclic totally real extension `E/F`, base change of the quaternionic packet is characterized by Gal-invariance, with the expected twisting ambiguity by characters of `E/F`; equality of packets is reduced to node 9/strong multiplicity one. This is the interface needed by the cyclic-base-change chapter, not a second FLT-specific JL theorem.  *Citation:* Arthur–Clozel (1989), *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*, Chs. 3–4 (theorem numbers unverified); see also the blueprint’s explicit dependency at `blueprint/src/chapter/ch04overview.tex:86-88`.

## Dependency edges

Internal edges (a `(?)` marks a route choice that should be checked against the eventual formal statement):

* `1 → 2,3` (local algebra and the choice of the ramified set are prerequisites).
* `2 + 3 + 4 → 5` (local characters/orbital integrals feed the anisotropic trace formula) `(?)`.
* `5 + 4 → 6` (trace comparison gives global JL) `(?)`.
* `6 + 7 → restricted-FLT-JL` (the theorem in **What FLT needs**).
* `8 + 6 → 9` (derive inner-form multiplicity one from transfer and `GL₂` strong multiplicity one) `(?)`.
* `restricted-FLT-JL + 9 → 10` (packet uniqueness is the multiplicity-one step in the base-change image argument) `(?)`.

External campaign edges:

* **hub-lsb1u.5 (cyclic base change):** consumes node 10 and the restricted transfer; its image/classification statement is exactly the blueprint dependency at `ch04overview.tex:86-88`.
* **hub-lsb1u.10 (Galois representations):** consumes node 7 to identify good-prime traces/determinants with the quaternionic Hecke eigenpacket in `FLT/GaloisRepresentation/Automorphic.lean:87-95`; the forthcoming assumption is named at `FLT/Assumptions/README.md:48-49`.
* **hub-lsb1u.9 (CFT):** supplies the local reciprocity/central-character and solvable-extension interfaces used to state levels and base change (the blueprint already flags global class field theory at `ch04overview.tex:27-30`) `(?)`.
* **Mathlib:** adeles/topological restricted products and finite-dimensional linear algebra are prerequisites for nodes 1, 5, and 7; there is currently no trace-formula anchor.

## Mathlib anchors

The runner could not resolve external hosts for a live documentation fetch (DNS failure on the Mathlib docs URL), so the statuses below are checked against the repository’s Mathlib import paths and current Mathlib namespaces. A live docs pass should confirm names after the next dependency update.

| Topic | Status in Mathlib4 | Namespace/module anchor | FLT repo seed |
|---|---|---|---|
| Quaternion algebras | **Partial**. `Mathlib.Analysis.Quaternion` supplies Hamilton-quaternion notation, not the general central-simple/quaternion-algebra theory needed here. | `Mathlib.Analysis.Quaternion` | `FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean:52-57` defines `IsQuaternionAlgebra`; `FLT/QuaternionAlgebra/NumberField.lean:59-72` defines `IsQuaternionAlgebra.NumberField.WithRigidification` and the finite-place split model; `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean` is the form layer. |
| Adeles | **Exists, with FLT extensions**. Finite, infinite, and full number-field adeles are in Mathlib; local compactness/base-change/restricted-product lemmas are extended in FLT. | `IsDedekindDomain.FiniteAdeleRing`, `NumberField.InfiniteAdeleRing`, `NumberField.AdeleRing`; modules `Mathlib.NumberTheory.NumberField.{FiniteAdeleRing,InfiniteAdeleRing,AdeleRing}` | `FLT/Mathlib/NumberTheory/NumberField/FiniteAdeleRing.lean:10-21`, `FLT/HaarMeasure/FiniteAdeleRing.lean`, `FLT/NumberField/AdeleRing.lean`, and `FLT/QuaternionAlgebra/NumberField.lean`. |
| Automorphic forms | **Absent in general / partial in FLT.** Mathlib has representation-theory primitives but no developed global automorphic-representation/JL API. | No established Mathlib automorphic-form namespace. FLT’s custom namespaces are `TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm` and `AutomorphicForm.GLn`. | `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean:24-34`; finite-dimensionality in `.../FiniteDimensional.lean:15-24`; Hecke operators in `.../HeckeOperators/Concrete.lean:15-43`; the older GL(n)/Q prototype warns it is unfinished at `FLT/GlobalLanglandsConjectures/GLnDefs.lean:17-23`. |
| Trace formula | **Absent.** No Mathlib trace-formula module/namespace and no FLT implementation of orbital-integral or invariant-trace-formula machinery was found. | None. Existing Haar-measure and representation-theory namespaces are only prerequisites. | `FLT/HaarMeasure/*` and `FLT/Mathlib/MeasureTheory/Group/*` are analytic seeds, but `rg` finds no trace-formula implementation. |

The concrete `FLT/` seed list is: quaternion/algebra/form files `FLT/Mathlib/Algebra/IsQuaternionAlgebra.lean`, `FLT/QuaternionAlgebra/NumberField.lean`, `FLT/AutomorphicForm/QuaternionAlgebra/Basic.lean`, `FiniteDimensional.lean`, `HeckeOperators/{Abstract,Local,Concrete}.lean`, and `InnerProduct.lean`; adelic files `FLT/Mathlib/NumberTheory/NumberField/{AdeleRing,FiniteAdeleRing,InfiniteAdeleRing}.lean`, `FLT/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean`, `FLT/Mathlib/MeasureTheory/Constructions/BorelSpace/{AdeleRing,FiniteAdeleRing}.lean`, `FLT/NumberField/{AdeleRing,InfiniteAdeleRing}.lean`, `FLT/HaarMeasure/FiniteAdeleRing.lean`, `FLT/HaarMeasure/HaarChar/{AdeleRing,FiniteAdeleRing}.lean`, and the base-change/restricted-product files under `FLT/DedekindDomain/FiniteAdeleRing/`. These are usable infrastructure seeds, not JL statements.

## Route risk

* The dominant absence is the analytic core: orbital-integral matching, the anisotropic trace formula, and global transfer are one XL-sized proof stack; Mathlib has no trace-formula infrastructure.
* Automorphic representations for `GL₂/F`, local components, and the archimedean discrete-series/type-2 interface are not formalized. The old `AutomorphicForm.GLn` prototype explicitly says it never reached weights at infinity.
* Multiplicity one is not an assumption file yet. The cyclic-base-change image criterion couples it to node 10 and therefore to hub-lsb1u.5; splitting the two projects without a precise packet interface is a schedule risk.
* The existing quaternion-algebra miniproject materially narrows the Lean-facing statement (discriminant 1, weight 2, `U₁(S)`, finite-dimensional Hecke modules), but it does not prove JL or multiplicity one. It is a useful seed, not a reduction of the analytic XL node.
* Size verdict: smaller than the Mazur chapter’s map, whose core spans multiple XL nodes. This chapter has one unavoidable XL trace/global-transfer stack plus several L/M interfaces; with the specialized theorem taken as an assumption it is manageable, while proving the theorem is a separate major analytic campaign.
