
import ForMathlib.FinLemmas
import FirstOrderZFC.Language

namespace FirstOrder.Language

variable {α : Type*} {n : ℕ} {M : Type*} [set.Structure M] {A : Set M} {a b c x y z : M}

namespace set

-- ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y
noncomputable def axiomOfExtensionality : set.Sentence :=
  ∀' ∀' (∀' (&2 ∈' &0 ⇔ &2 ∈' &1) ⟹ &0 =' &1)

@[simp]
theorem realize_axiomOfExtensionality :
    M ⊨ axiomOfExtensionality ↔ ∀ (x y : M), (∀ z, z ∈ x ↔ z ∈ y) → x = y := by
  simp [axiomOfExtensionality, Sentence.Realize, Formula.Realize]

-- ∃ x, ∀ a, a ∉ x
def axiomOfEmpty : set.Sentence :=
  ∃' ∀' (∼ (&1 ∈' &0))

@[simp]
theorem realize_axiomOfEmpty :
    M ⊨ axiomOfEmpty ↔ ∃ x : M, ∀ y, y ∉ x := by
  simp [axiomOfEmpty, Sentence.Realize, Formula.Realize]

-- ∀ x y ∃ z, ∀ a, a ∈ z ↔ a = x ∨ a = y
def axiomOfPairing : set.Sentence :=
  ∀' ∀' ∃' ∀' (&3 ∈' &2 ⇔ &3 =' &0 ⊔ &3 =' &1)

@[simp]
theorem realize_axiomOfPairing :
    M ⊨ axiomOfPairing ↔ ∀ x y, ∃ z : M, ∀ a, a ∈ z ↔ a = x ∨ a = y := by
  simp [axiomOfPairing, Sentence.Realize, Formula.Realize]

-- ∀ x, ∃ y, ∀ a, a ∈ y ↔ ∃ z ∈ x, a ∈ z
def axiomOfUnion : set.Sentence :=
  ∀' ∃' ∀' (&2 ∈' &1 ⇔ ∃' (&3 ∈' &0 ⊓ &2 ∈' &3))

@[simp]
theorem realize_axiomOfUnion :
    M ⊨ axiomOfUnion ↔ ∀ x : M, ∃ y : M, ∀ a, a ∈ y ↔ ∃ z ∈ x, a ∈ z := by
  simp [axiomOfUnion, Sentence.Realize, Formula.Realize]

-- ∀ x ∃ y, ∀ a, a ∈ y ↔ a ⊆ x
def axiomOfPowerset : set.Sentence :=
  ∀' ∃' ∀' (&2 ∈' &1 ⇔ &2 ⊆' &0)

@[simp]
theorem realize_axiomOfPowerset :
    M ⊨ axiomOfPowerset ↔ ∀ x, ∃ y : M, ∀ a, a ∈ y ↔ a ⊆ x := by
  simp [axiomOfPowerset, Sentence.Realize, Formula.Realize]

-- ∀ x, (∃ y, y ∈ x) → ∃ y ∈ x, ¬ ∃ z ∈ y, z ∈ x
def axiomOfRegularity : set.Sentence :=
  ∀' (∃' (&1 ∈' &0) ⟹ ∃' (&1 ∈' &0 ⊓ ∼ (∃' (&2 ∈' &1 ⊓ &2 ∈' &0))))

@[simp]
theorem realize_axiomOfRegularity :
    M ⊨ axiomOfRegularity ↔ ∀ x : M, (∃ y, y ∈ x) → ∃ y ∈ x, ¬ ∃ z ∈ y, z ∈ x := by
  simp [axiomOfRegularity, Sentence.Realize, Formula.Realize]

-- -- ∀ v₁, ⋯, vₙ x, ∃ y, ∀ a, a ∈ y ↔ a ∈ x ∧ φ(v₁, ⋯, vₙ, a)
noncomputable def axiomOfSeparation [Finite α] (φ : set.Formula (α ⊕ Fin 1)) : set.Sentence :=
  Formula.iAlls α (∀' ∃' ∀'
    (&2 ∈' &1 ⇔ &2 ∈' &0 ⊓ BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![2]) φ))

@[simp]
theorem realize_axiomOfSeparation [Finite α] {φ : set.Formula (α ⊕ Fin 1)} :
    M ⊨ axiomOfSeparation φ ↔
      ∀ (v : α → M), ∀ x : M, ∃ y : M, ∀ a, a ∈ y ↔ a ∈ x ∧ φ.Realize (Sum.elim v ![a]) := by
  simp only [Sentence.Realize, Formula.Realize, axiomOfSeparation, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, Nat.succ_eq_add_one, BoundedFormula.realize_iAlls,
    BoundedFormula.realize_all, BoundedFormula.realize_ex, BoundedFormula.realize_iff, realize_mem,
    Term.realize_var, Sum.elim_inr, Fin.snoc_apply_one, Fin.snoc_apply_one', Fin.snoc_apply_two',
    BoundedFormula.realize_inf, Fin.snoc_apply_zero, Fin.snoc_apply_zero',
    BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl, Function.comp_id,
    Sum.elim_comp_map, Sum.elim_comp_inr]
  congr!
  ext x
  cases x using Fin.cases <;> simp

-- ∀ v₁ ⋯ vₙ x, (∀ a ∈ x, ∃ b, φ(v₁, ⋯, vₙ, a, b)) → ∃ y, ∀ a ∈ x, ∃ b ∈ y, φ(v₁, ⋯, vₙ, a, b)
noncomputable def axiomOfCollection [Finite α] (φ : set.Formula (α ⊕ Fin 2)) : set.Sentence :=
  Formula.iAlls α (∀' (
    (∀' (&1 ∈' &0 ⟹ ∃' (BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![1, 2]) φ)))
      ⟹ ∃' ∀' (&2 ∈' &0
        ⟹ ∃' (&3 ∈' &1 ⊓ BoundedFormula.relabel (k := 0) (Sum.map Sum.inr ![2, 3]) φ))))

@[simp]
theorem realize_axiomOfCollection [Finite α] {φ : set.Formula (α ⊕ Fin 2)} :
    M ⊨ axiomOfCollection φ ↔
      ∀ (v : α → M), ∀ x : M, (∀ a ∈ x, ∃ b, φ.Realize (Sum.elim v ![a, b])) →
        ∃ y : M, ∀ a ∈ x, ∃ b ∈ y, φ.Realize (Sum.elim v ![a, b]) := by
  simp only [Sentence.Realize, Formula.Realize, axiomOfCollection, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, Nat.succ_eq_add_one, BoundedFormula.realize_iAlls,
    BoundedFormula.realize_all, BoundedFormula.realize_imp, realize_mem, Term.realize_var,
    Sum.elim_inr, Fin.snoc_apply_zero, Fin.snoc_apply_zero', Fin.snoc_apply_one',
    BoundedFormula.realize_ex, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
    Fin.cast_refl, Function.comp_id, Fin.snoc_apply_two', BoundedFormula.realize_inf,
    Fin.snoc_apply_one, Fin.snoc_apply_three']
  congr! <;> ext x <;> cases x with | inl => simp | inr x => cases x using Fin.cases <;> simp

inductive ZFMinusAxioms : set.Sentence → Prop
| extensionality : ZFMinusAxioms axiomOfExtensionality
| empty : ZFMinusAxioms axiomOfEmpty
| pairing : ZFMinusAxioms axiomOfPairing
| union : ZFMinusAxioms axiomOfUnion
| powerset : ZFMinusAxioms axiomOfPowerset
| regularity : ZFMinusAxioms axiomOfRegularity
| separation {n : ℕ} (φ : set.Formula (Fin n ⊕ Fin 1)) : ZFMinusAxioms (axiomOfSeparation φ)
| collection {n : ℕ} (φ : set.Formula (Fin n ⊕ Fin 2)) : ZFMinusAxioms (axiomOfCollection φ)

def isEmpty (t : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' ∼ (&(Fin.last n) ∈' t.relabel (Sum.map id Fin.castSucc))

def isSingleton (t t₁ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t.relabel (Sum.map id Fin.castSucc)
    ⇔ &(Fin.last n) =' t₁.relabel (Sum.map id Fin.castSucc))

def isPair (t t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t.relabel (Sum.map id Fin.castSucc)
    ⇔ &(Fin.last n) =' t₁.relabel (Sum.map id Fin.castSucc)
      ⊔ &(Fin.last n) =' t₂.relabel (Sum.map id Fin.castSucc))

def isInsert (t t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t.relabel (Sum.map id Fin.castSucc)
    ⇔ &(Fin.last n) =' t₁.relabel (Sum.map id Fin.castSucc)
      ⊔ &(Fin.last n) ∈' t₂.relabel (Sum.map id Fin.castSucc))

def isSUnion (t t₁ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t.relabel (Sum.map id Fin.castSucc)
    ⇔ ∃' (&(Fin.last (n + 1)) ∈' t₁.relabel (Sum.map id (Fin.castAdd 2))
      ⊓ &(Fin.last n).castSucc ∈' &(Fin.last (n + 1))))

def isUnion (t t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t.relabel (Sum.map id Fin.castSucc)
    ⇔ &(Fin.last n) ∈' t₁.relabel (Sum.map id Fin.castSucc)
      ⊔ &(Fin.last n) ∈' t₂.relabel (Sum.map id Fin.castSucc))

end set

/-- ZF minus axiom of infinity. -/
def Theory.zfMinusInf : set.Theory :=
  setOf set.ZFMinusAxioms

scoped notation "ZF-Inf" => FirstOrder.Language.Theory.zfMinusInf

namespace set

noncomputable section

open Theory

variable [M ⊨ ZF-Inf]

@[ext (iff := false), grind ext]
theorem ext : (∀ z : M, z ∈ x ↔ z ∈ y) → x = y := by
  simpa using realize_sentence_of_mem (M := M) (T := ZF-Inf) ZFMinusAxioms.extensionality x y

theorem ext_iff : x = y ↔ ∀ z : M, z ∈ x ↔ z ∈ y := by
  grind

instance : Std.Antisymm (· ⊆ · : M → M → Prop) where
  antisymm := by grind

private lemma exists_empty : ∃ x : M, ∀ a : M, a ∉ x := by
  simpa using realize_sentence_of_mem (M := M) (T := ZF-Inf) ZFMinusAxioms.empty

scoped instance : EmptyCollection M where
  emptyCollection := Classical.choose exists_empty

@[simp, grind .]
theorem notMem_empty : x ∉ (∅ : M) :=
  Classical.choose_spec exists_empty x

theorem nonempty_iff_ne_empty : Nonempty x ↔ x ≠ ∅ := by
  grind

@[push]
theorem not_nonempty_iff_eq_empty : ¬ Nonempty x ↔ x = ∅ := by
  grind

theorem eq_empty_or_nonempty (x : M) : x = ∅ ∨ Nonempty x := by
  grind

@[simp]
theorem not_nonempty_empty : ¬ Nonempty (∅ : M) := by
  grind

@[fun_prop]
theorem _root_.Set.DefinableFun.empty : A.DefinableFun set fun _ : α → M => ∅ :=
  .of_pred (by simp only [ext_iff, notMem_empty, false_iff]; fun_prop)

private lemma exists_pair (x y : M) : ∃ z : M, ∀ a : M, a ∈ z ↔ a = x ∨ a = y := by
  simpa [Sentence.Realize, Formula.Realize] using
    realize_sentence_of_mem (M := M) (T := ZF-Inf) ZFMinusAxioms.pairing x y

scoped instance : Singleton M M where
  singleton x := Classical.choose (exists_pair x x)

@[simp, grind =]
theorem mem_singleton : x ∈ ({y} : M) ↔ x = y := by
  simpa [Singleton.singleton] using Classical.choose_spec (exists_pair y y) x

@[fun_prop]
theorem _root_.Set.DefinableFun.singleton [Finite α] {f : (α → M) → M} (hf : A.DefinableFun set f) :
    A.DefinableFun set fun v => {f v} :=
  .of_pred (by simp_rw [ext_iff, mem_singleton]; fun_prop)

@[simp, grind .]
theorem nonempty_singleton : Nonempty ({x} : M) := by
  simp [Nonempty]

private lemma exists_sUnion (x : M) : ∃ y : M, ∀ a : M, a ∈ y ↔ ∃ z ∈ x, a ∈ z := by
  simpa [Sentence.Realize, Formula.Realize] using
    realize_sentence_of_mem (M := M) (T := ZF-Inf) ZFMinusAxioms.union x

protected def sUnion (x : M) :=
  Classical.choose (exists_sUnion x)

scoped prefix:110 "⋃₀ " => set.sUnion

@[simp, grind =]
theorem mem_sUnion : x ∈ ⋃₀ y ↔ ∃ z ∈ y, x ∈ z :=
  Classical.choose_spec (exists_sUnion y) x

@[fun_prop]
theorem _root_.Set.DefinableFun.sUnion [Finite α] {f : (α → M) → M} (hf : A.DefinableFun set f) :
    A.DefinableFun set fun v => ⋃₀ f v :=
  .of_pred (by simp only [ext_iff, mem_sUnion]; fun_prop)

@[simp]
theorem nonempty_sUnion : Nonempty (⋃₀ x) ↔ ∃ y ∈ x, Nonempty y := by
  simp [Nonempty]
  grind

@[simp] theorem sUnion_empty : ⋃₀ (∅ : M) = ∅ := by grind
@[simp] theorem sUnion_singleton : ⋃₀ ({x} : M) = x := by grind

scoped instance : Union M where
  union x y := ⋃₀ Classical.choose (exists_pair x y)

@[simp, grind =]
theorem mem_union : x ∈ y ∪ z ↔ x ∈ y ∨ x ∈ z := by
  simp [Union.union, Classical.choose_spec (exists_pair y z)]

@[fun_prop]
theorem _root_.Set.DefinableFun.union [Finite α] {f g : (α → M) → M} (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set g) : A.DefinableFun set fun v => f v ∪ g v :=
  .of_pred (by simp only [ext_iff, mem_union]; fun_prop)

theorem subset_union_left : x ⊆ x ∪ y := by grind
theorem subset_union_right : y ⊆ x ∪ y := by grind

@[simp, grind =]
theorem nonempty_union : Nonempty (x ∪ y) ↔ Nonempty x ∨ Nonempty y := by
  simp [Nonempty]
  grind

scoped instance : Insert M M where
  insert x y := {x} ∪ y

@[simp, grind =]
theorem mem_insert : x ∈ insert y z ↔ x = y ∨ x ∈ z := by
  simp [insert]

@[fun_prop]
theorem _root_.Set.DefinableFun.insert [Finite α] {f g : (α → M) → M} (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set g) : A.DefinableFun set fun v => insert (f v) (g v) :=
  .of_pred (by simp only [ext_iff, mem_insert]; fun_prop)

@[simp, grind .]
theorem nonempty_insert : Nonempty (insert x y) := by
  simp [Nonempty]

instance : LawfulSingleton M M where
  insert_empty_eq := by grind

@[simp] theorem sUnion_pair : (⋃₀ ({x, y} : M) : M) = x ∪ y := by grind

@[simp]
theorem singleton_eq_singleton_iff : ({x} : M) = {y} ↔ x = y := by
  rw [ext_iff]
  simp

@[simp]
theorem singleton_eq_pair_iff : ({x} : M) = {y, z} ↔ x = y ∧ x = z := by
  refine ⟨fun h => ?_, by grind⟩
  rw [ext_iff] at h
  grind [h y, h z]

@[simp]
theorem pair_eq_singleton_iff : ({x, y} : M) = {z} ↔ x = z ∧ y = z := by
  grind [singleton_eq_pair_iff]

@[simp]
theorem pair_eq_pair_iff {x₁ y₁ x₂ y₂ : M} :
    ({x₁, y₁} : M) = {x₂, y₂} ↔ x₁ = x₂ ∧ y₁ = y₂ ∨ x₁ = y₂ ∧ x₂ = y₁ := by
  refine ⟨fun h => ?_, by grind⟩
  rw [ext_iff] at h
  grind [h x₁, h y₁, h x₂, h y₂]

@[simp]
theorem pair_self (x : M) : ({x, x} : M) = {x} := by
  grind

private lemma exists_powerset (x : M) : ∃ y : M, ∀ a : M, a ∈ y ↔ a ⊆ x := by
  simpa [Sentence.Realize, Formula.Realize] using
    realize_sentence_of_mem (M := M) (T := ZF-Inf) ZFMinusAxioms.powerset x

protected def powerset (x : M) :=
  Classical.choose (exists_powerset x)

scoped prefix:110 "𝒫 " => set.powerset

@[simp, grind =]
theorem mem_powerset : x ∈ 𝒫 y ↔ x ⊆ y :=
  Classical.choose_spec (exists_powerset y) x

@[fun_prop]
theorem _root_.Set.DefinableFun.powerset [Finite α] {f : (α → M) → M} (hf : A.DefinableFun set f) :
    A.DefinableFun set fun v => 𝒫 f v :=
  .of_pred (by simp only [ext_iff, mem_powerset]; fun_prop)

@[simp, grind .] theorem nonempty_powerset : Nonempty (𝒫 x) := ⟨∅, by grind⟩

private lemma exists_sep (x : M) (p : M → Prop)
    (hp : Set.univ.DefinablePred set fun v : Unit → M => p (v ())) :
    ∃ y : M, ∀ a, a ∈ y ↔ a ∈ x ∧ p a := by
  rw [Set.DefinablePred, Set.definable_iff_finitely_definable] at hp
  rcases hp with ⟨s, -, hp⟩
  rw [Set.definable_iff_exists_formula_sum] at hp
  rcases hp with ⟨φ, hφ⟩
  simp only [SetLike.coe_sort_coe, Set.ext_iff, Set.mem_setOf_eq,
    (Equiv.funUnique Unit M).forall_congr_left, Equiv.funUnique_symm_apply, uniqueElim_const] at hφ
  have := realize_sentence_of_mem (M := M) (T := ZF-Inf)
    (ZFMinusAxioms.separation (φ.relabel (Sum.map s.equivFin (fun _ => 0))))
  simp only [realize_axiomOfSeparation, Formula.realize_relabel, Sum.elim_comp_map] at this
  simp only [hφ]
  convert this (fun i => s.equivFin.symm i) x
  ext
  simp

def sep (x : M) (p : M → Prop)
    (hp : Set.univ.DefinablePred set fun v : Unit → M => p (v ()) := by fun_prop) : M :=
  Classical.choose (exists_sep x p hp)

@[simp, grind =]
theorem mem_sep {p hp} : x ∈ sep y p hp ↔ x ∈ y ∧ p x :=
  Classical.choose_spec (exists_sep y p hp) x

@[fun_prop]
theorem _root_.Set.DefinableFun.sep [Finite α] {f : (α → M) → M} {p : (α → M) → M → Prop}
    (hf : A.DefinableFun set f)
    (hp : A.DefinablePred set fun v : Option α → M => p (v ∘ some) (v none))
    {hp' : ∀ v : α → M, Set.univ.DefinablePred set fun w : Unit → M => p v (w ())} :
    A.DefinableFun set fun v : α → M => sep (f v) (p v) (hp' v) :=
  .of_pred (by
    simp only [ext_iff, mem_sep]
    refine .forall (.iff (.and (by fun_prop) ?_) (by fun_prop))
    apply hp.comp (f := fun v => Option.elim' (v none) (v ∘ some ∘ some))
    intro x
    cases x <;> simp only [Option.elim'_some, Option.elim'_none] <;> fun_prop)

private lemma exists_replace (x : M) (f : M → M)
    (hf : Set.univ.DefinableFun set fun v : Unit → M => f (v ())) :
    ∃ y : M, ∀ a, a ∈ y ↔ ∃ b ∈ x, a = f b := by
  have hf := hf
  rw [Set.DefinableFun, Set.definable_iff_finitely_definable] at hf
  rcases hf with ⟨s, -, hf⟩
  rw [Set.definable_iff_exists_formula_sum] at hf
  rcases hf with ⟨φ, hφ⟩
  simp only [Function.tupleGraph, Function.comp_apply, SetLike.coe_sort_coe, Set.ext_iff,
    Set.mem_setOf_eq] at hφ
  have := realize_sentence_of_mem (M := M) (T := ZF-Inf)
    (ZFMinusAxioms.collection (φ.relabel (Sum.map s.equivFin (Option.elim' 1 (fun _ => 0)))))
  simp only [Fin.isValue, realize_axiomOfCollection, Formula.realize_relabel,
    Sum.elim_comp_map] at this
  specialize this (fun i => s.equivFin.symm i) x fun a ha => ?_
  · specialize hφ (Option.elim' (f a) (fun _ => a))
    simp only [Option.elim'_some, Option.elim'_none, true_iff] at hφ
    exists f a
    convert hφ
    · ext
      simp
    · ext x
      cases x <;> simp
  rcases this with ⟨y, hy⟩
  exists sep y (fun a => ∃ b ∈ x, a = f b) (by
    refine .exists (.and (by fun_prop) (.eq (by fun_prop) ?_))
    refine .comp' (f := fun v _ => v none) ?_ hf
    fun_prop)
  intro a
  rw [mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨b, hb, rfl⟩
  specialize hy b hb
  rcases hy with ⟨c, _, hc⟩
  suffices c = f b by rwa [← this]
  specialize hφ (Option.elim' c (fun _ => b))
  simp only [Option.elim'_some, Option.elim'_none] at hφ
  rw [eq_comm, hφ]
  convert hc
  · ext
    simp
  · ext x
    cases x <;> simp

def replace (x : M) (f : M → M)
    (hf : Set.univ.DefinableFun set fun v : Unit → M => f (v ()) := by fun_prop) : M :=
  Classical.choose (exists_replace x f hf)

@[simp, grind =]
theorem mem_replace {f hf} : x ∈ replace y f hf ↔ ∃ z ∈ y, x = f z :=
  Classical.choose_spec (exists_replace y f hf) x

@[simp]
theorem nonempty_replace {f hf} : Nonempty (replace x f hf) ↔ Nonempty x := by
  simp [Nonempty]

@[fun_prop]
theorem _root_.Set.DefinableFun.replace [Finite α] {f : (α → M) → M} {g : (α → M) → M → M}
    (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set fun v : Option α → M => g (v ∘ some) (v none))
    {hg' : ∀ v : α → M, Set.univ.DefinableFun set fun w : Unit → M => g v (w ())} :
    A.DefinableFun set fun v : α → M => replace (f v) (g v) (hg' v) :=
  .of_pred (by
    simp only [ext_iff, mem_replace]
    refine .forall (.iff (.exists (.and (by fun_prop) (.forall (.iff (by fun_prop)
      (.mem (by fun_prop) ?_))))) (by fun_prop))
    apply hg.comp' (f := fun v => Option.elim' ((v ∘ some) none) (v ∘ some ∘ some ∘ some ∘ some))
    intro x
    cases x <;> simp only [Option.elim'_some, Option.elim'_none] <;> fun_prop)

protected def sInter (x : M) :=
  sep (⋃₀ x) fun y => ∀ z ∈ x, y ∈ z

scoped prefix:110 "⋂₀ " => set.sInter

@[simp]
theorem sInter_empty : ⋂₀ (∅ : M) = ∅ := by
  grind [set.sInter]

theorem mem_sInter (hy : Nonempty y) : x ∈ ⋂₀ y ↔ ∀ z ∈ y, x ∈ z := by
  grind [set.sInter]

@[grind =]
theorem mem_sInter' : x ∈ ⋂₀ y ↔ Nonempty y ∧ ∀ z ∈ y, x ∈ z := by
  rcases eq_empty_or_nonempty y with rfl | hy
  · simp
  · grind [mem_sInter]

@[fun_prop]
theorem _root_.Set.DefinableFun.sInter [Finite α] {f : (α → M) → M} (hf : A.DefinableFun set f) :
    A.DefinableFun set fun v => ⋂₀ f v :=
  .of_pred (by simp only [ext_iff, mem_sInter']; fun_prop)

@[simp]
theorem sInter_singleton : ⋂₀ {x} = x := by
  grind

scoped instance : Inter M where
  inter x y := sep x fun z => z ∈ y

@[simp, grind =]
theorem mem_inter : x ∈ y ∩ z ↔ x ∈ y ∧ x ∈ z := by simp [Inter.inter]

@[simp] theorem sInter_pair : ⋂₀ {x, y} = x ∩ y := by grind

theorem inter_subset_left : x ∩ y ⊆ x := by grind
theorem inter_subset_right : x ∩ y ⊆ y := by grind

@[fun_prop]
theorem _root_.Set.DefinableFun.inter [Finite α] {f g : (α → M) → M} (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set g) : A.DefinableFun set fun v => f v ∩ g v :=
  .of_pred (by simp only [ext_iff, mem_inter]; fun_prop)

scoped instance : SDiff M where
  sdiff x y := sep x fun z => z ∉ y

@[simp, grind =]
theorem mem_sdiff : x ∈ y \ z ↔ x ∈ y ∧ x ∉ z := by simp [SDiff.sdiff]

@[fun_prop]
theorem _root_.Set.DefinableFun.sdiff [Finite α] {f g : (α → M) → M} (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set g) : A.DefinableFun set fun v => f v \ g v :=
  .of_pred (by simp only [ext_iff, mem_sdiff]; fun_prop)

protected def iUnion (x : M) (f : M → M)
    (hf : Set.univ.DefinableFun set fun v : Unit → M => f (v ()) := by fun_prop) : M :=
  ⋃₀ (replace x f hf)

scoped syntax (name := iUnionSyntax) "⋃ " ident " ∈ " term ", " term:60 : term
macro_rules (kind := iUnionSyntax)
  | `(⋃ $i ∈ $x, $f) => `(set.iUnion $x fun $i => $f)

@[simp, grind =]
theorem mem_iUnion {f hf} : x ∈ set.iUnion y f hf ↔ ∃ i ∈ y, x ∈ f i := by
  grind [set.iUnion]

theorem mem_iUnion_of_mem {f hf i} (hi : i ∈ y) (hx : x ∈ f i) : x ∈ set.iUnion y f hf := by
  grind

theorem regularity (x : M) (hx : Nonempty x) : ∃ y ∈ x, ¬ ∃ z ∈ y, z ∈ x := by
  have := realize_sentence_of_mem (M := M) (T := ZF-Inf) ZFMinusAxioms.regularity
  simp only [realize_axiomOfRegularity] at this
  grind

theorem not_mem_self : ¬ x ∈ x := by
  grind [regularity {x} ⟨x, by grind⟩]

theorem not_mem_cycle₂ : x ∈ y → y ∉ x := by
  grind [regularity {x, y} ⟨x, by grind⟩]

theorem not_mem_cycle₃ : x ∈ y → y ∈ z → z ∉ x := by
  grind [regularity {x, y, z} ⟨x, by grind⟩]

@[simp]
theorem realize_isEmpty {t : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isEmpty t).Realize v w ↔ t.realize (Sum.elim v w) = ∅ := by
  simp [isEmpty, Sum.elim_comp_map]
  grind

@[simp]
theorem realize_isSingleton {t t₁ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isSingleton t t₁).Realize v w ↔ t.realize (Sum.elim v w) = {t₁.realize (Sum.elim v w)} := by
  simp [isSingleton, Sum.elim_comp_map]
  grind

@[simp]
theorem realize_isPair {t t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isPair t t₁ t₂).Realize v w ↔
      t.realize (Sum.elim v w) = {t₁.realize (Sum.elim v w), t₂.realize (Sum.elim v w)} := by
  simp [isPair, Sum.elim_comp_map]
  grind

@[simp]
theorem realize_isInsert {t t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isInsert t t₁ t₂).Realize v w ↔
      t.realize (Sum.elim v w) =
        insert (t₁.realize (Sum.elim v w)) (t₂.realize (Sum.elim v w)) := by
  simp [isInsert, Sum.elim_comp_map]
  grind

@[simp]
theorem realize_isSUnion {t t₁ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isSUnion t t₁).Realize v w ↔ t.realize (Sum.elim v w) = ⋃₀ t₁.realize (Sum.elim v w) := by
  simp [isSUnion, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0)]
  grind

@[simp]
theorem realize_isUnion {t t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isUnion t t₁ t₂).Realize v w ↔
      t.realize (Sum.elim v w) = t₁.realize (Sum.elim v w) ∪ t₂.realize (Sum.elim v w) := by
  simp [isUnion, Sum.elim_comp_map]
  grind

end

end FirstOrder.Language.set
