import Mathlib.ModelTheory.Definability

open FirstOrder Language

namespace Set

variable {M : Type*} {A : Set M} {L : Language} [L.Structure M] {α β : Type*}
  {p q : (α → M) → Prop} {f g : (α → M) → M}

variable (A L) in
@[fun_prop]
def DefinablePred (p : (α → M) → Prop) :=
  A.Definable L (setOf p)

@[fun_prop]
theorem DefinablePred.const (p : Prop) : A.DefinablePred L fun _ : α → M => p := by
  by_cases h : p <;> simp only [h]
  · exact definable_univ
  · exact definable_empty

@[fun_prop]
theorem DefinablePred.not (hp : A.DefinablePred L p) : A.DefinablePred L fun v => ¬ p v :=
  hp.compl

@[fun_prop]
theorem DefinablePred.and (hp : A.DefinablePred L p) (hq : A.DefinablePred L q) :
    A.DefinablePred L fun v => p v ∧ q v :=
  hp.inter hq

@[fun_prop]
theorem DefinablePred.or (hp : A.DefinablePred L p) (hq : A.DefinablePred L q) :
    A.DefinablePred L fun v => p v ∨ q v :=
  hp.union hq

@[fun_prop]
theorem DefinablePred.imp (hp : A.DefinablePred L p) (hq : A.DefinablePred L q) :
    A.DefinablePred L fun v => p v → q v := by
  convert hp.not.or hq
  tauto

@[fun_prop]
theorem DefinablePred.iff (hp : A.DefinablePred L p) (hq : A.DefinablePred L q) :
    A.DefinablePred L fun v => p v ↔ q v := by
  simp_rw [iff_iff_implies_and_implies]
  fun_prop

@[fun_prop]
theorem DefinablePred.forall {p : M → (α → M) → Prop}
    (hp : A.DefinablePred L fun v : Option α → M => p (v Option.none) (v ∘ Option.some)) :
    A.DefinablePred L fun v => ∀ x, p x v := by
  rw [DefinablePred]
  convert (hp.preimage_comp (Equiv.optionEquivSumPUnit.{0} α)).forall_of_finite
  apply (Equiv.funUnique PUnit M).symm.forall_congr
  intro a
  simp only [preimage_setOf_eq, Equiv.funUnique_symm_apply, mem_setOf_eq]
  congr!

@[fun_prop]
theorem DefinablePred.exists {p : M → (α → M) → Prop}
    (hp : A.DefinablePred L fun v : Option α → M => p (v Option.none) (v ∘ Option.some)) :
    A.DefinablePred L fun v => ∃ x, p x v := by
  simp_rw [← not_forall_not]
  exact hp.not.forall.not

theorem _root_.FirstOrder.Language.Formula.relaize (φ : L.Formula α) :
    A.DefinablePred L φ.Realize := by
  apply Definable.mono _ (empty_subset A)
  rw [empty_definable_iff]
  exists φ

theorem DefinablePred.rel {n : ℕ} (r : L.Relations n) :
    A.DefinablePred L (Structure.RelMap r) := by
  rw [DefinablePred, definable_iff_exists_formula_sum]
  exists r.formula (Term.var ∘ Sum.inr)

@[fun_prop]
theorem DefinablePred.comp [Finite α] {f : (β → M) → α → M}
    (hf : ∀ i, A.DefinableFun L fun v => f v i)
    (hp : A.DefinablePred L p) : A.DefinablePred L fun v => p (f v) :=
  hp.preimage_map hf

@[fun_prop]
theorem DefinablePred.ite {r} [DecidablePred p]
    (hp : A.DefinablePred L p) (hq : A.DefinablePred L q) (hr : A.DefinablePred L r) :
    A.DefinablePred L fun v => if p v then q v else r v := by
  simp_rw [ite_prop_iff_or]
  fun_prop

@[fun_prop]
theorem DefinableFun.comp' [Finite α] {f : (β → M) → α → M}
    (hf : ∀ i, A.DefinableFun L fun v => f v i)
    (hg : A.DefinableFun L g) : A.DefinableFun L fun v => g (f v) :=
  comp hf hg

-- leads to cycle
-- @[fun_prop]
theorem DefinableFun.comp₁ [Finite α] {g : M → M}
    (hf : A.DefinableFun L fun v => f v) (hg : A.DefinableFun L fun v : Unit → M => g (v ())) :
    A.DefinableFun L fun v => g (f v) :=
  comp (fun _ => hf) hg

@[fun_prop]
theorem DefinablePred.eq [Finite α] (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.DefinablePred L fun v => f v = g v :=
  hf.setOf_eq hg

@[fun_prop]
theorem DefinableFun.const (a : M) : Set.univ.DefinableFun L fun _ : α → M => a :=
  definableFun_const _ _ (mem_univ a)

@[fun_prop]
theorem DefinableFun.var (i) : A.DefinableFun L fun v : α → M => v i :=
  (definableFun_var _ _).of_empty

theorem DefinableFun.of_pred (h : A.DefinablePred L fun v : Option α → M => f (v ∘ some) = v none) :
    A.DefinableFun L f :=
  h

end Set
