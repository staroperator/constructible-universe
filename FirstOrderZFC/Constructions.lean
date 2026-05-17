import FirstOrderZFC.Basic

namespace FirstOrder.Language.set

variable {α : Type*} {n : ℕ} {M : Type*} [set.Structure M] {A : Set M} {a b c x y z : M}

def isKpair (t t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∃' ∃' (isPair (t.relabel (Sum.map id (Fin.castAdd 2))) &(Fin.last n).castSucc &(Fin.last (n + 1))
    ⊓ isSingleton &(Fin.last n).castSucc (t₁.relabel (Sum.map id (Fin.castAdd 2)))
    ⊓ isPair &(Fin.last (n + 1)) (t₁.relabel (Sum.map id (Fin.castAdd 2)))
      (t₂.relabel (Sum.map id (Fin.castAdd 2))))

def isRelation (t t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t.relabel (Sum.map id Fin.castSucc)
    ⟹ ∃' (&(Fin.last (n + 1)) ∈' t₁.relabel (Sum.map id (Fin.castAdd 2))
      ⊓ ∃' (&(Fin.last (n + 2)) ∈' t₂.relabel (Sum.map id (Fin.castAdd 3))
        ⊓ isKpair &((Fin.last n).castAdd 2) &(Fin.last (n + 1)).castSucc &(Fin.last (n + 2)))))

def isTotal (t t₁ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' (&(Fin.last n) ∈' t₁.relabel (Sum.map id Fin.castSucc)
    ⟹ ∃' ∃' (&(Fin.last (n + 2)) ∈' t.relabel (Sum.map id (Fin.castAdd 3))
        ⊓ isKpair &(Fin.last (n + 2)) &((Fin.last n).castAdd 2) &(Fin.last (n + 1)).castSucc))

def isUnique (t : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  ∀' ∀' ∀' (
    ∃' (&(Fin.last (n + 3)) ∈' t.relabel (Sum.map id (Fin.castAdd 4))
      ⊓ isKpair &(Fin.last (n + 3)) &((Fin.last n).castAdd 3) &((Fin.last (n + 1)).castAdd 2))
    ⟹ ∃' (&(Fin.last (n + 3)) ∈' t.relabel (Sum.map id (Fin.castAdd 4))
      ⊓ isKpair &(Fin.last (n + 3)) &((Fin.last n).castAdd 3) &(Fin.last (n + 2)).castSucc)
    ⟹ &(Fin.last (n + 1)).castSucc =' &(Fin.last (n + 2)))

def isFunction (t t₁ t₂ : set.Term (α ⊕ Fin n)) : set.BoundedFormula α n :=
  isRelation t t₁ t₂ ⊓ isTotal t t₁ ⊓ isUnique t

noncomputable section

variable [M ⊨ ZF-Inf]

def ofNat : Nat → M
| 0 => ∅
| n + 1 => insert (set.ofNat n) (set.ofNat n)

@[simp, grind =] theorem ofNat_zero : ofNat 0 = (∅ : M) := rfl
@[simp, grind =] theorem ofNat_succ {n : ℕ} : ofNat (n + 1) = insert (ofNat n) (ofNat n : M) := rfl

theorem ofNat_mem_ofNat_of_lt {n m : ℕ} (h : n < m) : ofNat n ∈ (ofNat m : M) := by
  induction h <;> grind

@[simp]
theorem ofNat_inj {n m : ℕ} : (ofNat n : M) = ofNat m ↔ n = m := by
  grind [ofNat_mem_ofNat_of_lt (M := M), not_mem_self (M := M) (x := ofNat n)]

@[simp] theorem natCast_ne_natCast_iff {n m : ℕ} : (ofNat n : M) ≠ ofNat m ↔ n ≠ m := ofNat_inj.not

/-- Kuratowski pair. -/
def kpair (x y : M) : M :=
  {{x}, {x, y}}

@[simp, grind =]
theorem kpair_inj {x₁ y₁ x₂ y₂ : M} : kpair x₁ y₁ = kpair x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  simp [kpair]
  grind

@[fun_prop]
nonrec theorem _root_.Set.DefinableFun.kpair [Finite α] {f g : (α → M) → M}
    (hf : A.DefinableFun set f) (hg : A.DefinableFun set g) :
    A.DefinableFun set fun v => kpair (f v) (g v) := by
  simp only [kpair]
  fun_prop

@[simp]
theorem realize_isKpair {t t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isKpair t t₁ t₂).Realize v w ↔
      t.realize (Sum.elim v w) = kpair (t₁.realize (Sum.elim v w)) (t₂.realize (Sum.elim v w)) := by
  simp [isKpair, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0), kpair]

def prod (a b : M) : M :=
  sep (𝒫 𝒫 (a ∪ b)) fun p => ∃ x ∈ a, ∃ y ∈ b, p = kpair x y

@[grind =]
theorem mem_prod {p} : p ∈ prod a b ↔ ∃ x ∈ a, ∃ y ∈ b, p = kpair x y := by
  grind [prod, kpair]

@[simp]
theorem kpair_mem_prod_iff : kpair x y ∈ prod a b ↔ x ∈ a ∧ y ∈ b := by
  simp [mem_prod, *]

theorem kpair_mem_prod (hx : x ∈ a) (hy : y ∈ b) : kpair x y ∈ prod a b := by
  simp [kpair_mem_prod_iff, *]

@[simp, grind =]
theorem nonempty_prod : Nonempty (prod a b) ↔ Nonempty a ∧ Nonempty b := by
  simp [Nonempty, mem_prod]

@[fun_prop]
nonrec theorem _root_.Set.DefinableFun.prod [Finite α] {f g : (α → M) → M}
    (hf : A.DefinableFun set f) (hg : A.DefinableFun set g) :
    A.DefinableFun set fun v => prod (f v) (g v) := by
  simp only [prod]
  fun_prop

@[simp]
theorem realize_isRelation {t t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isRelation t t₁ t₂).Realize v w ↔
      t.realize (Sum.elim v w) ⊆ prod (t₁.realize (Sum.elim v w)) (t₂.realize (Sum.elim v w)) := by
  simp [isRelation, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0),
    Fin.snoc_comp_castAdd (m := 1), Fin.snoc_comp_castAdd (m := 2), Fin.snoc_castAdd (m := 0),
    Fin.snoc_castAdd (m := 1), subset_def, mem_prod]

abbrev Prod (a b : M) := ↥(prod a b)

namespace Prod

variable {x x₁ x₂ : ↥a} {y y₁ y₂ : ↥b} {p q : Prod a b}

def fst (p : Prod a b) : ↥a :=
  ⟨Classical.choose (mem_prod.1 p.2), (Classical.choose_spec (mem_prod.1 p.2)).1⟩

def snd (p : Prod a b) : ↥b :=
  ⟨Classical.choose (Classical.choose_spec (mem_prod.1 p.2)).2,
    (Classical.choose_spec (Classical.choose_spec (mem_prod.1 p.2)).2).1⟩

def mk (x : ↥a) (y : ↥b) : Prod a b :=
  ⟨kpair x.1 y.1, kpair_mem_prod x.2 y.2⟩

@[simp, grind =] theorem coe_mk : (mk x y).1 = kpair x.1 y.1 := rfl

@[simp, grind =]
theorem mk_inj : mk x₁ y₁ = mk x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  simp_rw [← Subtype.coe_inj]
  exact kpair_inj

@[simp, grind =]
theorem mk_fst_snd (p : Prod a b) : mk p.fst p.snd = p := by
  ext1
  exact (Classical.choose_spec (Classical.choose_spec (mem_prod.1 p.2)).2).2.symm

@[simp, grind =]
theorem fst_mk : (mk x y).fst = x :=
  (mk_inj.1 (mk_fst_snd _)).1

@[simp, grind =]
theorem snd_mk : (mk x y).snd = y :=
  (mk_inj.1 (mk_fst_snd _)).2

@[ext, grind ext]
theorem ext : p.fst = q.fst → p.snd = q.snd → p = q := by
  rw [← mk_fst_snd p, ← mk_fst_snd q]
  grind

@[simp, grind =]
lemma fst_kpair {x y} {h : kpair x y ∈ prod a b} :
    fst ⟨kpair x y, h⟩ = ⟨x, (kpair_mem_prod_iff.1 h).1⟩ := by
  rw [kpair_mem_prod_iff] at h
  rw! [← coe_mk (x := ⟨x, h.1⟩) (y := ⟨y, h.2⟩), Subtype.eta, fst_mk]
  rfl

@[simp, grind =]
lemma coe_snd_kpair {x y} {h : kpair x y ∈ prod a b} :
    snd ⟨kpair x y, h⟩ = ⟨y, (kpair_mem_prod_iff.1 h).2⟩ := by
  rw [kpair_mem_prod_iff] at h
  rw! [← coe_mk (x := ⟨x, h.1⟩) (y := ⟨y, h.2⟩), Subtype.eta, snd_mk]
  rfl

@[fun_prop]
theorem definableFun_fst : DefinableFun (fst : Prod a b → ↥a) := by
  simp only [DefinableFun]
  convert_to Set.univ.DefinablePred set fun v : Fin 2 → M => v 1 ∈ a ∧ ∃ y ∈ b, kpair (v 1) y = v 0
  · grind
  · fun_prop

@[fun_prop]
theorem definableFun_snd : DefinableFun (snd : Prod a b → ↥b) := by
  simp only [DefinableFun]
  convert_to Set.univ.DefinablePred set fun v : Fin 2 → M => v 1 ∈ b ∧ ∃ x ∈ a, kpair x (v 1) = v 0
  · grind
  · fun_prop

@[fun_prop]
theorem definableFun_mk {f : ↥a → ↥b} {g : ↥a → ↥c} (hf : DefinableFun f) (hg : DefinableFun g) :
    DefinableFun fun x => mk (f x) (g x) := by
  simp only [DefinableFun] at *
  convert_to Set.univ.DefinablePred set fun v : Fin 2 → M =>
    ∃ y z, (∃ (h : v 0 ∈ a), (f ⟨v 0, h⟩).1 = y) ∧ (∃ (h : v 0 ∈ a), (g ⟨v 0, h⟩).1 = z)
    ∧ kpair y z = v 1
  · grind [Prod.coe_mk]
  · refine .exists (.exists (.and ?_ (.and ?_ (by fun_prop)))) <;> simp only [Function.comp_apply]
    · convert hf.comp (f := fun v : Option (Option (Fin 2)) → M =>
        ![v (some (some 0)), v (some none)]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop
    · convert hg.comp (f := fun v : Option (Option (Fin 2)) → M => ![v (some (some 0)), v none]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop

example : Prod a b ≃ ↥a × ↥b where
  toFun p := (p.fst, p.snd)
  invFun p := mk p.1 p.2
  left_inv := by grind
  right_inv := by grind

@[elab_as_elim, cases_eliminator]
theorem cases_on {p : Prod a b → Prop} (x : Prod a b) (h : ∀ x y, p (Prod.mk x y)) : p x := by
  rw [← mk_fst_snd x]
  apply h

@[simp]
theorem «forall» {p : Prod a b → Prop} : (∀ (x : Prod a b), p x) ↔ ∀ x y, p (Prod.mk x y) :=
  ⟨fun h x y => h (Prod.mk x y), fun h x => by cases x; apply h⟩

@[simp]
theorem «exists» {p : Prod a b → Prop} : (∃ (x : Prod a b), p x) ↔ ∃ x y, p (Prod.mk x y) :=
  ⟨fun ⟨x, h⟩ => ⟨x.fst, x.snd, by simpa⟩, fun ⟨x, y, h⟩ => ⟨Prod.mk x y, h⟩⟩

end Prod

@[fun_prop]
theorem DefinablePred.exists {p : ↥a → ↥b → Prop}
    (hp : DefinablePred fun x : Prod a b => p x.fst x.snd) :
    DefinablePred fun x => ∃ y, p x y := by
  simp only [DefinablePred] at *
  convert_to Set.univ.DefinablePred set fun v : Unit → M =>
    ∃ y, ∃ (h : v () ∈ a) (hy : y ∈ b), p ⟨v (), h⟩ ⟨y, hy⟩
  · grind
  · refine .exists ?_
    convert hp.comp (f := fun v _ => kpair (v (some ())) (v none)) (by fun_prop) using 2
    grind

@[fun_prop]
theorem DefinablePred.forall {p : ↥a → ↥b → Prop}
    (hp : DefinablePred fun x : Prod a b => p x.fst x.snd) :
    DefinablePred fun x => ∀ y, p x y := by
  simp_rw [← not_exists_not]
  exact hp.not.exists.not

@[fun_prop]
theorem DefinablePred.existsUnique {p : ↥a → ↥b → Prop}
    (hp : DefinablePred fun x : Prod a b => p x.fst x.snd) :
    DefinablePred fun x => ∃! y, p x y := by
  simp_rw [ExistsUnique]
  refine .exists (.and hp (.forall (.imp ?_ (by fun_prop))))
  convert hp.comp (f := fun x : Prod (prod a b) b => Prod.mk (Prod.fst x.fst) x.snd) (by fun_prop)
    using 2
  simp

theorem DefinableFun.of_pred {f : ↥a → ↥b} (h : DefinablePred fun x : Prod a b => f x.fst = x.snd) :
    DefinableFun f := by
  simp only [DefinablePred, DefinableFun] at *
  convert h.comp (f := fun (v : Fin 2 → M) _ => kpair (v 0) (v 1)) (by fun_prop) using 2
  grind

def sum (a b : M) :=
  replace a (fun x => kpair (ofNat 0) x) ∪ replace b fun x => kpair (ofNat 1) x

@[grind =]
theorem mem_sum :
    x ∈ sum a b ↔ (∃ y ∈ a, x = kpair (ofNat 0) y) ∨ (∃ y ∈ b, x = kpair (ofNat 1) y) := by
  simp [sum]

abbrev Sum (a b : M) := ↥(sum a b)

namespace Sum

def inl (x : ↥a) : Sum a b := ⟨kpair (ofNat 0) x.1, by grind⟩

def inr (x : ↥b) : Sum a b := ⟨kpair (ofNat 1) x.1, by grind⟩

theorem eq_inl_or_eq_inr (x : Sum a b) : (∃ y, x = inl y) ∨ (∃ y, x = inr y) := by
  rcases mem_sum.1 x.2 with ⟨y, hy, h⟩ | ⟨y, hy, h⟩
  · refine Or.inl ⟨⟨y, hy⟩, ?_⟩
    ext1
    grind [inl]
  · refine Or.inr ⟨⟨y, hy⟩, ?_⟩
    ext1
    grind [inr]

@[fun_prop]
theorem definableFun_inl : DefinableFun (inl : ↥a → Sum a b) := by
  simp only [DefinableFun, inl, exists_prop]
  fun_prop

@[fun_prop]
theorem definableFun_inr : DefinableFun (inr : ↥b → Sum a b) := by
  simp only [DefinableFun, inr, exists_prop]
  fun_prop

@[elab_as_elim, cases_eliminator]
theorem cases_on {p : Sum a b → Prop} (x : Sum a b) (inl : ∀ x, p (inl x)) (inr : ∀ y, p (inr y)) :
    p x := by
  grind [eq_inl_or_eq_inr x]

end Sum

def sigma (a : M) (f : M → M)
    (hf : Set.univ.DefinableFun set fun v => f (v ()) := by fun_prop) : M :=
  sep (𝒫 𝒫 (a ∪ set.iUnion a f hf)) (fun p => ∃ x ∈ a, ∃ y ∈ f x, p = kpair x y)
    (.exists (.and (by fun_prop) (.exists (.and (.mem (by fun_prop) (.comp₁ (by fun_prop) hf))
      (by fun_prop)))))

@[grind =]
theorem mem_sigma {f hf p} : p ∈ sigma a f hf ↔ ∃ x ∈ a, ∃ y ∈ f x, p = kpair x y := by
  grind [sigma, kpair]

@[simp]
theorem kpair_mem_sigma_iff {f hf} : kpair x y ∈ sigma a f hf ↔ x ∈ a ∧ y ∈ f x := by
  simp [mem_sigma, *]

theorem kpair_mem_sigma {f hf} (hx : x ∈ a) (hy : y ∈ f x) : kpair x y ∈ sigma a f hf := by
  simp [kpair_mem_sigma_iff, *]

@[simp, grind =]
theorem nonempty_sigma {f hf} : Nonempty (sigma a f hf) ↔ ∃ x ∈ a, Nonempty (f x) := by
  simp [Nonempty, mem_sigma]

theorem sigma_eq_prod : sigma a (fun _ => b) = prod a b := by
  grind

@[fun_prop]
nonrec theorem _root_.Set.DefinableFun.sigma [Finite α] {f : (α → M) → M} {g : (α → M) → M → M}
    (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set fun v : Option α → M => g (v ∘ some) (v none))
    {hg' : ∀ v, Set.univ.DefinableFun set fun w : Unit → M => g v (w ())} :
    A.DefinableFun set fun v => sigma (f v) (g v) (hg' v) :=
  .of_pred (by
    simp only [ext_iff, mem_sigma]
    refine .forall (.iff (.exists (.and (by fun_prop) (.exists (.and (.mem (by fun_prop) ?_)
      (by fun_prop))))) (by fun_prop))
    apply hg.comp (g := fun v => Option.elim' (v (some none)) (v ∘ some ∘ some ∘ some ∘ some))
    intro x
    cases x <;> simp only [Option.elim'_some, Option.elim'_none] <;> fun_prop)

abbrev Sigma (a : M) (f : M → M) (hf := by fun_prop) := ↥(sigma a f hf)

namespace Sigma

variable {f : M → M} {hf : Set.univ.DefinableFun set fun v : Unit → M => f (v ())}

def fst (p : Sigma a f hf) : ↥a :=
  ⟨Classical.choose (mem_sigma.1 p.2), (Classical.choose_spec (mem_sigma.1 p.2)).1⟩

def snd (p : Sigma a f hf) : ↥(f p.fst) :=
  ⟨Classical.choose (Classical.choose_spec (mem_sigma.1 p.2)).2,
    (Classical.choose_spec (Classical.choose_spec (mem_sigma.1 p.2)).2).1⟩

def mk (x : ↥a) (y : ↥(f x)) : Sigma a f hf :=
  ⟨kpair x.1 y.1, kpair_mem_sigma x.2 y.2⟩

variable {x x₁ x₂ : ↥a} {y : ↥(f x)} {y₁ : ↥(f x₁)} {y₂ : ↥(f x₂)} {p : Sigma a f hf}

@[simp] theorem coe_mk : (mk x y : Sigma a f hf).1 = kpair x.1 y.1 := rfl

@[simp, grind =]
theorem mk_inj : (mk x₁ y₁ : Sigma a f hf) = mk x₂ y₂ ↔ x₁ = x₂ ∧ y₁ ≍ y₂ := by
  grind [coe_mk]

@[simp, grind =]
theorem mk_fst_snd (p : Sigma a f hf) : mk p.fst p.snd = p := by
  ext1
  exact (Classical.choose_spec (Classical.choose_spec (mem_sigma.1 p.2)).2).2.symm

@[simp, grind =]
theorem fst_mk : (mk x y : Sigma a f hf).fst = x :=
  (mk_inj.1 (mk_fst_snd _)).1

@[grind =]
theorem snd_mk : (mk x y : Sigma a f hf).snd ≍ y :=
  (mk_inj.1 (mk_fst_snd _)).2

@[ext, grind ext]
theorem ext {p q : Sigma a f hf} : p.fst = q.fst → p.snd ≍ q.snd → p = q := by
  rw [← mk_fst_snd p, ← mk_fst_snd q]
  grind

@[simp, grind =]
lemma fst_kpair {x y} {h : kpair x y ∈ sigma a f hf} :
    fst ⟨kpair x y, h⟩ = ⟨x, (kpair_mem_sigma_iff.1 h).1⟩ := by
  rw [kpair_mem_sigma_iff] at h
  rw! [← coe_mk (x := ⟨x, h.1⟩) (y := ⟨y, h.2⟩), Subtype.eta, fst_mk]
  rfl

@[simp, grind =]
lemma coe_snd_kpair {x y} {h : kpair x y ∈ sigma a f hf} :
    snd ⟨kpair x y, h⟩ = ⟨y, by rw [fst_kpair]; exact (kpair_mem_sigma_iff.1 h).2⟩ := by
  rw [kpair_mem_sigma_iff] at h
  rw! [← coe_mk (x := ⟨x, h.1⟩) (y := ⟨y, h.2⟩), Subtype.eta]
  grind

@[fun_prop]
theorem definableFun_fst : DefinableFun (fst : Sigma a f hf → ↥a) := by
  simp only [DefinableFun]
  convert_to Set.univ.DefinablePred set fun v : Fin 2 → M =>
    v 1 ∈ a ∧ ∃ y ∈ f (v 1), kpair (v 1) y = v 0
  · grind
  · refine .and ?_ (.exists (.and (.mem ?_ (.comp₁ ?_ hf)) ?_)) <;> fun_prop

example : Sigma a f hf ≃ (x : ↥a) × ↥(f x) where
  toFun p := ⟨p.fst, p.snd⟩
  invFun p := mk p.1 p.2
  left_inv _ := by simp
  right_inv := by intro ⟨_, _⟩; simp [snd_mk]

end Sigma

abbrev Sets (a : M) := ↥(𝒫 a)

namespace Sets

variable {x y : ↥a} {s t : Sets a} {p : ↥a → Prop} {hp : DefinablePred p}

instance : Membership ↥a (Sets a) where
  mem s x := x.1 ∈ s.1

theorem coe_mem_coe : x.1 ∈ s.1 ↔ x ∈ s := Iff.rfl

theorem mem_coe {x : M} : x ∈ s.1 ↔ ∃ (h : x ∈ a), ⟨x, h⟩ ∈ s := by
  constructor
  · intro hx
    exists (mem_powerset.1 s.2) hx
  · intro ⟨hx, h⟩
    rwa [← Subtype.coe_mk x hx, coe_mem_coe]

@[ext, grind ext]
theorem ext : (∀ x, x ∈ s ↔ x ∈ t) → s = t := by
  intro h
  ext
  grind [mem_coe]

instance : HasSubset (Sets a) where
  Subset s t := ∀ ⦃x⦄, x ∈ s → x ∈ t

@[grind =] theorem subset_def : s ⊆ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t := Iff.rfl

theorem coe_subset_coe : s.1 ⊆ t.1 ↔ s ⊆ t := by grind [mem_coe]

instance : Std.Refl (· ⊆ · : Sets a → Sets a → Prop) where
  refl := by grind

-- grind introduces extra variables
instance : Std.Antisymm (· ⊆ · : Sets a → Sets a → Prop) where
  antisymm _ _ h₁ h₂ := by simp only [subset_def] at h₁ h₂; ext; exact ⟨@h₁ _, @h₂ _⟩

instance : IsTrans _ (· ⊆ · : Sets a → Sets a → Prop) where
  trans := by grind

@[fun_prop]
theorem definablePred_mem {f : ↥a → ↥b} {g : ↥a → Sets b} (hf : DefinableFun f)
    (hg : DefinableFun g) : DefinablePred fun x => f x ∈ g x := by
  simp only [DefinableFun, DefinablePred] at *
  convert_to Set.univ.DefinablePred set fun v : Unit → M =>
    ∃ y z, (∃ (h : v () ∈ a), (f ⟨v (), h⟩).1 = y) ∧ (∃ (h : v () ∈ a), (g ⟨v (), h⟩).1 = z) ∧ y ∈ z
  · grind [coe_mem_coe]
  · refine .exists (.exists (.and ?_ (.and ?_ (by fun_prop))))
    · convert hf.comp (f := fun v => ![v (some (some ())), v (some none)]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop
    · convert hg.comp (f := fun v => ![v (some (some ())), v none]) ?_
      intro i
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;> fun_prop

@[fun_prop]
theorem definablePred_subset {f : ↥a → Sets b} {g : ↥a → Sets b} (hf : DefinableFun f)
    (hg : DefinableFun g) : DefinablePred fun x => f x ⊆ g x := by
  simp_rw [subset_def]
  fun_prop

@[grind]
def Nonempty (s : Sets a) :=
  ∃ x, x ∈ s

theorem nonempty_coe_iff : set.Nonempty s.1 ↔ s.Nonempty := by
  grind [mem_coe]

@[fun_prop]
theorem definablePred_nonempty {f : ↥a → Sets b} (hf : DefinableFun f) :
    DefinablePred fun x => Nonempty (f x) := by
  simp_rw [Nonempty]
  fun_prop

def setOf (p : ↥a → Prop) (hp : DefinablePred p := by fun_prop) : Sets a :=
  ⟨sep a (fun x => ∃ (h : x ∈ a), p ⟨x, h⟩) hp, by grind⟩

@[simp, grind =]
theorem mem_setOf : x ∈ setOf p hp ↔ p x := by
  simp [setOf, ← coe_mem_coe, x.2]

@[fun_prop]
theorem definableFun_setOf {p : ↥a → ↥b → Prop}
    (hp : DefinablePred fun x : Prod a b => p x.fst x.snd) :
    DefinableFun fun x => setOf (fun y => p x y) (by
      simpa using hp.comp (f := fun y : ↥b => Prod.mk x y) (by fun_prop)) := by
  refine .of_pred ?_
  simp only [Sets.ext_iff, mem_setOf]
  refine .forall (.iff ?_ (by fun_prop))
  convert hp.comp (f := fun x : Prod (prod a (𝒫 b)) b =>
    Prod.mk (Prod.fst (Prod.fst x)) (Prod.snd x)) (by fun_prop) using 2
  simp

instance : EmptyCollection (Sets a) where
  emptyCollection := setOf fun _ => False
  
@[simp, grind .]
theorem not_mem_empty : x ∉ (∅ : Sets a) := by simp [EmptyCollection.emptyCollection]

protected def univ : Sets a := setOf fun _ => True

@[simp, grind .] theorem mem_univ : x ∈ Sets.univ := by simp [Sets.univ]

instance : Singleton ↥a (Sets a) where
  singleton x := setOf fun y => y = x

@[simp, grind .] theorem mem_singleton : x ∈ ({y} : Sets a) ↔ x = y := by simp [Singleton.singleton]

instance : Insert ↥a (Sets a) where
  insert x s := setOf fun y => y = x ∨ y ∈ s

@[simp, grind .] theorem mem_insert : x ∈ insert y s ↔ x = y ∨ x ∈ s := by simp [Insert.insert]

instance : Union (Sets a) where
  union s t := setOf fun x => x ∈ s ∨ x ∈ t

@[simp, grind =] theorem mem_union : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by simp [Union.union]

@[fun_prop]
theorem definableFun_union {f g : ↥a → Sets b} (hf : DefinableFun f) (hg : DefinableFun g) :
    DefinableFun fun x => f x ∪ g x := by
  fun_prop [Union.union]

instance : Inter (Sets a) where
  inter s t := setOf fun x => x ∈ s ∧ x ∈ t

@[simp, grind =] theorem mem_inter : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by simp [Inter.inter]

@[fun_prop]
theorem definableFun_inter {f g : ↥a → Sets b} (hf : DefinableFun f) (hg : DefinableFun g) :
    DefinableFun fun x => f x ∩ g x := by
  fun_prop [Inter.inter]

instance : Compl (Sets a) where
  compl s := setOf fun x => ¬ x ∈ s

@[simp, grind =] theorem mem_compl : x ∈ sᶜ ↔ x ∉ s := by simp [Compl.compl]
@[simp] theorem compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s := by simp only [subset_def, mem_compl]; grind

@[fun_prop]
theorem definableFun_compl : DefinableFun fun s : Sets a => sᶜ := by
  fun_prop [Compl.compl]

instance : SDiff (Sets a) where
  sdiff s t := setOf fun x => x ∈ s ∧ x ∉ t

@[simp, grind =] theorem mem_sdiff : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := by simp [SDiff.sdiff]

@[fun_prop]
theorem definableFun_sdiff {f g : ↥a → Sets b} (hf : DefinableFun f) (hg : DefinableFun g) :
    DefinableFun fun x => f x \ g x := by
  fun_prop [SDiff.sdiff]

protected def sUnion (S : Sets (𝒫 a)) : Sets a :=
  setOf fun x => ∃ s ∈ S, x ∈ s

scoped prefix:110 "⋃₀ " => Sets.sUnion

@[simp, grind =]
theorem mem_sUnion {S : Sets (𝒫 a)} : x ∈ ⋃₀ S ↔ ∃ s ∈ S, x ∈ s := by
  simp [Sets.sUnion]

@[simp] theorem sUnion_subset_iff {S : Sets (𝒫 a)} : ⋃₀ S ⊆ t ↔ ∀ s ∈ S, s ⊆ t := by grind

@[fun_prop]
theorem definableFun_sUnion : DefinableFun fun S : Sets (𝒫 a) => ⋃₀ S := by
  simp only [Sets.sUnion]
  fun_prop

protected def sInter (S : Sets (𝒫 a)) : Sets a :=
  setOf fun x => ∀ s ∈ S, x ∈ s

scoped prefix:110 "⋂₀ " => Sets.sInter

@[simp, grind =]
theorem mem_sInter {S : Sets (𝒫 a)} : x ∈ ⋂₀ S ↔ ∀ s ∈ S, x ∈ s := by
  simp [Sets.sInter]

@[simp] theorem subset_sInter_iff {S : Sets (𝒫 a)} : t ⊆ ⋂₀ S ↔ ∀ s ∈ S, t ⊆ s := by grind

@[fun_prop]
theorem definableFun_sInter : DefinableFun fun S : Sets (𝒫 a) => ⋂₀ S := by
  simp only [Sets.sInter]
  fun_prop

end Sets

@[grind]
def IsTotal (f a : M) :=
  ∀ x ∈ a, ∃ y, kpair x y ∈ f

@[fun_prop]
theorem _root_.Set.DefinablePred.isTotal [Finite α] {f g : (α → M) → M} (hf : A.DefinableFun set f)
    (hg : A.DefinableFun set g) : A.DefinablePred set fun v => IsTotal (f v) (g v) := by
  simp only [IsTotal]
  fun_prop

@[simp]
theorem realize_isTotal {t t₁ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isTotal t t₁).Realize v w ↔
      IsTotal (t.realize (Sum.elim v w)) (t₁.realize (Sum.elim v w)) := by
  simp [isTotal, IsTotal, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0),
    Fin.snoc_comp_castAdd (m := 1), Fin.snoc_comp_castAdd (m := 2), Fin.snoc_castAdd (m := 0),
    Fin.snoc_castAdd (m := 1)]

@[grind]
def IsUnique (f : M) :=
  ∀ x y₁ y₂, kpair x y₁ ∈ f → kpair x y₂ ∈ f → y₁ = y₂

@[fun_prop]
theorem _root_.Set.DefinablePred.isUnique [Finite α] {f : (α → M) → M} (hf : A.DefinableFun set f) :
    A.DefinablePred set fun v => IsUnique (f v) := by
  simp only [IsUnique]
  fun_prop

@[simp]
theorem realize_isUnique {t : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isUnique t).Realize v w ↔ IsUnique (t.realize (Sum.elim v w)) := by
  simp [isUnique, IsUnique, Sum.elim_comp_map, Fin.snoc_comp_castAdd (m := 0),
    Fin.snoc_comp_castAdd (m := 1), Fin.snoc_comp_castAdd (m := 2), Fin.snoc_comp_castAdd (m := 3),
    Fin.snoc_castAdd (m := 0), Fin.snoc_castAdd (m := 1), Fin.snoc_castAdd (m := 2)]

@[mk_iff, grind]
structure IsFunction (f a b : M) : Prop where
  isRel : f ⊆ prod a b
  isTotal : IsTotal f a
  isUnique : IsUnique f

theorem IsFunction.isTotal' {f} (hf : IsFunction f a b) : ∀ x ∈ a, ∃ y ∈ b, kpair x y ∈ f := by
  intro x hx
  rcases hf.isTotal x hx with ⟨y, hy⟩
  grind [hf.isRel hy]

theorem IsFunction.isTotalUnique {f} (hf : IsFunction f a b) :
    ∀ x ∈ a, ∃! y ∈ b, kpair x y ∈ f := by
  intro x hx
  rcases hf.isTotal' x hx with ⟨y, hy, h⟩
  exists y
  grind [hf.isUnique]

@[fun_prop]
theorem _root_.Set.DefinablePred.IsFunction [Finite α] {f g h : (α → M) → M}
    (hf : A.DefinableFun set f) (hg : A.DefinableFun set g) (hh : A.DefinableFun set h) :
    A.DefinablePred set fun v => IsFunction (f v) (g v) (h v) := by
  simp only [isFunction_iff]
  fun_prop

@[simp]
theorem realize_isFunction {t t₁ t₂ : set.Term (α ⊕ Fin n)} {v : α → M} {w : Fin n → M} :
    (isFunction t t₁ t₂).Realize v w ↔
      IsFunction (t.realize (Sum.elim v w)) (t₁.realize (Sum.elim v w))
        (t₂.realize (Sum.elim v w)) := by
  simp [isFunction]
  grind

def func (a b : M) :=
  sep (𝒫 (prod a b)) fun f => IsTotal f a ∧ IsUnique f

theorem mem_func {f} : f ∈ func a b ↔ IsFunction f a b := by
  simp [func, isFunction_iff]

abbrev Func (a b : M) := ↥(func a b)

namespace Func

variable {f g : Func a b} {x : ↥a} {y : ↥b}

def graph (f : Func a b) : Sets (prod a b) :=
  ⟨f.1, mem_powerset.2 (mem_func.1 f.2).1⟩

instance : FunLike (Func a b) ↥a ↥b where
  coe f x := ⟨Classical.choose ((mem_func.1 f.2).isTotal' _ x.2),
    (Classical.choose_spec ((mem_func.1 f.2).isTotal' _ x.2)).1⟩
  coe_injective' f g h := by
    simp only [funext_iff, Subtype.mk_eq_mk] at h
    ext p
    wlog h' : p ∈ f.1 generalizing p f g
    · simp only [h', false_iff]
      contrapose h'
      rwa [← this g f (fun a => (h a).symm) _ h']
    simp only [h', true_iff]
    rcases mem_prod.1 ((mem_func.1 f.2).1 h') with ⟨x, hx, y, hy, rfl⟩
    convert (Classical.choose_spec ((mem_func.1 g.2).isTotal' _ hx)).2
    rw [← h ⟨x, hx⟩]
    exact (mem_func.1 f.2).isUnique _ _ _ h'
      (Classical.choose_spec ((mem_func.1 f.2).isTotal' _ hx)).2

@[ext, grind ext]
theorem ext : (∀ x, f x = g x) → f = g := DFunLike.ext f g

@[simp, grind =]
theorem mem_graph {p : Prod a b} : p ∈ f.graph ↔ f p.fst = p.snd := by
  conv_lhs => rw [← Sets.coe_mem_coe, ← Prod.mk_fst_snd p, Prod.coe_mk]
  constructor
  · intro h
    ext1
    exact (mem_func.1 f.2).isUnique _ _ _
      (Classical.choose_spec ((mem_func.1 f.2).isTotal' _ p.fst.2)).2 h
  · intro h
    rw [← h]
    exact (Classical.choose_spec ((mem_func.1 f.2).isTotal' _ p.fst.2)).2

theorem mem_graph' : Prod.mk x y ∈ f.graph ↔ f x = y := by grind

@[simp, grind =] theorem coe_graph : f.graph.1 = f.1 := rfl

@[simp, grind =] theorem graph_inj : f.graph = g.graph ↔ f = g := by grind

@[fun_prop]
theorem definableFun_graph : DefinableFun (graph : Func a b → Sets (prod a b)) := by
  simp only [DefinableFun]
  convert_to Set.univ.DefinablePred set fun v : Fin 2 → M => v 0 ∈ func a b ∧ v 0 = v 1
  · grind
  · fun_prop

@[fun_prop]
theorem definableFun_apply {f : ↥a → Func b c} {g : ↥a → ↥b} (hf : DefinableFun f)
    (hg : DefinableFun g) : DefinableFun fun x => f x (g x) := by
  refine .of_pred ?_
  simp_rw [← mem_graph']
  fun_prop

def mk (f : ↥a → ↥b) (hf : DefinableFun f := by fun_prop) : Func a b :=
  let s := Sets.setOf (fun p : Prod a b => f p.fst = p.snd) (by fun_prop)
  ⟨s.1, mem_func.2 ⟨by grind, fun x hx => ⟨f ⟨x, hx⟩, by
    nth_rw 1 [← Subtype.coe_mk x hx, ← Prod.coe_mk, Sets.coe_mem_coe]
    grind⟩, fun x y₁ y₂ h₁ h₂ => by
      simp only [Sets.setOf, mem_sep, kpair_mem_prod_iff, and_exists_self, s] at h₁ h₂
      rcases h₁ with ⟨⟨hx, hy₁⟩, h₁⟩
      rcases h₂ with ⟨⟨_, hy₂⟩, h₂⟩
      rw! [← Prod.coe_mk (x := ⟨x, hx⟩) (y := ⟨y₁, hy₁⟩), Subtype.eta, Prod.fst_mk, Prod.snd_mk]
        at h₁
      rw! [← Prod.coe_mk (x := ⟨x, hx⟩) (y := ⟨y₂, hy₂⟩), Subtype.eta, Prod.fst_mk, Prod.snd_mk]
        at h₂
      rw [← Subtype.mk_eq_mk (h := hy₁) (h' := hy₂), ← h₁, ← h₂]⟩⟩

@[simp]
theorem graph_mk {f : ↥a → ↥b} {hf} :
    (mk f hf).graph = Sets.setOf (fun p : Prod a b => f p.fst = p.snd) (by fun_prop) := rfl

@[simp, grind =]
theorem mk_apply {f : ↥a → ↥b} {hf} : mk f hf x = f x := by
  symm
  simpa using mem_graph (f := mk f hf) (p := Prod.mk x (mk f hf x))

@[fun_prop]
theorem definableFun_mk {f : ↥a → ↥b → ↥c} (hf : DefinableFun fun x : Prod a b => f x.fst x.snd)
    {hf' : ∀ x, DefinableFun (f x)} : DefinableFun fun x => mk (f x) (hf' x) := by
  refine .of_pred ?_
  simp only [Func.ext_iff, mk_apply]
  refine .forall (.eq ?_ (by fun_prop))
  convert DefinableFun.comp
    (f := fun x : Prod (prod a (func b c)) b => Prod.mk (Prod.fst x.fst) x.snd) (by fun_prop) hf
    using 2
  simp

def id : Func a a :=
  mk fun x => x

@[simp, grind =] theorem id_apply : id x = x := by simp [id]

def comp (g : Func b c) (f : Func a b) : Func a c :=
  mk fun x => g (f x)

@[simp, grind =] theorem comp_apply {g : Func b c} : g.comp f x = g (f x) := by simp [comp]

/-- Principle of unique choice is a theorem of ZF. -/
theorem unique_choice {p : ↥a → ↥b → Prop} (hp : DefinablePred fun x : Prod a b => p x.fst x.snd)
    (h : ∀ x, ∃! y, p x y) : ∃ (f : Func a b), ∀ x, p x (f x) := by
  choose f hf hf' using h
  simp only at hf hf'
  suffices DefinableFun f by exact ⟨Func.mk f, by grind⟩
  refine .of_pred ?_
  convert hp using 2
  grind

@[fun_prop]
theorem definablePred_injective : DefinablePred fun f : Func a b => Function.Injective f := by
  fun_prop [Function.Injective]

@[fun_prop]
theorem definablePred_surjective : DefinablePred fun f : Func a b => Function.Surjective f := by
  fun_prop [Function.Surjective]

@[fun_prop]
theorem definablePred_bijective : DefinablePred fun f : Func a b => Function.Bijective f := by
  fun_prop [Function.Bijective]

theorem exists_left_inv_of_injective (ha : Nonempty a) (hf : Function.Injective f) :
    ∃ (g : Func b a), Function.LeftInverse g f := by
  rcases ha.coe_sort with ⟨x₀⟩
  have : ∀ y, ∃! x, f x = y ∨ (x = x₀ ∧ ¬ ∃ x, f x = y) := by
    intro y
    by_cases h : ∃ x, f x = y
    · rcases h with ⟨x, hx⟩
      exists x
      grind
    · exists x₀
      grind
  apply unique_choice (by fun_prop) at this
  rcases this with ⟨g, hg⟩
  exists g
  grind

theorem exists_inv_of_bijective (hf : Function.Bijective f) :
    ∃ (g : Func b a), Function.LeftInverse g f ∧ Function.RightInverse g f := by
  rcases unique_choice (by fun_prop) hf.existsUnique with ⟨g, hg⟩
  exists g
  grind [hf.injective]

/-- **Cantor's theorem**: there is no surjection from `a` to `𝒫 a`. -/
theorem cantor_surjective (f : Func a (𝒫 a)) : ¬ Function.Surjective f := by
  intro hf
  rcases hf (Sets.setOf fun x => x ∉ f x) with ⟨x, hx⟩
  simp only [Sets.ext_iff, Sets.mem_setOf] at hx
  grind

/-- **Cantor's theorem**: there is no injection from `𝒫 a` to `a`. -/
theorem cantor_injective (f : Func (𝒫 a) a) : ¬ Function.Injective f := by
  intro hf
  rcases exists_left_inv_of_injective (by simp) hf with ⟨g, hg⟩
  exact cantor_surjective g hg.surjective

end Func

namespace Sets

variable {f : Func a b} {x : ↥a} {y : ↥b}

def image (f : Func a b) (s : Sets a) : Sets b :=
  setOf fun y => ∃ x ∈ s, f x = y

scoped infixr:80 " '' " => image

@[simp, grind =] theorem mem_image {s : Sets a} : y ∈ f '' s ↔ ∃ x ∈ s, f x = y := by simp [image]

@[simp]
theorem nonempty_image_iff {s : Sets a} : (f '' s).Nonempty ↔ s.Nonempty := by
  simp [Nonempty, -Subtype.exists]

alias ⟨_, Nonempty.image⟩ := nonempty_image_iff

-- `fun_prop` does not use `definableFun_apply`, why?
@[fun_prop]
theorem definableFun_image {f : ↥a → Func b c} {g : ↥a → Sets b}
    (hf : DefinableFun f) (hg : DefinableFun g) : DefinableFun fun x => f x '' g x := by
  simp only [image]
  refine definableFun_setOf (.exists (.and ?_ (.eq (Func.definableFun_apply ?_ ?_) ?_)))
    <;> fun_prop

def preimage (f : Func a b) (s : Sets b) : Sets a :=
  setOf fun x => f x ∈ s

scoped infixr:80 " ⁻¹' " => preimage

@[simp, grind =] theorem mem_preimage {s : Sets b} : x ∈ f ⁻¹' s ↔ f x ∈ s := by simp [preimage]

@[fun_prop]
theorem definableFun_preimage {f : ↥a → Func b c} {g : ↥a → Sets c}
    (hf : DefinableFun f) (hg : DefinableFun g) : DefinableFun fun x => f x ⁻¹' g x := by
  simp only [preimage]
  refine definableFun_setOf ?_
  refine definablePred_mem (Func.definableFun_apply ?_ ?_) ?_ <;> fun_prop

@[simp] theorem image_subset_iff {s : Sets a} {t : Sets b} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by grind

theorem preimage_image_eq {s : Sets a} (hf : Function.Injective f) : f ⁻¹' f '' s = s := by grind

/-- **Tarski's fixed point theorem** on `𝒫 a`. -/
theorem exists_fixed_point_of_monotone {f : Func (𝒫 a) (𝒫 a)} (hf : ∀ s t, s ⊆ t → f s ⊆ f t) :
    ∃ s, f s = s := by
  let s := ⋂₀ (setOf fun s : Sets a => f s ⊆ s)
  exists s
  have hs : f s ⊆ s := by
    rw [subset_sInter_iff]
    intro t ht
    have hst : s ⊆ t := by grind
    grind
  apply hs.antisymm
  intro x hx
  simp only [s, mem_sInter, mem_setOf] at hx
  exact hx _ (hf _ _ hs)

end Sets

open Sets in
/-- **Schröder-Bernstein theorem**: if there are injection from `a` to `b` and injection from `b` to
`a`, then there is a bijection between `a` and `b`.

Tarski's fixed point theorem is used to avoid axiom of infinity. -/
theorem Func.exists_bijective_of_injective {f : Func a b} {g : Func b a}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ (h : Func a b), Function.Bijective h := by
  classical
  rcases eq_empty_or_nonempty b with rfl | hb
  · rcases eq_empty_or_nonempty a with rfl | ha
    · exists id
      grind [Function.Bijective, Function.Injective, Function.Surjective]
    · rcases ha.coe_sort with ⟨x⟩
      simpa using (f x).2
  let F : Func (𝒫 a) (𝒫 a) := mk fun s => (g '' (f '' s)ᶜ)ᶜ
  have hF : ∀ s t, s ⊆ t → F s ⊆ F t := by
    intro s t hst
    simpa [F, preimage_image_eq, hf, hg]
  rcases Sets.exists_fixed_point_of_monotone hF with ⟨s, hs⟩
  rcases exists_left_inv_of_injective hb hg with ⟨h, hh⟩
  exists mk fun x => if x ∈ s then f x else h x
  constructor
  · grind [Function.Injective]
  · intro y
    by_cases hy : y ∈ f '' s
    · rw [mem_image] at hy
      rcases hy with ⟨x, hx, rfl⟩
      exists x
      grind
    · exists g y
      grind

end

end FirstOrder.Language.set
