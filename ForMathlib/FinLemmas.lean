import Mathlib.Data.Fin.Tuple.Basic

@[simp]
theorem Fin.snoc_apply_zero' {α} {p : Fin 0 → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 0 = x := rfl

@[simp]
theorem Fin.snoc_apply_one {α n} {p : Fin (n + 2) → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 1 = p 1 := rfl

@[simp]
theorem Fin.snoc_apply_one' {α} {p : Fin 1 → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 1 = x := rfl

@[simp]
theorem Fin.snoc_apply_two {α n} {p : Fin (n + 3) → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 2 = p 2 := rfl

@[simp]
theorem Fin.snoc_apply_two' {α} {p : Fin 2 → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 2 = x := rfl

@[simp]
theorem Fin.snoc_apply_three {α n} {p : Fin (n + 4) → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 3 = p 3 := rfl

@[simp]
theorem Fin.snoc_apply_three' {α} {p : Fin 3 → α} {x : α} :
    Fin.snoc (α := fun _ => α) p x 3 = x := rfl
