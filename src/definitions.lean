import tactic 

namespace Algebra 

universe u

lemma pnat_wf : well_founded (preorder.to_has_lt ℕ+).1 := 
measure_wf coe

lemma Zp_well_order (A : set pnat) : A.nonempty →  
    ∃ m ∈ A, (∀ x ∈ A, m ≤ x) := 
begin 
  intro H,
  have := well_founded.has_min pnat_wf A H,
  rcases this with ⟨m, H1,H2⟩,
  use m, split,{exact H1},
  intros x H3, replace H2 := H2 x H3,
  exact not_lt.mp H2,
end 

lemma add_int_zero : ∀ a : ℤ, a + int.zero = a := 
by tidy 

lemma add_int_zero_unique : ∀ a b : ℤ, a + b = a → (0 ≤ b) → b = 0 := 
by tidy

section has_add
variables {G : Type} [has_add G]

def left_add : G → G → G := λ a b, a + b

def right_add : G → G → G := λ a b, b + a 

end has_add


@[ancestor has_add] class semigroup (G : Type u) extends has_add G :=
(assoc : ∀ a b c : G, a + b + c = a + (b + c))


namespace  semigroup
variables {G : Type u} [semigroup G] {a b c : G}



lemma associative   : ∀ a b c : G, a + b + c = a + (b + c) :=
semigroup.assoc

instance semigroup.is_associative : is_associative G (+) := ⟨semigroup.assoc⟩

end semigroup


class commutative_semigroup (G : Type u) extends semigroup G :=
(comm : ∀ a b : G, a + b = b + a)


section commutative_semigroup
variables {G : Type u} [commutative_semigroup G]

lemma add_comm : ∀ a b : G, a + b = b + a  :=
commutative_semigroup.comm

instance commutative_semigroup.is_commutative : is_commutative G (+) :=
⟨commutative_semigroup.comm⟩

end commutative_semigroup


class left_cancel_semigroup (G : Type u) extends semigroup G :=
(left_cancel : ∀ a b c : G, a + b = a + c → b = c)


section left_cancel_semigroup
variables {G : Type u} [left_cancel_semigroup G] {a b c : G}

lemma add_cancel_l : a + b = a + c → b = c :=
left_cancel_semigroup.left_cancel a b c

lemma left_cancel_iff : a + b = a + c ↔ b = c :=
⟨add_cancel_l, congr_arg _⟩

theorem add_right_injective (a : G) : function.injective ((+) a) :=
λ b c, add_cancel_l

@[simp]
theorem add_right_inj (a : G) {b c : G} : a + b = a + c ↔ b = c :=
⟨add_cancel_l, congr_arg _⟩

end left_cancel_semigroup


class right_cancel_semigroup (G : Type u) extends semigroup G :=
(right_cancel : ∀ a b c : G, a + b = c + b → a = c)


section right_cancel_semigroup
variables {G : Type u} [right_cancel_semigroup G] {a b c : G}

lemma add_cancel_r : a + b = c + b → a = c :=
right_cancel_semigroup.right_cancel a b c

lemma add_right_cancel_iff : b + a = c + a ↔ b = c :=
⟨add_cancel_r, congr_arg _⟩

theorem add_left_injective (a : G) : function.injective (λ x, x + a) :=
λ b c, add_cancel_r

@[simp]
theorem add_left_inj (a : G) {b c : G} : b + a = c + a ↔ b = c :=
⟨add_cancel_r, congr_arg _⟩

end right_cancel_semigroup

class monoid (M : Type u) extends semigroup M, has_zero M :=
(ident_l : ∀ a : M, 0 + a = a) 
(ident_r : ∀ a : M, a + 0 = a)

section monoid
variables {M : Type u} [monoid M]

@[simp]
lemma zero_add : ∀ a : M, 0 + a = a :=
monoid.ident_l

@[simp]
lemma add_zero : ∀ a : M, a + 0 = a :=
monoid.ident_r

instance monoid_left_id : is_left_id M (+) 0 :=
⟨ monoid.ident_l ⟩

instance monoid_right_id : is_right_id M (+) 0 :=
⟨ monoid.ident_r ⟩

lemma left_inv_eq_right_inv {a b c : M} (hba : b + a = 0) (hac : a + c = 0) : b = c :=
by rw [← monoid.ident_l c, ← hba, semigroup.associative,hac, add_zero]

end monoid

class commutative_monoid (M : Type u) extends monoid M := 
(comm : ∀ a b : M, a + b = b + a)

section commutative_monoid 
variables {M : Type u} [commutative_monoid M]


instance is_comm_semigroup : commutative_semigroup M := 
{ add := (+),
  assoc := semigroup.associative,
  comm := commutative_monoid.comm}

end commutative_monoid

class left_cancel_monoid (M : Type u) extends  monoid M  :=
(cancel_l : ∀ a b c : M, a + b = a + c → b = c)

class right_cancel_monoid (M : Type u) extends  monoid M  :=
(cancel_r : ∀ a b c : M, a + b = a + c → b = c)

class cancellative_monoid (M : Type u) extends monoid M:= 
(cancel_l : ∀ a b c : M, a + b = a + c → b = c)
(cancel_r : ∀ a b c : M, a + b = c + b → a = c)

class group (α : Type u) extends monoid α, has_neg α :=
(inv_l : ∀ a : α, -a + a = 0)

namespace group

variables {G : Type u} [group G] {a b c : G}

@[simp]
lemma inv_left : ∀ a : G, (-a) + a = 0 :=
group.inv_l

lemma inv_self_l (a : G) : (-a) + a = 0 := group.inv_l a

lemma associative {a b c : G} :  a + b + c = a + (b + c) := semigroup.associative a b c



lemma ident_l {a : G} : 0 + a = a := monoid.ident_l a
lemma ident_r {a : G} : a + 0 = a := monoid.ident_r a

@[simp]
lemma inv_cancel_left (a b : G) : (-a) + (a + b) = b :=
by {rw [← associative, inv_self_l, ident_l]}

@[simp]
lemma add_zero_imp_inv (h : a + b = 0) : (-a) = b :=
left_inv_eq_right_inv (inv_self_l a) h

@[simp]
lemma inv_idempotent (a : G) : - (-a) = a := 
add_zero_imp_inv (inv_l a)

@[simp] 
lemma inv_r (a : G) : a + (-a) = 0 := 
by { have H : -(- a) + (-a) = 0 := inv_l (-a), rwa inv_idempotent at H}

lemma inv_self_r (a : G) : a + (-a) = 0 := inv_r a

@[simp]
lemma inv_cancel_right (a b : G) : a + b + (-b) = a :=
by rw [associative, inv_r, add_zero]


def abelian (G : Type u) [group G] : Prop := ∀ a b : G, a + b = b + a

def pow (g : G) : ℕ → G
| 0 := 0 
| (n + 1) :=  g + pow n 

infix `↟` : 100 := group.pow

end group

instance group.to_cancel_monoid {G : Type u} [group G] : cancellative_monoid G := { 
  add := has_add.add,
  assoc := λ a b c, group.associative,
  zero := has_zero.zero,
  ident_l := λ a , group.ident_l ,
  ident_r := λ a, group.ident_r,
  cancel_l := λ a b c H, by 
  {rw [← group.inv_cancel_left a b,
       H,  ← group.associative,  group.inv_l, group.ident_l]},
  cancel_r := λ a b c H, by 
  {rw [← group.inv_cancel_right a b,
       H, group.associative,  group.inv_r, group.ident_r]},
}


end Algebra 