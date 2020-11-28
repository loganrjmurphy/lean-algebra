import tactic 

namespace groups  

variables (α : Type) 

example (a b c : α) [add_group α] : a + b = a + c → b = c := (add_right_inj a).mp

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

local notation ℤ`⁺` := pnat

lemma add_int_zero : ∀ a : ℤ, a + int.zero = a := 
by tidy 

lemma add_int_zero_unique : ∀ a b : ℤ, a + b = a → (0 ≤ b) → b = 0 := 
by tidy


class semigroup (α : Type) extends has_add α:= 
(assoc : ∀ a b c : α , a + b + c = a + (b + c))

class has_ident (α : Type*) := (id : α)

notation `e` := has_ident.id 

class monoid (M : Type) extends semigroup M, has_ident M :=
(ident_l: ∀ a : M, e + a = a) (ident_r : ∀ a : M, a + e = a)

class has_neg  (α : Type) := (neg : α → α)

notation -a := has_neg.neg a 

class group (α : Type*) extends monoid α, has_neg α :=
(inv_l : ∀ a : α, -a + a = e) (inv_r : ∀ a : α, a + (-a) = e)

variables {G  H : Type} [group G] [group H] {a b c : G}

namespace group



def identity (G : Type) [group G] : G := has_ident.id

def action (G : Type) [group G] : G → G → G := has_add.add

@[instance] def nonempty : nonempty G :=  ⟨identity G⟩


def ident_l : ∀ a : G, e + a = a := monoid.ident_l

def ident_r : ∀ a : G, a + e = a := monoid.ident_r
def assoc : ∀ a b c : G , a + b + c = a + (b + c) := semigroup.assoc


lemma id_unique : 
  ∀ e', (∀ a : G, a + e' = a ∧ e' + a = a) → e = e' := 
begin
  intros e' H, 
  rcases (H e) with ⟨H1,H2⟩,
  have := (group.ident_l e'), rw H1 at this,
  exact this
end 

lemma inv_unique : ∀ a b c : G, b = (-a) → c = (-a) → b = c := 
begin
   intros a b c H1 H2,
   have H3 := group.inv_r a,
   have H4 := group.inv_l a,
   have H5 := group.ident_r c,
   rw ← H1 at H3,
   rw ← H2 at H4,
   rwa [← H3, ← group.assoc, H4, group.ident_l] at H5,
end  

def inv_idempotent : ∀ a : G, - (- a) = a := 
begin 
  intro a,
  have H1 := group.inv_r (a),
  have H2 := group.ident_l (- -a),
  rw ← H1 at H2,
  rw [← H2, group.assoc,group.inv_r (- a), group.ident_r]
end 


lemma add_inv : ∀ a b : G, - (a + b) = (-b) + (-a) := 
begin 
  intros a b,
  let c := - (a + b),
  have H1 : (a + b) + c = e, from group.inv_r (a + b),
  have H2 : (-a) + (a + b) + c = (-a) + e, by {rw group.assoc, rw H1},
  rw [← group.assoc,group.inv_l,group.ident_l,group.ident_r] at H2,
  have H3 : (-b) + (b + c) = (-b) + (-a), by {rw H2,},
  rwa [← group.assoc, group.inv_l, group.ident_l] at H3,
end  

lemma inv_cancel_right (a b : G) : b + a + (-a) = b :=
by rw [group.assoc, group.inv_r, group.ident_r]

lemma cancel_right {a b c : G} :   b + a = c + a → b = c :=
λ H, by  
rw [← inv_cancel_right a b,  H,  
    group.assoc,  group.inv_r, group.ident_r] 


lemma inv_cancel_left (a b : G) :(-a) + a + b = b :=
by rw [group.inv_l, group.ident_l]

lemma cancel_left {a b c : G} : a + b = a + c → b = c :=
λ H, by  
rw [← inv_cancel_left a b,group.assoc, 
    H, ← group.assoc, group.inv_l, group.ident_l]


lemma inv_of_eq_ident_r  {a b : G} : a + b = e → b = (-a) := 
λ h, by {rw ← group.inv_r a at h, 
             apply group.cancel_left h,}

lemma inv_of_eq_ident_l {a b : G} : b + a = e → b = (-a) := 
λ  h, by {rw ← group.inv_l a at h, 
             apply group.cancel_right h,}

lemma ident_of_idempotent_l {a b : G}  : a + b = a → b = e := 
λ H, by 
{rw [← group.ident_r a,  group.assoc, group.ident_l] at H,
 apply group.cancel_left H}


lemma ident_of_idempotent_r {a b : G}  :  b + a = a → b = e := 
λ H, by 
{rw [← group.ident_l a,  ← group.assoc, group.ident_r] at H,
 apply group.cancel_right H}

end group 


def abelian : Prop := ∀ a b : G, a + b = b + a

def pow (x : G) : ℕ → G 
| 0 := e 
| (n + 1) := x + pow n 

infix `↟`  : 100 := pow 


/---Direct Products ---/

def direct_product_action (G H : Type) [group G] [group H] : G × H  → G × H → G × H := 
(λ x y, ⟨x.1 + y.1, x.2 + y.2⟩)

instance : has_add (G × H) := ⟨direct_product_action G H⟩

lemma direct_product_assoc : 
 ∀ (a b c : G × H),  (a + b) + c =  a + (b + c) := 
 begin 
   intros a b c,
   unfold has_add.add,
   rw direct_product_action,
   simp,split,
   apply group.assoc,
   apply group.assoc,
 end 

instance : has_ident (G × H) := 
  ⟨⟨group.identity G, group.identity H⟩⟩  

  
instance : has_neg (G × H) := 
  {neg := λ p, ⟨- p.1, - p.2⟩ }

lemma group_ident_left (g : G) : group.identity G + g = g := 
by {unfold group.identity, rw group.ident_l}


lemma group_ident_right (g : G) :  g + group.identity G  = g := 
by {unfold group.identity, rw group.ident_r}


@[instance] def direct_product : group (G × H) := 
{
  add := direct_product_action G H,
  assoc := direct_product_assoc,
  id := has_ident.id,
  ident_l := 
    begin 
      intro g, unfold has_add.add,
      rw direct_product_action,
      unfold has_ident.id,
      simp, 
      rw [group_ident_left g.fst,group_ident_left g.snd],
      cases g, refl,
    end ,
  ident_r := 
    begin 
      intro g, unfold has_add.add,
      rw direct_product_action,
      unfold has_ident.id,
      simp, 
      rw [group_ident_right g.fst,group_ident_right g.snd],
      cases g, refl,
    end  ,
  neg := has_neg.neg ,
  inv_l := 
    begin
      intro a, unfold has_neg.neg, unfold has_add.add,
      unfold direct_product_action, simp,
      rw group.inv_l, rw group.inv_l, refl,
    end ,
  inv_r := 
    begin 
      intro a, unfold has_neg.neg, unfold has_add.add,
      unfold direct_product_action, simp,
      rw group.inv_r, rw group.inv_r, refl,
    end 
}

/---- Subgroups ---/

structure submonoid (M : Type*) [monoid M] :=
(carrier : set M)
(ident : (e : M) ∈ carrier)
(closure {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)

structure subgroup (G : Type*) [group G] extends submonoid G :=
(inv {x} : x ∈ carrier → (-x) ∈ carrier)

instance : has_coe (subgroup G) (set G) := ⟨λ G, G.carrier⟩ 
instance : has_mem G (subgroup G) := ⟨λ m K, m ∈ (K : set G)⟩

lemma coe_coe (K : subgroup G) : ↥(K : set G) = K := rfl

variable (K : subgroup G)

namespace subgroup 

lemma ident : (e : G) ∈ K := K.ident

lemma closure {a b : G} : a ∈ K → b ∈ K → a + b ∈ K := 
  λ h1 h2, K.closure h1 h2

lemma inverse {a : G} : a ∈ K → (-a ∈ K) := λ h, K.inv h

theorem inv_mem_iff {x : G} : (-x) ∈ K ↔ x ∈ K :=
begin 
  split, 
  {intro H, replace H := subgroup.inverse K (-x) H, 
   rwa group.inv_idempotent at H},
  intro H, exact subgroup.inverse K x H
end 

lemma cancel_right_mem {x y : G} (h : x ∈ K) : y + x ∈ K ↔ y ∈ K :=
begin 
  split, 
  {intro hyx, have h' := subgroup.closure K hyx (K.inverse h),
   rwa [group.assoc, group.inv_r, group.ident_r] at h',},
  {intro hy, exact subgroup.closure K hy h,}
end 

lemma cancel_left_mem {x y : G} (h : x ∈ K) :  x + y ∈ K ↔ y ∈ K :=
begin 
  split, 
  {intro hyx, have h' := subgroup.closure K (K.inverse h) hyx,
   rwa [← group.assoc, group.inv_l, group.ident_l] at h',},
  {intro hy, exact subgroup.closure K h hy,}
end 





end subgroup 

-- Homomorphisms

structure group_hom (G H : Type) [group G] [group H] := 
(f : G → H)
(preserves : ∀ x y : G, f(x + y) = f x + f y)

def is_isomorphisim (φ : group_hom G H) : Prop := 
function.bijective φ.1

def isomorphic : Prop := 
  ∃ φ : group_hom G H, is_isomorphisim φ 

notation G ≃ H := isomorphic G H

def isomorphism : Type := 
  {φ : group_hom G H // is_isomorphisim φ}

def kernel (φ : group_hom G H) : set G := 
{g | φ.1 g = e}


@[instance] def kernel_group (φ : group_hom G H) : 
  group (kernel φ) := sorry 

end groups 